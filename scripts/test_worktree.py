"""Temporary-repository tests for worktree branch selection, shared pin-keyed package caches,
primary-checkout protection, and cache bootstrap."""

from __future__ import annotations

import json
import os
import pathlib
import shutil
import stat
import subprocess
import tempfile
import unittest

REPO = pathlib.Path(__file__).resolve().parent.parent
SCRIPT = REPO / "scripts/worktree.sh"

GIT_ENV = {
    **os.environ,
    "GIT_AUTHOR_NAME": "Test",
    "GIT_AUTHOR_EMAIL": "test@example.com",
    "GIT_COMMITTER_NAME": "Test",
    "GIT_COMMITTER_EMAIL": "test@example.com",
    "GIT_CONFIG_GLOBAL": os.devnull,
    "GIT_CONFIG_NOSYSTEM": "1",
}


def git(cwd: pathlib.Path, *args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(cwd), *args],
        capture_output=True,
        text=True,
        check=True,
        env=GIT_ENV,
    ).stdout.strip()


@unittest.skipUnless(shutil.which("git"), "git is required")
class WorktreeCreateTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.tmp = pathlib.Path(tmp.name)
        self.origin = self.tmp / "origin.git"
        subprocess.run(
            ["git", "init", "--quiet", "--bare", "-b", "main", str(self.origin)],
            check=True,
            env=GIT_ENV,
        )
        # A second clone plays the other worker, who pushes branches.
        self.other = self.clone("other")
        (self.other / "README").write_text("base\n", encoding="utf-8")
        git(self.other, "add", "README")
        git(self.other, "commit", "--quiet", "-m", "base")
        git(self.other, "push", "--quiet", "origin", "main")
        self.main_sha = git(self.other, "rev-parse", "HEAD")
        self.feature_sha = self.push_branch("feature/takeover")
        self.work = self.clone("work")
        (self.work / "scripts").mkdir()
        shutil.copy(SCRIPT, self.work / "scripts/worktree.sh")

    def clone(self, name: str) -> pathlib.Path:
        path = self.tmp / name
        subprocess.run(
            ["git", "clone", "--quiet", str(self.origin), str(path)],
            check=True,
            env=GIT_ENV,
            capture_output=True,
        )
        return path

    def push_branch(self, branch: str) -> str:
        git(self.other, "switch", "--quiet", "-c", branch, self.main_sha)
        (self.other / "work.txt").write_text(f"{branch}\n", encoding="utf-8")
        git(self.other, "add", "work.txt")
        git(self.other, "commit", "--quiet", "-m", f"work on {branch}")
        git(self.other, "push", "--quiet", "origin", branch)
        sha = git(self.other, "rev-parse", "HEAD")
        git(self.other, "switch", "--quiet", "main")
        return sha

    def create(self, *args: str, **extra_env: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["bash", str(self.work / "scripts/worktree.sh"), "create", *args],
            cwd=self.work,
            capture_output=True,
            text=True,
            check=False,
            env={**GIT_ENV, **extra_env},
        )

    def upstream(self, wt: pathlib.Path) -> str | None:
        proc = subprocess.run(
            ["git", "-C", str(wt), "rev-parse", "--abbrev-ref", "@{upstream}"],
            capture_output=True,
            text=True,
            check=False,
            env=GIT_ENV,
        )
        return proc.stdout.strip() if proc.returncode == 0 else None

    def test_remote_only_branch_tracks_origin(self) -> None:
        proc = self.create("feature/takeover", "takeover")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        wt = self.work / ".worktrees/takeover"
        self.assertEqual(git(wt, "rev-parse", "HEAD"), self.feature_sha)
        self.assertEqual(self.upstream(wt), "origin/feature/takeover")

    def test_branch_pushed_after_clone_is_fetched_and_tracked(self) -> None:
        late_sha = self.push_branch("feature/late")
        proc = self.create("feature/late", "late")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        wt = self.work / ".worktrees/late"
        self.assertEqual(git(wt, "rev-parse", "HEAD"), late_sha)
        self.assertEqual(self.upstream(wt), "origin/feature/late")

    def test_remote_only_branch_with_base_ref_is_refused(self) -> None:
        proc = self.create("feature/takeover", "takeover", "origin/main")
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("exists on origin", proc.stderr)
        self.assertFalse((self.work / ".worktrees/takeover").exists())
        self.assertEqual(git(self.work, "branch", "--list", "feature/takeover"), "")

    def test_new_branch_starts_from_origin_main_without_upstream(self) -> None:
        proc = self.create("feature/fresh", "fresh")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        wt = self.work / ".worktrees/fresh"
        self.assertEqual(git(wt, "rev-parse", "HEAD"), self.main_sha)
        self.assertIsNone(self.upstream(wt))

    def test_conflicting_copy_flags_are_refused(self) -> None:
        proc = self.create("feature/fresh", "fresh", "--copy-cslib", "--copy-packages")
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("mutually exclusive", proc.stderr)
        self.assertFalse((self.work / ".worktrees/fresh").exists())

    def test_create_shares_readonly_pin_keyed_packages_and_never_updates_in_place(self) -> None:
        manifest_v1 = {"packages": [{"name": "cslib", "rev": "11111111aaaa22223333"}]}
        (self.other / "lake-manifest.json").write_text(json.dumps(manifest_v1), encoding="utf-8")
        git(self.other, "add", "lake-manifest.json")
        git(self.other, "commit", "--quiet", "-m", "pin v1")
        git(self.other, "push", "--quiet", "origin", "main")
        git(self.work, "fetch", "--quiet", "origin", "main")
        git(self.work, "reset", "--quiet", "--hard", "origin/main")

        paths = [pathlib.Path(".lake/packages/cslib/.lake") / part
                 for part in ("build/trace", "config/lakefile.olean")]
        for path in paths:
            cache = self.work / path
            cache.parent.mkdir(parents=True, exist_ok=True)
            cache.write_bytes(b"v1 cache\n")

        first = self.create("feature/one", "one")
        self.assertEqual(first.returncode, 0, first.stderr)
        wt_one = self.work / ".worktrees/one"
        pkg_link_one = wt_one / ".lake/packages"
        self.assertTrue(pkg_link_one.is_symlink())
        shared_v1 = (self.work / ".worktrees/.shared/packages-cslib-11111111").resolve()
        self.assertEqual(pkg_link_one.resolve(), shared_v1)

        for path in paths:
            root_file = self.work / path
            worker_file = wt_one / path
            self.assertFalse(os.path.samefile(root_file, worker_file))
            self.assertEqual(stat.S_IMODE(worker_file.stat().st_mode) & 0o222, 0)
            with self.assertRaises(PermissionError):
                worker_file.write_bytes(b"cannot mutate shared cache\n")
            self.assertEqual(root_file.read_bytes(), b"v1 cache\n")

        # Mutate the primary checkout's .lake/packages and verify a second worktree at the same pin
        # reuses the existing shared directory without updating it in place.
        for path in paths:
            (self.work / path).write_bytes(b"mutated root cache\n")
        second = self.create("feature/two", "two")
        self.assertEqual(second.returncode, 0, second.stderr)
        wt_two = self.work / ".worktrees/two"
        self.assertEqual((wt_two / ".lake/packages").resolve(), shared_v1)
        for path in paths:
            self.assertEqual((wt_two / path).read_bytes(), b"v1 cache\n")
            self.assertTrue(os.path.samefile(wt_one / path, wt_two / path))

        # Advance the cslib pin on a new branch and verify a new shared directory is created
        # while the v1 shared directory remains untouched.
        manifest_v2 = {"packages": [{"name": "cslib", "rev": "22222222bbbb33334444"}]}
        git(self.other, "switch", "--quiet", "-c", "feature/pin-v2", "origin/main")
        (self.other / "lake-manifest.json").write_text(json.dumps(manifest_v2), encoding="utf-8")
        git(self.other, "add", "lake-manifest.json")
        git(self.other, "commit", "--quiet", "-m", "pin v2")
        git(self.other, "push", "--quiet", "origin", "feature/pin-v2")
        git(self.other, "switch", "--quiet", "main")

        for path in paths:
            (self.work / path).write_bytes(b"v2 cache\n")
        third = self.create("feature/pin-v2", "pin-v2")
        self.assertEqual(third.returncode, 0, third.stderr)
        wt_three = self.work / ".worktrees/pin-v2"
        shared_v2 = (self.work / ".worktrees/.shared/packages-cslib-22222222").resolve()
        self.assertEqual((wt_three / ".lake/packages").resolve(), shared_v2)
        for path in paths:
            self.assertEqual((wt_three / path).read_bytes(), b"v2 cache\n")
            self.assertEqual((wt_one / path).read_bytes(), b"v1 cache\n")

    def test_create_runs_cache_bootstrap_in_fresh_worktree(self) -> None:
        log_file = self.tmp / "bootstrap.jsonl"
        cache_dir = self.other / "scripts/cache"
        cache_dir.mkdir(parents=True)
        shutil.copy(REPO / "scripts/cache/ensure.sh", cache_dir / "ensure.sh")
        (cache_dir / "ensure.sh").chmod(0o755)
        get_sh = cache_dir / "get.sh"
        get_sh.write_text(
            "#!/usr/bin/env python3\n"
            "import json, os\n"
            "with open(os.environ['TEST_BOOTSTRAP_LOG'], 'a') as f:\n"
            "    f.write(json.dumps({'cwd': os.getcwd()}) + '\\n')\n",
            encoding="utf-8",
        )
        get_sh.chmod(0o755)
        (self.other / "lean-toolchain").write_text("leanprover/lean4:v4.36.0-rc1\n")
        (self.other / "lake-manifest.json").write_text('{"packages": []}\n')
        (self.other / "lakefile.toml").write_text('name = "fixture"\n')
        git(self.other, "add", ".")
        git(self.other, "commit", "--quiet", "-m", "add cache scripts")
        git(self.other, "push", "--quiet", "origin", "main")
        git(self.work, "fetch", "--quiet", "origin", "main")
        git(self.work, "reset", "--quiet", "--hard", "origin/main")
        shutil.copy(SCRIPT, self.work / "scripts/worktree.sh")

        proc = self.create("feature/bootstrapped", "bootstrapped", TEST_BOOTSTRAP_LOG=str(log_file))
        self.assertEqual(proc.returncode, 0, proc.stderr)
        wt = self.work / ".worktrees/bootstrapped"
        self.assertTrue((wt / ".lake/cache-bootstrap/attempt.json").is_file())
        events = [json.loads(line) for line in log_file.read_text().splitlines()]
        self.assertEqual(len(events), 1)
        self.assertEqual(pathlib.Path(events[0]["cwd"]).resolve(), wt.resolve())

        # Opt-out skips automatic cache bootstrap on worktree creation.
        proc_skip = self.create(
            "feature/optout",
            "optout",
            TEST_BOOTSTRAP_LOG=str(log_file),
            COMPLEXITYLIB_CACHE_AUTO="0",
        )
        self.assertEqual(proc_skip.returncode, 0, proc_skip.stderr)
        wt_skip = self.work / ".worktrees/optout"
        self.assertFalse((wt_skip / ".lake/cache-bootstrap/attempt.json").exists())
        self.assertEqual(len(log_file.read_text().splitlines()), 1)

    def test_mismatched_root_cslib_git_revision_is_not_copied_into_new_pin(self) -> None:
        cslib_repo = self.work / ".lake/packages/cslib"
        cslib_repo.mkdir(parents=True)
        git(cslib_repo, "init", "--quiet", "-b", "main")
        (cslib_repo / "Cslib.lean").write_text("-- old cslib\n", encoding="utf-8")
        git(cslib_repo, "add", "Cslib.lean")
        git(cslib_repo, "commit", "--quiet", "-m", "old cslib")
        old_rev = git(cslib_repo, "rev-parse", "HEAD")
        new_rev = "f" * 40 if not old_rev.startswith("ffffffff") else "e" * 40

        (self.other / "lake-manifest.json").write_text(
            json.dumps({"packages": [{"name": "cslib", "rev": new_rev}]}),
            encoding="utf-8",
        )
        git(self.other, "add", "lake-manifest.json")
        git(self.other, "commit", "--quiet", "-m", "new cslib pin")
        git(self.other, "push", "--quiet", "origin", "main")
        git(self.work, "fetch", "--quiet", "origin", "main")
        git(self.work, "reset", "--quiet", "--hard", "origin/main")

        proc = self.create("feature/mismatch", "mismatch")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn("does not match manifest pin", proc.stderr)
        wt = self.work / ".worktrees/mismatch"
        self.assertFalse((wt / ".lake/packages").exists())
        self.assertFalse(
            (self.work / f".worktrees/.shared/packages-cslib-{new_rev[:8]}").exists()
        )


@unittest.skipUnless(shutil.which("git"), "git is required")
class WorktreeSeedTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.tmp = pathlib.Path(tmp.name)
        self.root = self.tmp / "root"
        self.root.mkdir()
        git(self.root, "init", "--quiet")
        (self.root / "scripts").mkdir()
        shutil.copy(SCRIPT, self.root / "scripts/worktree.sh")
        self.pkg_cache_paths = []
        for package in ("cslib", "mathlib"):
            source = self.root / ".lake/packages" / package / "Source.lean"
            source.parent.mkdir(parents=True)
            source.write_text("immutable source\n", encoding="utf-8")
            source.with_name("SourceLink.lean").symlink_to("Source.lean")
            self.pkg_cache_paths += [pathlib.Path("packages") / package / ".lake" / path
                                     for path in ("build/lib/Lean/Dependency.trace",
                                                  "config/lakefile.olean")]
        self.root_cache_paths = [pathlib.Path("build/lib/Lean/Root.trace"),
                                 pathlib.Path("config/lakefile.olean")]
        self.cache_paths = self.pkg_cache_paths + self.root_cache_paths
        for path in self.cache_paths:
            cache = self.root / ".lake" / path
            cache.parent.mkdir(parents=True, exist_ok=True)
            cache.write_text(f"root cache {path}\n", encoding="utf-8")
            cache.chmod(0o640)
            os.utime(cache, ns=(1_700_000_000_000_000_000, 1_700_000_000_000_000))

    def seed(self, target: pathlib.Path, *flags: str, **extra_env: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["bash", str(self.root / "scripts/worktree.sh"), "seed", str(target), *flags],
            capture_output=True, text=True, check=False, env={**GIT_ENV, **extra_env},
        )

    def assert_cache_isolated(self, target: pathlib.Path, flag: str | None) -> None:
        for path in self.cache_paths:
            original = self.root / ".lake" / path
            seeded = target / ".lake" / path
            before = original.read_bytes()
            self.assertEqual(seeded.read_bytes(), before)
            self.assertNotEqual(original.stat().st_ino, seeded.stat().st_ino, str(path))
            self.assertEqual(seeded.stat().st_mtime_ns, original.stat().st_mtime_ns)
            is_writable_copy = (
                path in self.root_cache_paths
                or flag == "--copy-packages"
                or (flag == "--copy-cslib" and path.parts[:2] == ("packages", "cslib"))
            )
            if is_writable_copy:
                self.assertEqual(stat.S_IMODE(seeded.stat().st_mode), 0o640)
                seeded.write_bytes(b"worker updated cache\n")
                self.assertEqual(original.read_bytes(), before, str(path))
            else:
                self.assertEqual(stat.S_IMODE(seeded.stat().st_mode) & 0o222, 0)
                with self.assertRaises(PermissionError):
                    seeded.write_bytes(b"cannot mutate shared package cache\n")
                self.assertEqual(original.read_bytes(), before, str(path))

    def test_all_copy_modes_isolate_from_primary_checkout_and_respect_sharing(self) -> None:
        shared_dir = (self.root / ".worktrees/.shared/packages-cslib-default").resolve()
        for flag in (None, "--copy-cslib", "--copy-packages"):
            with self.subTest(flag=flag):
                target = self.tmp / str(flag)
                result = self.seed(target, *([flag] if flag else []))
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assert_cache_isolated(target, flag)
                if flag is None:
                    self.assertTrue((target / ".lake/packages").is_symlink())
                    self.assertEqual((target / ".lake/packages").resolve(), shared_dir)
                else:
                    self.assertFalse((target / ".lake/packages").is_symlink())
                for package in ("cslib", "mathlib"):
                    source = self.root / ".lake/packages" / package / "Source.lean"
                    seeded = target / ".lake/packages" / package / "Source.lean"
                    # Never hard-link any worktree package file to the primary checkout.
                    self.assertNotEqual(source.stat().st_ino, seeded.stat().st_ino)
                    uses_shared = flag is None or (flag == "--copy-cslib" and package != "cslib")
                    shared_source = shared_dir / package / "Source.lean"
                    self.assertEqual(seeded.stat().st_ino == shared_source.stat().st_ino, uses_shared)
                    link = seeded.with_name("SourceLink.lean")
                    self.assertTrue(link.is_symlink())
                    self.assertEqual(os.readlink(link), "Source.lean")
                    self.assertEqual(link.read_bytes(), source.read_bytes())

    def test_cache_symlinks_are_copied_without_sharing_their_targets(self) -> None:
        # Cover an internal cache link, the entire cache directory, and a package directory.
        original = self.root / ".lake/build/lib/Lean/Root.trace"
        external = self.tmp / "external.trace"
        original.rename(external)
        original.symlink_to(external)
        package = self.root / ".lake/packages/cslib"
        external_cache = self.tmp / "external-cache"
        (package / ".lake").rename(external_cache)
        (package / ".lake").symlink_to(external_cache, target_is_directory=True)
        package = self.root / ".lake/packages/mathlib"
        external_package = self.tmp / "external-package"
        package.rename(external_package)
        package.symlink_to(external_package, target_is_directory=True)
        for flag in (None, "--copy-cslib", "--copy-packages"):
            with self.subTest(flag=flag):
                target = self.tmp / str(flag)
                result = self.seed(target, *([flag] if flag else []))
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assert_cache_isolated(target, flag)
                self.assertFalse((target / ".lake/build/lib/Lean/Root.trace").is_symlink())
                self.assertFalse((target / ".lake/packages/cslib/.lake").is_symlink())
                if flag == "--copy-cslib":
                    # In --copy-cslib mode, mathlib is a symlink to the shared copy, not to
                    # external_package.
                    self.assertTrue((target / ".lake/packages/mathlib").is_symlink())
                    self.assertNotEqual(
                        (target / ".lake/packages/mathlib").resolve(),
                        external_package.resolve(),
                    )
                else:
                    self.assertFalse((target / ".lake/packages/mathlib").is_symlink())

    def test_existing_cache_is_preserved_on_repeated_seed(self) -> None:
        target = self.tmp / "worker"
        self.assertEqual(self.seed(target).returncode, 0)
        cache = target / ".lake" / self.root_cache_paths[0]
        cache.write_text("worker state\n", encoding="utf-8")
        self.assertEqual(self.seed(target, "--copy-packages").returncode, 0)
        self.assertEqual(cache.read_text(), "worker state\n")

    def test_destination_cache_symlinks_are_refused_before_writing(self) -> None:
        for path in (".lake", ".lake/packages", ".lake/build", ".lake/config"):
            with self.subTest(path=path):
                target = self.tmp / path.replace("/", "-")
                external = self.tmp / (target.name + "-external")
                external.mkdir()
                link = target / path
                link.parent.mkdir(parents=True)
                link.symlink_to(external, target_is_directory=True)
                result = self.seed(target)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("symlink", result.stderr)
                self.assertEqual(list(external.iterdir()), [])

    def test_primary_checkout_and_symlinks_into_primary_checkout_are_refused(self) -> None:
        # Refuses seeding the primary checkout directly.
        direct = self.seed(self.root)
        self.assertNotEqual(direct.returncode, 0)
        self.assertIn("primary checkout", direct.stderr)

        # Refuses seeding through a worktree symlink to the primary checkout.
        wt_link = self.tmp / "link-to-root"
        wt_link.symlink_to(self.root, target_is_directory=True)
        via_link = self.seed(wt_link)
        self.assertNotEqual(via_link.returncode, 0)
        self.assertIn("primary checkout", via_link.stderr)

        # Refuses any cache/package symlink inside a worktree that points into the primary checkout.
        for rel, target_in_root in (
            (".lake", self.root / ".lake"),
            (".lake/packages", self.root / ".lake/packages"),
            (".lake/build", self.root / ".lake/build"),
            (".lake/config", self.root / ".lake/config"),
            (".lake/packages/cslib", self.root / ".lake/packages/cslib"),
        ):
            with self.subTest(rel=rel):
                wt = self.tmp / ("bad-" + rel.replace("/", "-"))
                link = wt / rel
                link.parent.mkdir(parents=True, exist_ok=True)
                link.symlink_to(target_in_root, target_is_directory=True)
                res = self.seed(wt)
                self.assertNotEqual(res.returncode, 0)
                self.assertIn("primary checkout", res.stderr)

        # Refuses a shared packages root inside the primary checkout.
        wt_env = self.tmp / "bad-env-wt"
        res_env = self.seed(wt_env, COMPLEXITYLIB_SHARED_PACKAGES_ROOT=str(self.root / ".lake"))
        self.assertNotEqual(res_env.returncode, 0)
        self.assertIn("primary checkout", res_env.stderr)


@unittest.skipUnless(shutil.which("git"), "git is required")
class WorktreePruneTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.tmp = pathlib.Path(tmp.name)
        self.root = self.tmp / "root"
        self.root.mkdir()
        git(self.root, "init", "--quiet", "-b", "main")
        (self.root / "scripts").mkdir()
        shutil.copy(SCRIPT, self.root / "scripts/worktree.sh")
        (self.root / ".gitignore").write_text("/.worktrees/\n/.worktrees-lookalike/\n.lake/\n")
        (self.root / "README").write_text("base\n")
        git(self.root, "add", ".")
        git(self.root, "commit", "--quiet", "-m", "fixture")
        self.branch_count = 0

    def registered(self, path: pathlib.Path) -> pathlib.Path:
        self.branch_count += 1
        git(self.root, "worktree", "add", "--quiet", "-b", f"worker-{self.branch_count}",
            str(path), "main")
        return self.cache(path)

    def cache(self, path: pathlib.Path) -> pathlib.Path:
        cache = path / ".lake/sentinel"
        cache.parent.mkdir(parents=True, exist_ok=True)
        cache.write_bytes(b"keep this cache\n")
        return cache

    def prune(self, *flags: str, env=None) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["bash", str(self.root / "scripts/worktree.sh"), "prune-merged", "main", *flags],
            capture_output=True, text=True, check=False, env=GIT_ENV if env is None else env,
        )

    def test_unregistered_directory_retains_its_cache(self) -> None:
        cache = self.cache(self.root / ".worktrees/plain")
        result = self.prune()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(cache.read_bytes(), b"keep this cache\n")

    def test_locked_worktree_retains_cache_and_does_not_block_other_pruning(self) -> None:
        locked = self.root / ".worktrees/locked"
        cache = self.registered(locked)
        git(self.root, "worktree", "lock", "--reason", "active worker", str(locked))
        removable = self.root / ".worktrees/removable"
        self.registered(removable)
        result = self.prune()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("locked", result.stdout)
        self.assertEqual(cache.read_bytes(), b"keep this cache\n")
        self.assertFalse(removable.exists())
        self.assertIn(str(locked.resolve()), git(self.root, "worktree", "list", "--porcelain"))

    def test_merged_registered_worktree_with_special_path_is_removed_by_git(self) -> None:
        for name in ("merged worker", "merged\nworker"):
            with self.subTest(name=name):
                target = self.root / ".worktrees" / name
                self.registered(target)
                dependency = target / ".lake/packages/demo"
                dependency.mkdir(parents=True)
                git(dependency, "init", "--quiet")
                result = self.prune()
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertFalse(target.exists())
                self.assertNotIn(str(target.resolve()),
                                 git(self.root, "worktree", "list", "--porcelain", "-z"))

    def test_dry_run_preserves_cache_and_registration(self) -> None:
        target = self.root / ".worktrees/merged"
        cache = self.registered(target)
        result = self.prune("--dry-run")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Would remove", result.stdout)
        self.assertEqual(cache.read_bytes(), b"keep this cache\n")
        self.assertIn(str(target.resolve()), git(self.root, "worktree", "list", "--porcelain"))

    def test_git_refusal_after_a_late_edit_preserves_work_and_cache(self) -> None:
        target = self.root / ".worktrees/late-edit"
        cache = self.registered(target)
        wrapper = self.tmp / "bin/git"
        wrapper.parent.mkdir()
        wrapper.write_text('''#!/usr/bin/env bash
if [ "${1:-}" = "worktree" ] && [ "${2:-}" = "remove" ]; then
  printf 'late untracked work\\n' > "$LATE_FILE"
fi
exec "$REAL_GIT" "$@"
''')
        wrapper.chmod(0o755)
        late_file = target / "late-work"
        result = self.prune(env={**GIT_ENV, "REAL_GIT": shutil.which("git"),
                                 "LATE_FILE": str(late_file),
                                 "PATH": str(wrapper.parent) + os.pathsep + os.environ["PATH"]})
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(cache.read_bytes(), b"keep this cache\n")
        self.assertEqual(late_file.read_bytes(), b"late untracked work\n")
        self.assertIn(str(target.resolve()), git(self.root, "worktree", "list", "--porcelain"))

    def test_dirty_and_unmerged_worktrees_retain_caches(self) -> None:
        dirty = self.root / ".worktrees/dirty"
        dirty_cache = self.registered(dirty)
        (dirty / "README").write_text("uncommitted work\n")
        unmerged = self.root / ".worktrees/unmerged"
        unmerged_cache = self.registered(unmerged)
        (unmerged / "README").write_text("unmerged work\n")
        git(unmerged, "add", "README")
        git(unmerged, "commit", "--quiet", "-m", "worker change")
        result = self.prune()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("dirty working tree", result.stdout)
        self.assertIn("unmerged commits", result.stdout)
        self.assertEqual(dirty_cache.read_bytes(), b"keep this cache\n")
        self.assertEqual(unmerged_cache.read_bytes(), b"keep this cache\n")

    def test_foreign_worktree_retains_cache(self) -> None:
        foreign = self.tmp / "foreign"
        foreign.mkdir()
        git(foreign, "init", "--quiet", "-b", "main")
        (foreign / ".gitignore").write_text(".lake/\n")
        git(foreign, "add", ".")
        git(foreign, "commit", "--quiet", "-m", "foreign fixture")
        target = self.root / ".worktrees/foreign"
        git(foreign, "worktree", "add", "--quiet", "-b", "worker", str(target))
        cache = self.cache(target)
        result = self.prune()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(cache.read_bytes(), b"keep this cache\n")
        self.assertIn(str(target.resolve()), git(foreign, "worktree", "list", "--porcelain"))

    def test_symlinked_worktree_retains_cache(self) -> None:
        target = self.root / ".worktrees/linked"
        self.registered(target)
        moved = self.tmp / "moved-worker"
        target.rename(moved)
        target.symlink_to(moved, target_is_directory=True)
        result = self.prune()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((moved / ".lake/sentinel").read_bytes(), b"keep this cache\n")
        self.assertTrue(target.is_symlink())

    def test_prefix_lookalike_and_nested_worktrees_stay_outside_scope(self) -> None:
        nearby = self.root / ".worktrees-lookalike/nearby"
        nearby_cache = self.registered(nearby)
        parent = self.root / ".worktrees/group"
        parent_cache = self.cache(parent)
        nested_cache = self.registered(parent / "nested")
        result = self.prune()
        self.assertEqual(result.returncode, 0, result.stderr)
        for cache in (nearby_cache, parent_cache, nested_cache):
            self.assertEqual(cache.read_bytes(), b"keep this cache\n")


if __name__ == "__main__":
    unittest.main()
