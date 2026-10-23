"""Temporary-repository tests for worktree branch selection and cache isolation."""

from __future__ import annotations

import os
import pathlib
import shutil
import stat
import subprocess
import tempfile
import unittest

SCRIPT = pathlib.Path(__file__).resolve().parent / "worktree.sh"

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

    def create(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["bash", str(self.work / "scripts/worktree.sh"), "create", *args],
            cwd=self.work,
            capture_output=True,
            text=True,
            check=False,
            env=GIT_ENV,
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

    def test_create_isolates_seeded_dependency_caches(self) -> None:
        paths = [pathlib.Path(".lake/packages/cslib/.lake") / part
                 for part in ("build/trace", "config/lakefile.olean")]
        for path in paths:
            cache = self.work / path
            cache.parent.mkdir(parents=True, exist_ok=True)
            cache.write_bytes(b"root cache\n")
        result = self.create("feature/fresh", "fresh")
        self.assertEqual(result.returncode, 0, result.stderr)
        for path in paths:
            root, worker = self.work / path, self.work / ".worktrees/fresh" / path
            self.assertFalse(os.path.samefile(root, worker))
            worker.write_bytes(b"worker cache\n")
            self.assertEqual(root.read_bytes(), b"root cache\n")


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
        self.cache_paths = []
        for package in ("cslib", "mathlib"):
            source = self.root / ".lake/packages" / package / "Source.lean"
            source.parent.mkdir(parents=True)
            source.write_text("immutable source\n", encoding="utf-8")
            source.with_name("SourceLink.lean").symlink_to("Source.lean")
            self.cache_paths += [pathlib.Path("packages") / package / ".lake" / path
                                 for path in ("build/lib/Lean/Dependency.trace",
                                              "config/lakefile.olean")]
        self.cache_paths += [pathlib.Path("build/lib/Lean/Root.trace"),
                             pathlib.Path("config/lakefile.olean")]
        for path in self.cache_paths:
            cache = self.root / ".lake" / path
            cache.parent.mkdir(parents=True, exist_ok=True)
            cache.write_text(f"root cache {path}\n", encoding="utf-8")
            cache.chmod(0o640)
            os.utime(cache, ns=(1_700_000_000_000_000_000, 1_700_000_000_000_000_000))

    def seed(self, target: pathlib.Path, *flags: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["bash", str(self.root / "scripts/worktree.sh"), "seed", str(target), *flags],
            capture_output=True, text=True, check=False, env=GIT_ENV,
        )

    def assert_cache_isolated(self, target: pathlib.Path) -> None:
        for path in self.cache_paths:
            original = self.root / ".lake" / path
            seeded = target / ".lake" / path
            before = original.read_bytes()
            self.assertEqual(seeded.read_bytes(), before)
            self.assertNotEqual(original.stat().st_ino, seeded.stat().st_ino, str(path))
            self.assertEqual(stat.S_IMODE(seeded.stat().st_mode), 0o640)
            self.assertEqual(seeded.stat().st_mtime_ns, original.stat().st_mtime_ns)
            seeded.write_bytes(b"worker updated cache\n")
            self.assertEqual(original.read_bytes(), before, str(path))

    def test_all_copy_modes_isolate_root_and_dependency_caches(self) -> None:
        for flag in (None, "--copy-cslib", "--copy-packages"):
            with self.subTest(flag=flag):
                target = self.tmp / str(flag)
                result = self.seed(target, *([flag] if flag else []))
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assert_cache_isolated(target)
                for package in ("cslib", "mathlib"):
                    source = self.root / ".lake/packages" / package / "Source.lean"
                    seeded = target / ".lake/packages" / package / "Source.lean"
                    shared = flag != "--copy-packages" and not (
                        flag == "--copy-cslib" and package == "cslib")
                    self.assertEqual(source.stat().st_ino == seeded.stat().st_ino, shared)
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
                self.assert_cache_isolated(target)
                for path in ("build/lib/Lean/Root.trace", "packages/cslib/.lake",
                             "packages/mathlib"):
                    self.assertFalse((target / ".lake" / path).is_symlink())

    def test_existing_cache_is_preserved_on_repeated_seed(self) -> None:
        target = self.tmp / "worker"
        self.assertEqual(self.seed(target).returncode, 0)
        cache = target / ".lake" / self.cache_paths[0]
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
