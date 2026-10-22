"""Unit tests for the branch selection of `scripts/worktree.sh create`."""

from __future__ import annotations

import os
import pathlib
import shutil
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


if __name__ == "__main__":
    unittest.main()
