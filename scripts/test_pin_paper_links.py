"""Unit tests for scripts/pin_paper_links.py."""

from __future__ import annotations

import contextlib
import io
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import pin_paper_links  # noqa: E402

GIT_ENV = {
    **os.environ,
    "GIT_AUTHOR_NAME": "Test",
    "GIT_AUTHOR_EMAIL": "test@example.com",
    "GIT_COMMITTER_NAME": "Test",
    "GIT_COMMITTER_EMAIL": "test@example.com",
    "GIT_CONFIG_GLOBAL": os.devnull,
    "GIT_CONFIG_NOSYSTEM": "1",
}


class PinPaperLinksTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        (self.root / "paper/sections").mkdir(parents=True)
        (self.root / "Complexity/Demo").mkdir(parents=True)
        (self.root / "paper/main.tex").write_text(
            "\\newcommand{\\decl}[3]{\\declat{8d38f7753b6c651c3363a157c806d05794d6ea11}{#1}{#2}{#3}}\n",
            encoding="utf-8",
        )

    def test_parse_declarations_with_namespaces_and_root(self) -> None:
        source = (
            "/-\nHeader comment with theorem fake_in_comment\n-/\n"
            "@[expose] public section\n"
            "namespace Cslib.Demo\n"
            "section Inner\n"
            "@[simp] theorem first_thm : True := trivial\n"
            "noncomputable def _root_.TopLevel.helper : Nat := 0\n"
            "end Inner\n"
            "theorem after_inner_sec : True := trivial\n"
            "end Cslib.Demo\n"
            "end\n"
        )
        decls = pin_paper_links.parse_declarations(source)
        self.assertEqual(decls[7], ("first_thm", "Cslib.Demo.first_thm"))
        self.assertEqual(decls[8], ("TopLevel.helper", "TopLevel.helper"))
        self.assertEqual(decls[10], ("after_inner_sec", "Cslib.Demo.after_inner_sec"))
        self.assertEqual(
            pin_paper_links.find_declaration_line(decls, "Cslib.Demo.first_thm"), 7
        )
        self.assertEqual(
            pin_paper_links.find_declaration_line(decls, "TopLevel.helper"), 8
        )
        self.assertEqual(
            pin_paper_links.find_declaration_line(decls, "Cslib.Demo.after_inner_sec"),
            10,
        )

    def test_check_and_pin_worktree_links(self) -> None:
        lean_file = self.root / "Complexity/Demo/Basic.lean"
        lean_file.write_text(
            "namespace Cslib.Demo\n"
            "\n"
            "theorem alpha_eq : 1 = 1 := rfl\n"
            "def beta_val : Nat := 42\n"
            "end Cslib.Demo\n",
            encoding="utf-8",
        )
        tex_file = self.root / "paper/sections/demo.tex"
        tex_file.write_text(
            "\\declat{1111111111111111111111111111111111111111}"
            "{Complexity/Demo/Basic.lean}{3}{Cslib.Demo.alpha\\_eq}\n"
            "\\decl{Complexity/Demo/Basic.lean}{4}{Cslib.Demo.beta\\_val}\n",
            encoding="utf-8",
        )
        checked, errors = pin_paper_links.check_links(self.root, worktree_only=True)
        self.assertEqual(checked, 2)
        self.assertEqual(errors, [])

        # Insert two lines at the top of Basic.lean so line numbers shift by +2.
        lean_file.write_text(
            "-- extra line 1\n"
            "-- extra line 2\n"
            "namespace Cslib.Demo\n"
            "\n"
            "theorem alpha_eq : 1 = 1 := rfl\n"
            "def beta_val : Nat := 42\n"
            "end Cslib.Demo\n",
            encoding="utf-8",
        )
        _, errors_shifted = pin_paper_links.check_links(self.root, worktree_only=True)
        self.assertEqual(len(errors_shifted), 2)

        new_sha = "2222222222222222222222222222222222222222"
        updated = pin_paper_links.pin_links(
            new_sha,
            root=self.root,
            path_prefix="Complexity/Demo/",
            use_worktree=True,
        )
        self.assertEqual(updated, 2)
        checked_after, errors_after = pin_paper_links.check_links(
            self.root, worktree_only=True
        )
        self.assertEqual(checked_after, 2)
        self.assertEqual(errors_after, [])
        self.assertIn(f"\\declat{{{new_sha}}}{{Complexity/Demo/Basic.lean}}{{5}}", tex_file.read_text())
        self.assertIn(f"\\declat{{{new_sha}}}{{Complexity/Demo/Basic.lean}}{{6}}", tex_file.read_text())

    def test_nested_attributes_and_atomic_pin_links(self) -> None:
        lean_file = self.root / "Complexity/Demo/Attr.lean"
        lean_file.write_text(
            "namespace Cslib.Demo\n"
            "@[simp, deprecated old (since := \"2026-10-22\") [foo]] irreducible_def tagged_def : Nat := 1\n"
            "end Cslib.Demo\n",
            encoding="utf-8",
        )
        decls = pin_paper_links.parse_declarations(lean_file.read_text(encoding="utf-8"))
        self.assertEqual(decls[2], ("tagged_def", "Cslib.Demo.tagged_def"))

        tex_a = self.root / "paper/sections/a.tex"
        tex_b = self.root / "paper/sections/b.tex"
        original_a = (
            "\\declat{1111111111111111111111111111111111111111}"
            "{Complexity/Demo/Attr.lean}{1}{Cslib.Demo.tagged\\_def}\n"
        )
        tex_a.write_text(original_a, encoding="utf-8")
        tex_b.write_text(
            "\\declat{1111111111111111111111111111111111111111}"
            "{Complexity/Demo/Attr.lean}{1}{Cslib.Demo.nonexistent}\n",
            encoding="utf-8",
        )
        with self.assertRaises(ValueError):
            pin_paper_links.pin_links(
                "3333333333333333333333333333333333333333",
                root=self.root,
                use_worktree=True,
            )
        # Ensure tex_a was not partially written when tex_b failed.
        self.assertEqual(tex_a.read_text(encoding="utf-8"), original_a)

    def test_check_requires_full_names(self) -> None:
        (self.root / "Complexity/Demo/Basic.lean").write_text(
            "namespace Cslib.Demo\ntheorem alpha_eq : 1 = 1 := rfl\nend Cslib.Demo\n",
            encoding="utf-8",
        )
        (self.root / "paper/sections/demo.tex").write_text(
            "\\declat{1111111111111111111111111111111111111111}"
            "{Complexity/Demo/Basic.lean}{2}{Demo.alpha\\_eq}\n",
            encoding="utf-8",
        )
        checked, errors = pin_paper_links.check_links(self.root, worktree_only=True)
        self.assertEqual(checked, 1)
        self.assertEqual(len(errors), 1)
        self.assertIn("found Cslib.Demo.alpha_eq", errors[0])
        with self.assertRaisesRegex(ValueError, "same short name: Cslib.Demo.alpha_eq"):
            pin_paper_links.find_declaration_line(
                pin_paper_links.parse_declarations(
                    (self.root / "Complexity/Demo/Basic.lean").read_text(encoding="utf-8")
                ),
                "Demo.alpha_eq",
            )

    def test_main_tex_links_are_checked_but_macro_definitions_skipped(self) -> None:
        (self.root / "Complexity/Demo/Basic.lean").write_text(
            "namespace Cslib.Demo\ntheorem alpha_eq : 1 = 1 := rfl\nend Cslib.Demo\n",
            encoding="utf-8",
        )
        main_tex = self.root / "paper/main.tex"
        main_tex.write_text(
            main_tex.read_text(encoding="utf-8")
            + "\\newcommand{\\demo}{\\declat{1111111111111111111111111111111111111111}"
            "{Complexity/Demo/Basic.lean}{9}{Cslib.Demo.missing}}\n"
            "\\declat{1111111111111111111111111111111111111111}"
            "{Complexity/Demo/Basic.lean}{1}{Cslib.Demo.alpha\\_eq}\n",
            encoding="utf-8",
        )
        checked, errors = pin_paper_links.check_links(self.root, worktree_only=True)
        self.assertEqual(checked, 1)
        self.assertEqual(len(errors), 1)
        self.assertIn("paper/main.tex", errors[0])


@unittest.skipUnless(shutil.which("git"), "git is required")
class PinCommandTests(unittest.TestCase):
    """`main(["--pin", ...])`: SHA validation and diagnostics for unresolvable links."""

    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        (self.root / "paper/sections").mkdir(parents=True)
        (self.root / "Complexity/Demo").mkdir(parents=True)
        (self.root / "paper/main.tex").write_text(
            "\\newcommand{\\decl}[3]{\\declat{8d38f7753b6c651c3363a157c806d05794d6ea11}{#1}{#2}{#3}}\n",
            encoding="utf-8",
        )
        (self.root / "Complexity/Demo/Basic.lean").write_text(
            "namespace Cslib.Demo\n\ntheorem alpha_eq : 1 = 1 := rfl\nend Cslib.Demo\n",
            encoding="utf-8",
        )
        self.tex = self.root / "paper/sections/demo.tex"
        self.tex.write_text(
            "\\declat{1111111111111111111111111111111111111111}"
            "{Complexity/Demo/Basic.lean}{1}{Cslib.Demo.alpha\\_eq}\n",
            encoding="utf-8",
        )
        self.git("init", "--quiet", "-b", "main")
        self.git("add", ".")
        self.git("commit", "--quiet", "-m", "base")
        self.head = self.git("rev-parse", "HEAD")

    def git(self, *args: str) -> str:
        return subprocess.run(
            ["git", "-C", str(self.root), *args],
            capture_output=True,
            text=True,
            check=True,
            env=GIT_ENV,
        ).stdout.strip()

    def run_main(self, *argv: str) -> tuple[int, str]:
        err = io.StringIO()
        with contextlib.redirect_stderr(err), contextlib.redirect_stdout(io.StringIO()):
            code = pin_paper_links.main(list(argv), root=self.root)
        return code, err.getvalue()

    def test_pin_to_ancestor_full_sha_succeeds(self) -> None:
        code, err = self.run_main("--pin", self.head)
        self.assertEqual(code, 0, err)
        self.assertIn(
            f"\\declat{{{self.head}}}{{Complexity/Demo/Basic.lean}}{{3}}", self.tex.read_text()
        )

    def test_pin_rejects_abbreviated_sha(self) -> None:
        original = self.tex.read_text()
        code, err = self.run_main("--pin", self.head[:12])
        self.assertEqual(code, 1)
        self.assertIn("full 40-character", err)
        self.assertEqual(self.tex.read_text(), original)

    def test_pin_rejects_unknown_sha(self) -> None:
        code, err = self.run_main("--pin", "f" * 40)
        self.assertEqual(code, 1)
        self.assertIn("not a commit", err)

    def test_pin_rejects_non_ancestor_sha(self) -> None:
        self.git("switch", "--quiet", "-c", "side")
        self.git("commit", "--quiet", "--allow-empty", "-m", "side")
        side = self.git("rev-parse", "HEAD")
        self.git("switch", "--quiet", "main")
        original = self.tex.read_text()
        code, err = self.run_main("--pin", side)
        self.assertEqual(code, 1)
        self.assertIn("not an ancestor of HEAD", err)
        self.assertEqual(self.tex.read_text(), original)

    def test_pin_reports_tex_file_lean_path_and_hint(self) -> None:
        self.tex.write_text(
            self.tex.read_text()
            + "\\declat{1111111111111111111111111111111111111111}"
            "{Complexity/Demo/Basic.lean}{1}{Cslib.Demo.renamed}\n",
            encoding="utf-8",
        )
        self.git("commit", "--quiet", "-am", "add a stale link")
        head = self.git("rev-parse", "HEAD")
        original = self.tex.read_text()
        code, err = self.run_main("--pin", head)
        self.assertEqual(code, 1)
        self.assertIn("paper/sections/demo.tex", err)
        self.assertIn("Complexity/Demo/Basic.lean", err)
        self.assertIn("'Cslib.Demo.renamed' not found", err)
        self.assertIn("moved or renamed", err)
        self.assertNotIn("Traceback", err)
        self.assertEqual(self.tex.read_text(), original)


if __name__ == "__main__":
    unittest.main()
