"""Unit tests for scripts/pin_paper_links.py."""

from __future__ import annotations

import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import pin_paper_links  # noqa: E402


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


if __name__ == "__main__":
    unittest.main()
