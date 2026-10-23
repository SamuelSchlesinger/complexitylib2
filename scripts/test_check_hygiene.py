"""Unit tests for scripts/check_hygiene.py."""

from __future__ import annotations

import pathlib
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_hygiene  # noqa: E402
import proof_lengths  # noqa: E402


class CheckHygieneTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        (self.root / "Complexity").mkdir()
        (self.root / "ComplexityTests").mkdir()

    def write(self, rel: str, content: str) -> pathlib.Path:
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
        return p

    def test_clean_candidate_module_passes(self) -> None:
        p = self.write(
            "Complexity/Clean.lean",
            "module\n"
            "-- upstream: candidate\n\n"
            "-- Justified heartbeat bump for large polynomial ring normalizer.\n"
            "set_option maxHeartbeats 400000 in\n"
            "theorem demo : True := by\n"
            "  simp only [and_self]\n"
            "  simp +decide only [and_self]\n"
            "  simp (config := { decide := true }) only [and_self]\n"
            "  simp\n",
        )
        self.assertEqual(check_hygiene.check_file(p, root=self.root, check_simp=True), [])

    def test_missing_upstream_marker_fails(self) -> None:
        p = self.write("Complexity/NoMarker.lean", "module\ntheorem demo : True := trivial\n")
        errors = check_hygiene.check_file(p, root=self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("missing or invalid `-- upstream:` marker", errors[0])

    def test_unjustified_set_option_fails(self) -> None:
        p = self.write(
            "Complexity/UnjustifiedOption.lean",
            "module\n"
            "-- upstream: candidate\n\n"
            "\n\n\n"
            "set_option maxHeartbeats 400000 in\n"
            "theorem demo : True := trivial\n",
        )
        errors = check_hygiene.check_file(p, root=self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("requires a justifying comment", errors[0])

    def test_set_option_justified_on_the_next_line_passes(self) -> None:
        p = self.write(
            "Complexity/MathlibStyleOption.lean",
            "module\n"
            "-- upstream: candidate\n\n"
            "\n\n\n"
            "set_option maxHeartbeats 400000 in\n"
            "-- Mathlib's maxHeartbeats linter expects the reason on this line.\n"
            "theorem demo : True := trivial\n",
        )
        self.assertEqual(check_hygiene.check_file(p, root=self.root), [])

    def test_forbidden_tokens_and_nonterminal_simp(self) -> None:
        p = self.write(
            "Complexity/BadProof.lean",
            "module\n"
            "-- upstream: candidate\n\n"
            "axiom bad_ax : False\n"
            "theorem t1 : True := by\n"
            "  simp\n"
            "  exact trivial\n"
            "theorem t2 : True := by sorry\n",
        )
        errors = check_hygiene.check_file(p, root=self.root, check_simp=True)
        self.assertEqual(len(errors), 3)
        self.assertTrue(any("forbidden custom `axiom`" in e for e in errors))
        self.assertTrue(any("non-terminal bare `simp`" in e for e in errors))
        self.assertTrue(any("forbidden `sorry`" in e for e in errors))

    def test_quote_characters_do_not_hide_forbidden_theorem(self) -> None:
        for literal in ("'\"'", r"'\"'"):
            with self.subTest(literal=literal):
                p = self.write(
                    "Complexity/Quote.lean",
                    "module\n-- upstream: candidate\n"
                    f"def quote : Char := {literal}\n"
                    "theorem hole : True := by sorry\n"
                    f"def quoteAgain : Char := {literal}\n",
                )
                self.assertEqual(check_hygiene.check_file(p, root=self.root),
                                 ["Complexity/Quote.lean:4: forbidden `sorry`"])

    def test_character_masks_preserve_offsets_and_count_literal_proofs(self) -> None:
        literals = ("'a'", "'é'", "'😊'", "'('", "')'", "'['", "']'", "'{'", "'}'",
                    r"'\''", r"'\\'", r"'\n'", r"'\r'",
                    r"'\t'", r"'\x22'", r"'\u0022'")
        for literal in literals:
            with self.subTest(literal=literal):
                text = f"theorem quoted : {literal} = {literal} := by\n  rfl\n"
                code, syntax = proof_lengths.masks(text)
                self.assertEqual(code, text)
                self.assertEqual(len(syntax), len(text))
                self.assertEqual([i for i, c in enumerate(syntax) if c == "\n"],
                                 [i for i, c in enumerate(text) if c == "\n"])
                self.assertEqual(syntax.count("'"), 0)
                rows = proof_lengths.scan(text, "Complexity/Quote.lean")
                self.assertEqual([(row["name"], row["body_lines"]) for row in rows],
                                 [("quoted", 1)])

    def test_primed_identifiers_are_not_character_literals(self) -> None:
        names = ("lemma'a'", "lemma!'a'", "lemma?'a'", "α'a'")
        text = "\n".join(f"theorem {name} : True := True.intro" for name in names)
        code, syntax = proof_lengths.masks(text)
        self.assertEqual((code, syntax), (text, text))
        self.assertEqual([row["name"] for row in proof_lengths.scan(text, "Complexity/Prime.lean")],
                         list(names))

    def test_character_literal_text_in_strings_and_comments_is_ignored(self) -> None:
        p = self.write(
            "Complexity/QuotedText.lean",
            "module\n-- upstream: candidate\n"
            r'''def text := "'\"' sorry"''' + "\n"
            "-- '\"' sorry\n"
            "/- outer '\"' /- sorry -/ comment -/\n"
            "def quote : Char := '\"'\n"
            "theorem hole : True := by native_decide\n",
        )
        self.assertEqual(check_hygiene.check_file(p, root=self.root),
                         ["Complexity/QuotedText.lean:7: forbidden `native_decide`"])


class CheckHygieneCLITests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name).resolve()
        self.empty = self.root / "empty"
        self.empty.mkdir()
        self.clean = self.root / "Clean.lean"
        self.clean.write_text("theorem clean : True := trivial\n", encoding="utf-8")
        self.bad = self.root / "Bad.lean"
        self.bad.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
        self.missing = self.root / "missing"

    def run_checker(self, *paths: pathlib.Path) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, "-B", str(pathlib.Path(check_hygiene.__file__)),
             *map(str, paths)],
            cwd=self.root, capture_output=True, text=True, check=False,
        )

    def test_empty_directory_fails_without_success_message(self) -> None:
        result = self.run_checker(self.empty)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, "")
        self.assertEqual(result.stderr, "ERROR: no source files found in selected paths\n")

    def test_missing_path_fails_without_traceback(self) -> None:
        result = self.run_checker(self.missing)
        self.assertEqual(result.returncode, 1)
        self.assertIn(f"ERROR: {self.missing}: input path does not exist\n", result.stderr)
        self.assertNotIn("Traceback", result.stderr)
        self.assertEqual(result.stdout, "")

    def test_empty_directory_does_not_hide_clean_file(self) -> None:
        for paths in ((self.clean,), (self.empty, self.clean)):
            with self.subTest(paths=paths):
                result = self.run_checker(*paths)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout, "All hygiene checks passed.\n")
                self.assertEqual(result.stderr, "")

    def test_mixed_selection_reports_both_missing_path_and_violation(self) -> None:
        result = self.run_checker(self.empty, self.missing, self.bad)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, "")
        self.assertIn(f"ERROR: {self.missing}: input path does not exist\n", result.stderr)
        self.assertIn(f"ERROR: {self.bad}:1: forbidden `sorry`\n", result.stderr)
        self.assertNotIn("no source files", result.stderr)
        self.assertNotIn("Traceback", result.stderr)


if __name__ == "__main__":
    unittest.main()
