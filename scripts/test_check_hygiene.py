"""Unit tests for scripts/check_hygiene.py."""

from __future__ import annotations

import pathlib
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


if __name__ == "__main__":
    unittest.main()
