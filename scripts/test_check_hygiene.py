"""Unit tests for scripts/check_hygiene.py."""

from __future__ import annotations

import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_hygiene  # noqa: E402


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


if __name__ == "__main__":
    unittest.main()
