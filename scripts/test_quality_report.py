"""Unit tests for the pure helpers of scripts/quality_report.py."""

from __future__ import annotations

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import quality_report as q  # noqa: E402


class QualityReportTests(unittest.TestCase):
    def test_areas_follow_the_program_table(self) -> None:
        self.assertEqual(q.area_of("Foundations/Data/List/Basic.lean"), "Foundations")
        self.assertEqual(q.area_of("Probability/PMF.lean"), "Foundations")
        self.assertEqual(q.area_of("Computability/Probabilistic/PTM.lean"), "Machines")
        self.assertEqual(q.area_of("Computability/PCP/Basic.lean"), "Classes")
        self.assertEqual(q.area_of("Computability/Circuit/Defs.lean"), "Circuit")
        self.assertEqual(q.area_of("Algorithms/Lean/Queue.lean"), "WordRAM")
        self.assertEqual(q.area_of("Computability/GenericRAM/Defs.lean"), q.OTHER_AREA)
        self.assertEqual(q.area_of("Init/"), q.OTHER_AREA)

    def test_module_roles(self) -> None:
        self.assertEqual(q.module_role("Complexity.Foundations.Data.List.Basic"), "lib")
        self.assertEqual(q.module_role("ComplexityTests.Smoke"), "test")
        self.assertEqual(q.module_role("ComplexityTests.Abstracts.All"), "abstract")
        self.assertEqual(q.module_role("ComplexityAbstracts.CookLevinBridge"), "abstract")

    def test_generated_constants_belong_to_their_owner(self) -> None:
        owners = {"Foo": "Foo", "Foo.bar": "Foo", "baz": "baz", "Ns.f": "Ns.f"}
        self.assertEqual(q.owner_of("Foo.bar", owners), "Foo")
        self.assertEqual(q.owner_of("baz.eq_1", owners), "baz")
        self.assertEqual(q.owner_of("baz.eq_def", owners), "baz")
        self.assertEqual(q.owner_of("Foo.mk.injEq", owners), "Foo")
        self.assertEqual(q.owner_of("Ns.f._proof_3", owners), "Ns.f")
        self.assertEqual(q.owner_of("Ns.f.match_2.splitter", owners), None)
        self.assertIsNone(q.owner_of("Foo.unrelated", owners))
        self.assertIsNone(q.owner_of("Mathlib.thing", owners))

    def test_unfolding_by_name(self) -> None:
        self.assertTrue(q.unfolds_by_name("f.eq_1", "f"))
        self.assertTrue(q.unfolds_by_name("f.eq_def", "f"))
        self.assertTrue(q.unfolds_by_name("f.induct", "f"))
        self.assertFalse(q.unfolds_by_name("f", "f"))
        self.assertFalse(q.unfolds_by_name("f.mk", "f"))
        self.assertFalse(q.unfolds_by_name("fg.eq_1", "f"))

    def test_utf16_columns(self) -> None:
        self.assertEqual(q.utf16_index("abc def", 4), 4)
        line = "𝔅 x := foo"  # 𝔅 takes two UTF-16 units
        self.assertEqual(line[q.utf16_index(line, 8):], "foo")
        self.assertEqual(q.utf16_index("ℕ → foo", 4), 4)

    def test_unfolding_positions(self) -> None:
        def at(before: str, previous: tuple[str, ...] = ()) -> bool:
            lines = [*previous, before + "target rest"]
            return q.unfolds_at(lines, len(lines) - 1, len(before))

        self.assertTrue(at("  unfold "))
        self.assertTrue(at("  unfold other "))
        self.assertTrue(at("  delta "))
        self.assertTrue(at("  simp only [foo, "))
        self.assertTrue(at("  rw [← "))
        self.assertTrue(at("  simp (config := {}) only ["))
        self.assertTrue(at("    ", ("  simp only [foo,",)))
        self.assertFalse(at("  exact "))
        self.assertFalse(at("  rw [sum_coe_sort T fun i => p."))
        self.assertFalse(at("  simp [f "))
        self.assertFalse(at("  rw [show a = b from "))
        self.assertFalse(at("  exact ⟨"))
        self.assertFalse(at("  refine foo ["))

    def test_attributes_and_keywords(self) -> None:
        keyword, attrs = q.header_info(
            "@[simp, aesop safe apply (rule_sets := [PolyTime]), local instance] theorem foo")
        self.assertEqual(keyword, "theorem")
        self.assertEqual(attrs, {"simp", "aesop"})
        self.assertEqual(q.header_info("@[expose] public def bar")[0], "def")
        self.assertEqual(q.header_info("@[deprecated (since := \"2026-10-19\")] alias x")[1],
                         {"deprecated"})
        self.assertEqual(q.header_info("noncomputable instance")[0], "instance")
        self.assertEqual(q.attribute_names("scoped simp, simps!"), {"simp", "simps"})

    def test_listed_names(self) -> None:
        doc = """
# Title

Mentions `Ignored.name` in prose.

## Main definitions

* `Foo.bar`, `Foo.baz`: two things, related to `NotListed`.
* `Long.first`,
  `Long.second`: a bullet continued on the next line.
* `.relative`: a name relative to the previous one.
* `u ≼ v` is notation, not a name.

## Main results

* `Foo.bar_spec`

## References
* `Not.a.result`: references are not listed.
"""
        self.assertEqual(q.listed_names(doc), [
            "Foo.bar", "Foo.baz", "Long.first", "Long.second", "relative", "Foo.bar_spec"])

    def test_name_matching(self) -> None:
        self.assertTrue(q.matches("Cslib.Foo.bar", "Foo.bar"))
        self.assertTrue(q.matches("Cslib.Foo.bar", "Cslib.Foo.bar"))
        self.assertFalse(q.matches("Cslib.Foo.foobar", "bar"))
        self.assertTrue(q.matches("_private.Complexity.A.B.0.Cslib.Foo.bar", "Foo.bar"))
        self.assertTrue(q.mentioned({"Foo.bar", "x"}, "Cslib.Foo.bar"))
        self.assertFalse(q.mentioned({"bar"}, "Cslib.Foo.foobar"))

    def test_rebuild_fanout_follows_public_reexports(self) -> None:
        # D publicly imports C, which publicly imports A; B imports A privately; E imports B.
        imports = {"A": [], "B": [("A", False)], "C": [("A", True)], "D": [("C", True)],
                   "E": [("B", True)], "F": [("D", False)]}
        fanout = q.rebuild_fanout(imports)
        self.assertEqual(fanout["A"], {"B", "C", "D", "F"})
        self.assertEqual(fanout["B"], {"E"})
        importers = q.transitive_importers(imports)
        self.assertEqual(importers["A"], {"B", "C", "D", "E", "F"})


if __name__ == "__main__":
    unittest.main()
