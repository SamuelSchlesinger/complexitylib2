"""Unit tests for the pure helpers of scripts/quality_report.py."""

from __future__ import annotations

import json
import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import quality_report as q  # noqa: E402


class QualityReportTests(unittest.TestCase):
    def test_areas_follow_the_program_table(self) -> None:
        self.assertEqual(q.area_of("Foundations/Data/List/Basic/"), "Foundations")
        self.assertEqual(q.area_of("Probability/PMF/"), "Foundations")
        self.assertEqual(q.area_of("Computability/BitString/Basic/"), "Foundations")
        self.assertEqual(q.area_of("Computability/Probabilistic/PTM/"), "Machines")
        self.assertEqual(q.area_of("Computability/PCP/Basic/"), "Classes")
        self.assertEqual(q.area_of("Computability/Circuit/Defs/"), "Circuit")
        self.assertEqual(q.area_of("Algorithms/Lean/Queue/"), "WordRAM")
        self.assertEqual(q.area_of("Init/"), q.OTHER_AREA)

    def test_areas_assigned_after_the_program_table(self) -> None:
        # #587's assignment of the paths its table left out.
        for path in ("Computability/GenericRAM/Defs/", "Computability/RAM/Basic/",
                     "Tactic/PolyTime/"):
            self.assertEqual(q.area_of(path), "Machines", path)
        self.assertEqual(q.area_of("Computability/BranchingProgram/Defs/"), "Circuit")
        for path in ("Computability/Kolmogorov/Basic/", "Computability/MCSP/Basic/",
                     "Computability/USTCON/Reader/", "Computability/Languages/Regular/",
                     "MachineLearning/UniformLearning/"):
            self.assertEqual(q.area_of(path), "Classes", path)
        # A module file named like an assigned directory belongs to it as well.
        self.assertEqual(q.area_of("Tactic/"), "Machines")

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

    def test_documentation_in_another_module_protects(self) -> None:
        # Module A defines the declarations; only module B's docstring names `docApi`.
        names = ["Cslib.Fixture.docApi", "Cslib.Fixture.helper", "Cslib.Other.mono",
                 "Cslib.Fixture.mono", "Cslib.Fixture.monotone"]
        doc_b = "/-! Module B builds on `Cslib.Fixture.docApi` and on `mono`. -/"
        named = q.doc_named(names, q.doc_tokens(doc_b))
        self.assertIn("Cslib.Fixture.docApi", named)
        self.assertNotIn("Cslib.Fixture.helper", named)
        # An ambiguous short name protects every declaration it could denote.
        self.assertTrue({"Cslib.Other.mono", "Cslib.Fixture.mono"} <= named)
        self.assertNotIn("Cslib.Fixture.monotone", named)
        self.assertEqual(q.doc_named(names, q.doc_tokens("`Fixture.docApi`")),
                         {"Cslib.Fixture.docApi"})

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


class OutputCheckTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.reference = pathlib.Path(tmp.name) / "current"
        self.copy = pathlib.Path(tmp.name) / "copy"
        for directory in (self.reference, self.copy):
            self.write(directory, "Complexity/A.ilean", "{}")
            self.write(directory, "Complexity/A.olean", "a")
            self.write(directory, "Complexity/A.c", "ignored")

    @staticmethod
    def write(directory: pathlib.Path, rel: str, text: str) -> None:
        path = directory / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def check(self, build_dir: pathlib.Path, skip: bool = False, current: bool = True) -> str:
        return q.check_outputs(build_dir, skip, current=lambda: current, reference=self.reference)

    def test_identical_custom_directory_is_checked(self) -> None:
        self.write(self.copy, "Complexity/A.c", "other files do not matter")
        self.assertIn("identical", self.check(self.copy))
        self.assertIn("lake build --no-build", self.check(self.reference))

    def test_stale_custom_directory_is_refused(self) -> None:
        # The current outputs gained a declaration that the copied directory lacks.
        self.write(self.reference, "Complexity/A.olean", "a with a new declaration")
        self.write(self.reference, "Complexity/B.ilean", "{}")
        with self.assertRaises(SystemExit) as error:
            self.check(self.copy)
        self.assertIn("2 file(s)", str(error.exception.code))
        self.assertEqual(q.output_differences(self.copy, self.reference),
                         ["Complexity/A.olean", "Complexity/B.ilean"])

    def test_stale_default_outputs_are_refused(self) -> None:
        with self.assertRaises(SystemExit):
            self.check(self.reference, current=False)

    def test_unchecked_reports_say_so(self) -> None:
        self.write(self.reference, "Complexity/A.olean", "changed")
        self.assertIn("not checked", self.check(self.copy, skip=True))

    def write_ileans(self, modules: dict[str, list[str]]) -> None:
        """Write an `.ilean` file for each module, with the given direct imports."""
        for module, imports in modules.items():
            self.write(self.reference, module.replace(".", "/") + ".ilean", json.dumps(
                {"module": module, "directImports": [[i, False, False, False] for i in imports]}))

    def test_outputs_of_deleted_modules_are_ignored(self) -> None:
        self.write_ileans({"Complexity": ["Complexity.A"], "ComplexityTests": [],
                           "ComplexityAbstracts": [], "Complexity.A": ["Mathlib.Init"],
                           "Complexity.Deleted": []})
        self.assertEqual(list(q.load_ileans(self.reference)), ["Complexity.A"])

    def test_missing_reachable_output_is_refused(self) -> None:
        self.write_ileans({"Complexity": ["Complexity.Live"], "ComplexityTests": [],
                           "ComplexityAbstracts": [], "Complexity.Live": ["Complexity.Missing"]})
        with self.assertRaises(SystemExit) as error:
            q.load_ileans(self.reference)
        self.assertIn("Missing.ilean is missing (imported by Complexity.Live)",
                      str(error.exception.code))

    def test_missing_root_output_is_refused(self) -> None:
        self.write_ileans({"Complexity": [], "ComplexityTests": []})
        with self.assertRaises(SystemExit) as error:
            q.load_ileans(self.reference)
        self.assertIn("ComplexityAbstracts.ilean is missing (a root)", str(error.exception.code))


if __name__ == "__main__":
    unittest.main()
