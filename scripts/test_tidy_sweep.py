"""Unit tests for the pure helpers of scripts/tidy_sweep.py."""

from __future__ import annotations

import json
import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import tidy_sweep as t  # noqa: E402
from proof_lengths import masks  # noqa: E402

POLY = "Turing.MultiTapeTM.ComputableTidilyInPolyTime"
PLAIN = "Turing.MultiTapeTM.ComputableInPolyTime"


def decl(name: str, kind: str = "thm", role: str = "decl", attrs=(), keyword="theorem",
         area: str = "Logics") -> dict:
    return {"name": name, "module": "Complexity.M", "path": "M.lean", "area": area,
            "role": role, "kind": kind, "keyword": keyword, "attrs": set(attrs),
            "implicit": [], "lib_refs": set(), "test_refs": set(), "abstract_refs": set()}


def const(tidy=(POLY,), ph: str = "1", e: str = "axiom", tb=()) -> dict:
    return {"m": "Complexity.M", "k": "thm", "e": e, "tidy": list(tidy), "tb": list(tb),
            "ph": ph}


class NameTests(unittest.TestCase):
    def test_plain_name_replaces_supported_notions_only(self) -> None:
        self.assertEqual(t.plain_name("A.computableTidilyInPolyTime_foo"),
                         "A.computableInPolyTime_foo")
        self.assertEqual(t.plain_name(POLY + ".comp"), PLAIN + ".comp")
        self.assertEqual(t.plain_name("x_computableTidilyInO_y"), "x_computableInO_y")
        self.assertEqual(t.plain_name("Cslib.Complexity.ComputableTidilyInFPTTime.of_x"),
                         "Cslib.Complexity.ComputableInFPTTime.of_x")
        for unsupported in ("computableTidilyInDegree_foo", "ComputableTidilyInTimeAndSpace.x",
                            "computableTidilyInOracle", "ComputesTidily"):
            self.assertEqual(t.plain_name(unsupported), unsupported)

    def test_notion_bridges(self) -> None:
        notion = t.BY_TIDY[POLY]
        self.assertEqual(notion.dot_of_tidy, POLY + ".computableInPolyTime")
        self.assertIn(PLAIN + ".of_tidy", t.BRIDGES)
        self.assertIn(notion.iff, t.BRIDGES)

    def test_renamed_token_keeps_the_written_prefix(self) -> None:
        old = "Cslib.A.CNF.computableTidilyInPolyTime_vars"
        new = "Cslib.A.CNF.computableInPolyTime_vars"
        self.assertEqual(t.renamed_token("CNF.computableTidilyInPolyTime_vars", old, new),
                         "CNF.computableInPolyTime_vars")
        self.assertEqual(t.renamed_token("@CNF.computableTidilyInPolyTime_vars", old, new),
                         "@CNF.computableInPolyTime_vars")
        self.assertEqual(t.renamed_token(old, old, new), new)
        # Written relative to the tidy namespace: the prefix itself changes.
        self.assertIsNone(t.renamed_token("map", POLY + ".map", PLAIN + ".map"))

    def test_written_name_is_the_shortest_unambiguous_suffix(self) -> None:
        known = {PLAIN + ".map", "Other.ComputableInPolyTime.map", "List.map"}
        self.assertEqual(t.written_name(PLAIN + ".map", ["Turing.MultiTapeTM", ""], known),
                         "ComputableInPolyTime.map")
        self.assertEqual(t.written_name(PLAIN + ".map", [PLAIN, ""], known), "map")
        # `ComputableInPolyTime.map` is ambiguous when `Other` is open too.
        self.assertEqual(t.written_name(PLAIN + ".map", ["Turing.MultiTapeTM", "Other", ""],
                                        known), PLAIN + ".map")
        self.assertEqual(t.written_name(PLAIN + ".map", ["Turing", "Other", ""], known),
                         "MultiTapeTM.ComputableInPolyTime.map")

    def test_scopes_track_namespaces_and_opens(self) -> None:
        text = ("namespace Cslib.Logic\n\nopen Turing.MultiTapeTM ComputableTidilyInPolyTime\n\n"
                "theorem a : True := trivial\n\nend Cslib.Logic\n\nopen Foo in\n"
                "theorem b : True := trivial\n\ntheorem c : True := trivial\n")
        scopes = t.Scopes(masks(text)[1], t.namespaces_of([POLY + ".map", "Foo.x"]))
        namespace, opens = scopes.at(text.index("theorem a"))
        self.assertEqual(namespace, "Cslib.Logic")
        self.assertEqual(opens, ("Turing.MultiTapeTM", POLY))
        self.assertEqual(scopes.at(text.index("theorem b")), ("", ("Foo",)))
        self.assertEqual(scopes.at(text.index("theorem c")), ("", ()))
        self.assertEqual(scopes.prefixes(text.index("theorem a"))[:3],
                         ["Cslib.Logic", "Cslib", ""])


class ClassificationTests(unittest.TestCase):
    def classify(self, d: dict, c: dict, registry=None, constants=None, private=None):
        return t.classify_decl(d, c, registry or {}, constants or {d["name"]: c}, private or {})

    def test_case_two_renames_and_checks_the_target(self) -> None:
        e = self.classify(decl("A.computableTidilyInPolyTime_x"), const())
        self.assertEqual((e.case, e.target), ("2", "A.computableInPolyTime_x"))
        e = self.classify(decl("A.mem_X_iff"), const())
        self.assertEqual((e.case, e.target), ("2", "A.mem_X_iff"))

    def test_collisions(self) -> None:
        c = const(ph="1")
        constants = {"A.computableTidilyInPolyTime_x": c,
                     "A.computableInPolyTime_x": const(tidy=(), ph="2")}
        e = self.classify(decl("A.computableTidilyInPolyTime_x"), c, constants=constants)
        self.assertEqual((e.case, e.reason), ("unclassifiable", "collision"))
        self.assertFalse(e.collision["equivalent"])
        constants["A.computableInPolyTime_x"]["ph"] = "1"
        e = self.classify(decl("A.computableTidilyInPolyTime_x"), c, constants=constants)
        self.assertTrue(e.collision["equivalent"])
        # A private declaration of the same module blocks the name as well.
        e = self.classify(decl("A.computableTidilyInPolyTime_y"), c,
                          private={"Complexity.M": {"A.computableInPolyTime_y"}})
        self.assertEqual(e.reason, "collision")

    def test_registered_twin_is_case_one(self) -> None:
        c = const(ph="5")
        constants = {POLY + ".map": c, PLAIN + ".map": const(tidy=(), ph="5")}
        e = self.classify(decl(POLY + ".map"), c, {POLY + ".map": PLAIN + ".map"}, constants)
        self.assertEqual((e.case, e.target, e.warnings), ("1", PLAIN + ".map", []))
        e = self.classify(decl(POLY + ".map"), c, {POLY + ".map": "Missing.twin"}, constants)
        self.assertEqual(e.reason, "registered twin missing")

    def test_unclassifiable_reasons(self) -> None:
        degree = "Turing.MultiTapeTM.ComputableTidilyInDegree"
        e = self.classify(decl("A.foo"), const(tidy=(POLY, degree)))
        self.assertEqual(e.reason, "unsupported notion")
        e = self.classify(decl("A.foo", attrs=("deprecated",)), const())
        self.assertEqual(e.reason, "deprecated alias")
        e = self.classify(decl("A.pSimulates_iff_tidy"), const())
        self.assertEqual(e.reason, "bridge")
        e = self.classify(decl(PLAIN + ".of_tidy"), const())
        self.assertEqual(e.reason, "bridge")
        e = self.classify(decl("A.ComputableTidilyInX", kind="def", keyword="def"), const())
        self.assertEqual(e.reason, "tidy notion definition")

    def test_definitions_and_fields_are_case_three(self) -> None:
        e = self.classify(decl("A.P", kind="def", keyword="def"), const(tidy=(), tb=(POLY,)))
        self.assertEqual((e.case, e.kind, e.body_only), ("3", "definition", True))
        e = self.classify(decl("A.S.polyTime", role="member"), const())
        self.assertEqual((e.case, e.kind), ("3", "structure field"))

    def test_registry_formats(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "r.json"
            path.write_text(json.dumps([{"original": "a", "plain": "b", "module": "M"}]))
            self.assertEqual(t.load_registry(path), {"a": "b"})
            path.write_text(json.dumps({"pairs": [{"original": "c", "plain": "d"}]}))
            self.assertEqual(t.load_registry(path), {"c": "d"})
            path.write_text(json.dumps([{"original": "c"}]))
            with self.assertRaises(ValueError):
                t.load_registry(path)
            self.assertEqual(t.load_registry(pathlib.Path(tmp) / "missing.json"), {})

    def test_allowlist_ignores_comments(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "a.txt"
            path.write_text("# header\nA/B.lean\n\nC.lean  # note\n")
            self.assertEqual(t.load_allowlist(path), {"A/B.lean", "C.lean"})


class ParsingTests(unittest.TestCase):
    def test_brackets_and_top_level_tokens(self) -> None:
        text = "(a : b := c) : T := x"
        self.assertEqual(t.match_bracket(text, 0), 11)
        self.assertEqual(t.find_top_level(text, 0, len(text), ":"), 13)
        self.assertEqual(t.find_top_level(text, 0, len(text), ":="), 17)

    def test_parse_decl(self) -> None:
        text = ("theorem foo {f : V → W} [DecidableEq V]\n    (hf hg : P f e e) (x : ℕ := 0) :\n"
                "    P (g ∘ f) e e := by\n  simp\n")
        mask = masks(text)[1]
        start = text.index("foo")
        dt = t.parse_decl(mask, 0, start, start + 3, len(text.rstrip()))
        self.assertEqual([b.bracket for b in dt.binders], ["{", "[", "(", "("])
        self.assertEqual(dt.binders[2].names, ["hf", "hg"])
        self.assertEqual(text[dt.binders[2].type_start:dt.binders[2].type_end].strip(), "P f e e")
        self.assertTrue(dt.binders[3].default)
        self.assertEqual(text[dt.colon + 1:dt.assign].strip(), "P (g ∘ f) e e")
        self.assertEqual(dt.problems, [])
        body, tactic = t.proof_parts(text, dt.assign, dt.end)
        self.assertTrue(tactic)
        dt = t.parse_decl(masks("theorem f : T\n  | 0 => a")[1], 0, 8, 9, 23)
        self.assertIn("no `:=` (pattern-matching definition)", dt.problems)

    def test_arguments(self) -> None:
        text = "X (f := id) a (b c) ⟨d, e⟩ h.1 |>.comp\n  more"
        mask = masks(text)[1]
        named = []
        args = t.parse_args(mask, 1, len(mask), 5, 0, named)
        self.assertEqual([text[a:b] for a, b in args], ["a", "(b c)", "⟨d, e⟩", "h.1"])
        self.assertEqual([text[a:b] for a, b in named], ["(f := id)"])
        # Arguments continue on a more indented line, and stop at keywords.
        text = "  X a\n    b\n  c"
        self.assertEqual(len(t.parse_args(text, 3, len(text), 3, 2)), 2)
        self.assertEqual(t.parse_args("X by simp", 1, 9, 1, 0), [])

    def test_atomic_application(self) -> None:
        text = "P f (encList e) enc"
        self.assertEqual(t.is_atomic_application(text, 0, len(text)), (0, 1))
        self.assertIsNone(t.is_atomic_application("P f → Q g", 0, 9))
        self.assertIsNone(t.is_atomic_application("∀ n, P n", 0, 8))

    def test_receiver_and_opener(self) -> None:
        text = "foo (bar baz).qux"
        self.assertEqual(t.receiver_start(text, text.index(".qux")), 4)
        text = "foo hf.comp"
        self.assertEqual(t.receiver_start(text, text.index(".comp")), 4)
        text = "simp [a, b]"
        self.assertEqual(t.enclosing_opener(text, 9), 5)


class EditTests(unittest.TestCase):
    def test_nested_wraps_render_inside_out(self) -> None:
        text = "f (X a) b"
        # The argument `(X a)` gets `(.of_tidy …)`; its own site appends `.tidy`.
        wraps = [t.Wrap(2, 7, "(.of_tidy ", ")", 0), t.Wrap(2, 7, "", ".tidy", 3)]
        reps = [t.Replace(3, 4, "Y")]
        self.assertEqual(t.render(text, reps, wraps, 0, len(text)), "f (.of_tidy (Y a).tidy) b")

    def test_regions_transform_their_edited_text(self) -> None:
        text = "a := X\nb"
        out = t.apply_edits(text, [t.Replace(5, 6, "Y")], [],
                            [t.Region(4, 6, lambda s: "[" + s + "]", "d")])
        self.assertEqual(out, "a :=[ Y]\nb")

    def test_round_trips(self) -> None:
        cases = {
            "f (.of_tidy (X a).tidy) b": "f (X a) b",
            "f (.of_tidy hV.tidy) b": "f hV b",
            "exact .of_tidy <| h.tidy\n": "exact h\n",
            "exact ComputableInPolyTime.of_tidy (h.tidy)": "exact h",
            "(X a).tidy.computableInPolyTime": "(X a)",
        }
        for before, after in cases.items():
            self.assertEqual(t.cancel_round_trips(before)[0], after, before)
        for kept in (".of_tidy <| (X a).tidy.comp h", ".of_tidy (f a.tidy)",
                     ".of_tidy <| h.tidy.comp g", "-- .of_tidy (h.tidy)"):
            self.assertEqual(t.cancel_round_trips(kept), (kept, 0), kept)


class WrapTests(unittest.TestCase):
    def test_term_without_hypotheses(self) -> None:
        self.assertEqual(t.wrap_proof("\n  map f", 2, 0, [], "P", True, "iff"),
                         "\n  .of_tidy (map f)")

    def test_term_with_hypotheses(self) -> None:
        hyps = [t.Hyp(["hf"], "P f", True), t.Hyp(["hg"], "∀ n, P (g n)", False)]
        self.assertEqual(
            t.wrap_proof("\n  (hf.comp\n    hg)", 2, 0, hyps, "P h", True, "iff"),
            " by\n  have hf := hf.tidy\n  have hg : ∀ n, P (g n) := by simpa only [iff] using hg"
            "\n  exact .of_tidy ((hf.comp\n    hg))")

    def test_tactic_block(self) -> None:
        body = " by\n  unfold f\n  fun_prop"
        self.assertEqual(t.wrap_proof(body, 2, 0, [t.Hyp(["h"], "P g", True)], "P f", True, "i"),
                         " by\n  have h := h.tidy\n  refine .of_tidy ?_\n  unfold f\n  fun_prop")
        self.assertEqual(t.wrap_proof(body, 2, 0, [], "P f ↔ Q", False, "i"),
                         " by\n  have this : P f ↔ Q := by\n    unfold f\n    fun_prop\n"
                         "  simpa only [i] using this")
        self.assertEqual(t.wrap_proof(" by simp", 2, 0, [t.Hyp(["h"], "P g", True)], None,
                                      False, "i"), " by\n  have h := h.tidy\n  simp")

    def test_reindent(self) -> None:
        self.assertEqual(t.reindent(["  a", "", "    b"], -2), ["a", "", "  b"])
        self.assertIsNone(t.reindent([" a"], -2))


class ConvertTests(unittest.TestCase):
    def planner(self, sg) -> t.Planner:
        p = object.__new__(t.Planner)
        p.model = type("M", (), {"constants": {"X": {"sg": sg}}})()
        return p

    def convert(self, text: str, sg, at: str = "X") -> tuple[str, str | None]:
        src = object.__new__(t.SourceFile)
        src.text, src.mask = text, masks(text)[1]
        fe = t.FileEdits()
        start = text.index(at)
        problem = self.planner(sg).convert_site(src, fe, start, start + len(at), "X")
        return t.render(text, fe.replaces, fe.wraps, 0, len(text)), problem

    def test_application_keeps_its_old_type(self) -> None:
        sg = [[[1, 0], [0, 0], [0, 1]], 1]  # {V} (enc) (hc : tidy) : tidy
        self.assertEqual(self.convert("  exact X enc hc", sg),
                         ("  exact (X enc (.of_tidy hc)).tidy", None))
        self.assertEqual(self.convert("  exact (X enc hc).comp g", sg)[0],
                         "  exact (X enc (.of_tidy hc)).tidy.comp g")
        self.assertEqual(self.convert("  X (V := ℕ) enc hc", sg)[0],
                         "  (X (V := ℕ) enc (.of_tidy hc)).tidy")

    def test_constants_and_dot_chains(self) -> None:
        self.assertEqual(self.convert("  exact X.comp h", [[[1, 0]], 1])[0],
                         "  exact X.tidy.comp h")

    def test_unconvertible_sites(self) -> None:
        sg = [[[0, 0]], 1]
        self.assertIn("partial", self.convert("  map X", sg)[1])
        self.assertIn("lemma list", self.convert("  simp [X]", sg)[1])
        self.assertIn("leading-dot", self.convert("  exact .X a", sg, "X")[1])
        self.assertIn("binders", self.convert("  X a", [[[0, 2]], 1])[1])
        self.assertIn("implicit", self.convert("  X a", [[[1, 1], [0, 0]], 1])[1])
        self.assertIn("bare", self.convert("  X a", [[[0, 0]], 2])[1])


class BuildOutputTests(unittest.TestCase):
    def test_diagnostics_and_declarations(self) -> None:
        out = ("✖ [3/4] Building M\nerror: ././././Complexity/M.lean:5:2: unknown identifier 'x'\n"
               "warning: Complexity/M.lean:9:0: unused variable `h`\n")
        self.assertEqual(t.diagnostics(out), [
            {"level": "error", "path": "Complexity/M.lean", "line": 5,
             "message": "unknown identifier 'x'"},
            {"level": "warning", "path": "Complexity/M.lean", "line": 9,
             "message": "unused variable `h`"}])
        text = "/-- doc -/\n@[simp]\ntheorem A.foo (x : ℕ) :\n    x = x := by\n  rfl\n"
        self.assertEqual(t.declaration_at(text, 5), "A.foo")
        # Lean reports some errors at the docstring, which belongs to the next declaration.
        text = ("theorem a : True := by\n  trivial\n\n/-- doc\nmore -/\n"
                "theorem b : True := trivial\n")
        self.assertEqual([t.declaration_at(text, n) for n in (2, 4, 6)], ["a", "b", "b"])
        self.assertEqual(t.command_line(text, 7), 6)
        self.assertTrue(t.CONSEQUENCE.search("❌️ Docstring on `#guard_msgs` does not match"))

    def test_module_paths(self) -> None:
        self.assertEqual(t.module_of(t.ROOT / "Complexity/A/B.lean"), "Complexity.A.B")
        self.assertEqual(t.module_of(t.ROOT / "abstracts/ComplexityAbstracts/X.lean"),
                         "ComplexityAbstracts.X")


class SummaryTests(unittest.TestCase):
    def test_counts_by_area_and_case(self) -> None:
        entries = [t.Entry("a", "M", "p", "Logics", "theorem", "2"),
                   t.Entry("b", "M", "p", "Logics", "theorem", "unclassifiable", "bridge"),
                   t.Entry("c", "M", "p", "Crypto", "definition", "3")]
        s = t.summary(entries)
        self.assertEqual(s["areas"]["Logics"], {"total": 2, "2": 1, "unclassifiable": 1})
        self.assertEqual(s["total"]["total"], 3)
        self.assertEqual(s["unclassifiable_reasons"], {"bridge": 1})
        self.assertEqual(list(s["areas"]), ["Crypto", "Logics"])


if __name__ == "__main__":
    unittest.main()
