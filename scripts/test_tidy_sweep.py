"""Unit tests for the pure helpers of scripts/tidy_sweep.py."""

from __future__ import annotations

import contextlib
import io
import json
import pathlib
import sys
import tempfile
import unittest
from collections import defaultdict
from types import SimpleNamespace

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
        scope = scopes.at(text.index("theorem a"))
        self.assertEqual(scope.namespace, "Cslib.Logic")
        self.assertEqual([o.namespace for o in scope.opens], ["Turing.MultiTapeTM", POLY])
        self.assertEqual(scopes.at(text.index("theorem b")).opens, (t.Open("Foo"),))
        self.assertEqual(scopes.at(text.index("theorem c")), t.Scope(""))
        self.assertEqual(scopes.prefixes(text.index("theorem a"))[:3],
                         ["Cslib.Logic", "Cslib", ""])


class ClassificationTests(unittest.TestCase):
    def classify(self, d: dict, c: dict, twins=None, constants=None, private=None):
        return t.classify_decl(d, c, twins or {}, constants or {d["name"]: c}, private or {})

    def test_case_two_renames_and_checks_the_target(self) -> None:
        e = self.classify(decl("A.computableTidilyInPolyTime_x"), const())
        self.assertEqual((e.case, e.target), ("2", "A.computableInPolyTime_x"))
        e = self.classify(decl("A.mem_X_iff"), const())
        self.assertEqual((e.case, e.target), ("2", "A.mem_X_iff"))

    def test_collisions(self) -> None:
        c = const(ph="1")
        # A target that still states tidy computability is not a twin.
        constants = {"A.computableTidilyInPolyTime_x": c,
                     "A.computableInPolyTime_x": const(ph="2")}
        e = self.classify(decl("A.computableTidilyInPolyTime_x"), c, constants=constants)
        self.assertEqual((e.case, e.reason), ("unclassifiable", "collision"))
        # A private declaration of the same module blocks the name as well.
        e = self.classify(decl("A.computableTidilyInPolyTime_y"), c,
                          private={"Complexity.M": {"A.computableInPolyTime_y"}})
        self.assertEqual((e.reason, e.detail), ("collision", "the target is private"))

    def test_committed_plain_twins(self) -> None:
        original = const(ph="5")
        constants = {POLY + ".map": original, PLAIN + ".map": const(tidy=(), ph="5"),
                     POLY + ".comp": original, PLAIN + ".comp": const(tidy=(), ph="6"),
                     POLY + ".fst": original, PLAIN + ".fst": const(ph="5"),
                     POLY + ".snd": original, PLAIN + ".snd": const(tidy=(), e="")}
        twins = t.discover_twins(constants)
        self.assertEqual(twins, {POLY + ".map": (PLAIN + ".map", "exact"),
                                 POLY + ".comp": (PLAIN + ".comp", "by name")})
        e = self.classify(decl(POLY + ".comp"), original, twins, constants)
        self.assertEqual((e.case, e.target, e.twin), ("1", PLAIN + ".comp", "by name"))
        self.assertEqual(len(e.warnings), 1)
        twins = t.twin_map(constants, {POLY + ".fst": "Missing.twin"})
        self.assertEqual(twins[POLY + ".fst"], ("Missing.twin", "registry"))
        e = self.classify(decl(POLY + ".fst"), original, twins, constants)
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

    def test_allowlist_ignores_comments(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "a.txt"
            path.write_text("# header\nA/B.lean\n\nC.lean  # note\n")
            self.assertEqual(t.load_allowlist(path), {"A/B.lean", "C.lean"})


class RegistryTests(unittest.TestCase):
    """Review 5635891057: malformed or ambiguous registry input is an error."""

    def load(self, data) -> dict:
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "r.json"
            path.write_text(data if isinstance(data, str) else json.dumps(data))
            return t.load_registry(path)

    def test_valid_shapes(self) -> None:
        self.assertEqual(self.load([{"original": "a", "plain": "b", "module": "M"}]), {"a": "b"})
        self.assertEqual(self.load({"pairs": [{"original": "c", "plain": "d"}]}), {"c": "d"})
        # Repeating a pair is harmless.
        self.assertEqual(self.load([{"original": "a", "plain": "b"}] * 2), {"a": "b"})
        self.assertEqual(t.load_registry(None), {})

    def test_malformed_input_is_rejected(self) -> None:
        cases = {
            "misspelled key": {"pair": [{"original": "a", "plain": "b"}]},
            "extra key": {"pairs": [], "version": 1},
            "not an array": {"pairs": {"a": "b"}},
            "scalar": "3",
            "not JSON": "[{",
            "missing plain": [{"original": "a"}],
            "unknown entry key": [{"original": "a", "plain": "b", "kind": "x"}],
            "empty name": [{"original": "", "plain": "b"}],
            "blank name": [{"original": "a", "plain": " b"}],
            "non-string": [{"original": "a", "plain": 3}],
            "entry not an object": [["a", "b"]],
            "own twin": [{"original": "a", "plain": "a"}],
            "conflicting twins": [{"original": "o", "plain": "p"},
                                  {"original": "o", "plain": "q"}],
        }
        for label, data in cases.items():
            with self.assertRaises(ValueError, msg=label):
                self.load(data)

    def test_a_requested_file_must_exist(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaisesRegex(ValueError, "not found"):
                t.load_registry(pathlib.Path(tmp) / "missing.json")


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


def fake_source(text: str, namespaces: set[str]) -> t.SourceFile:
    src = object.__new__(t.SourceFile)
    src.path = t.qr.source_path("M")
    src.text = text
    src.code, src.mask = masks(text)
    src.lines = text.split("\n")
    src.starts = [0]
    for line in src.lines:
        src.starts.append(src.starts[-1] + len(line) + 1)
    src.commands = [m.start() for m in t.qr.COMMAND_START.finditer(src.mask)]
    src._namespaces, src._scopes = namespaces, None
    return src


def fake_planner(text: str, constants: dict, known=(), privates=None, refs=()):
    """A planner over one source `Fake.lean` (module `M`) without a build."""
    p = object.__new__(t.Planner)
    p.model = SimpleNamespace(constants=constants, owners={},
                              lib=SimpleNamespace(ileans={}))
    p.known = set(known) | set(constants)
    p.privates = privates or {}
    p.twins, p.force_wrap = {}, frozenset()
    p.namespaces = t.namespaces_of(p.known)
    src = fake_source(text, p.namespaces)
    p.sources = {src.path: src}
    p._refs = {"M": [t.Ref(n, a, b, None) for n, a, b in refs]}
    p._locals = {}
    p._decl_spans = {}
    p.deferred = {}
    p.batch = {}
    p.reset()
    return p, src


class ConvertTests(unittest.TestCase):
    def convert(self, text: str, sg, at: str | None = None) -> tuple[str, str]:
        at = at or (".X" if ".X" in text else "X")
        p, src = fake_planner(text, {"X": {"m": "M", "sg": sg, "tidy": [POLY]}},
                              known={"Y"})
        p.renames = {"X": "Y"}
        start = text.index(at)
        p.convert(src.path, "M", start, start + len(at), "X", None, "tidy")
        fe = p.files[src.path]
        blocked = "; ".join(p.blockers.get("X", []))
        return t.render(text, fe.replaces, fe.wraps, 0, len(text)), blocked

    def test_application_keeps_its_old_type(self) -> None:
        sg = [[[1, 0], [0, 0], [0, 1]], 1]  # {V} (enc) (hc : tidy) : tidy
        self.assertEqual(self.convert("  exact X enc hc", sg),
                         ("  exact (Y enc (.of_tidy hc)).tidy", ""))
        self.assertEqual(self.convert("  exact (X enc hc).comp g", sg)[0],
                         "  exact (Y enc (.of_tidy hc)).tidy.comp g")
        self.assertEqual(self.convert("  X (V := ℕ) enc hc", sg)[0],
                         "  (Y (V := ℕ) enc (.of_tidy hc)).tidy")

    def test_constants_and_dot_chains(self) -> None:
        self.assertEqual(self.convert("  exact X.comp h", [[[1, 0]], 1])[0],
                         "  exact Y.tidy.comp h")

    def test_leading_dot_with_a_plain_conclusion(self) -> None:
        # `.of_foo h : DecidableInExpTime …`: the expected type does not change, so only the
        # tidy argument is converted. The `.ilean` span includes the leading dot.
        p, src = fake_planner("  exact .of_foo hc", {"N.of_foo": {"m": "M",
                              "sg": [[[0, 1]], 0], "tidy": [POLY]}}, known={"N.of_bar"})
        p.renames = {"N.of_foo": "N.of_bar"}
        start = src.text.index(".of_foo")
        self.assertTrue(p.convert(src.path, "M", start, start + 7, "N.of_foo", None, "tidy"))
        fe = p.files[src.path]
        # The new name is written explicitly: see `ResolutionTests.test_dot_notation`.
        self.assertEqual(t.render(src.text, fe.replaces, fe.wraps, 0, len(src.text)),
                         "  exact N.of_bar (.of_tidy hc)")
        self.assertTrue(t.spells(".of_foo", "N.of_foo"))

    def test_unconvertible_sites_stay_unchanged(self) -> None:
        """Review 5635891057: a skipped call keeps its text (no rename, no partial wraps) and
        blocks the referenced declaration, which is then deferred."""
        cases = [("  map X", [[[0, 0]], 1], "partial"),
                 ("  simp [X]", [[[0, 0]], 1], "lemma list"),
                 ("  exact .X a", [[[0, 0]], 1], "leading-dot"),
                 ("  X a", [[[0, 2]], 1], "binders"),
                 ("  X a", [[[1, 1], [0, 0]], 1], "implicit"),
                 # The argument is tidy, but the conclusion is not a bare predicate.
                 ("  X hc", [[[0, 1]], 2], "bare"),
                 # The first argument converts, the second cannot.
                 ("  X hc hd", [[[0, 1], [0, 2]], 1], "binders")]
        for text, sg, reason in cases:
            out, blocked = self.convert(text, sg)
            self.assertEqual(out, text, text)
            self.assertIn(reason, blocked, text)


class ResolutionTests(unittest.TestCase):
    """Review 5635891057: a replacement must denote its target from where it is written, and a
    stale span is never edited."""

    TEXT = ("namespace A\n\nopen Turing.MultiTapeTM\n\n"
            "theorem t (f : ℕ → ℕ) : ComputableTidilyInPolyTime f e e := sorry\n\nend A\n")

    def written(self, text: str, token: str, old: str, new: str, known=(), privates=None,
                refs=()):
        p, src = fake_planner(text, {old: {"m": "M"}, new: {"m": "M"}}, known, privates, refs)
        start = text.index(token)
        return p.written("M", src, start, start + len(token), old, new)

    def test_a_shadowing_declaration_forces_a_longer_name(self) -> None:
        # `A.ComputableInPolyTime` would capture a bare `ComputableInPolyTime` inside `A`.
        written, _ = self.written(self.TEXT, "ComputableTidilyInPolyTime", POLY, PLAIN,
                                  known={"A.ComputableInPolyTime"})
        self.assertEqual(written, PLAIN)
        written, _ = self.written(self.TEXT, "ComputableTidilyInPolyTime", POLY, PLAIN)
        self.assertEqual(written, "ComputableInPolyTime")

    def test_private_names_of_the_module_shadow_too(self) -> None:
        written, _ = self.written(self.TEXT, "ComputableTidilyInPolyTime", POLY, PLAIN,
                                  privates={"M": {"A.ComputableInPolyTime"}})
        self.assertEqual(written, PLAIN)

    def test_local_binders_shadow_short_names(self) -> None:
        text = ("namespace B\n\ntheorem t (map : ℕ) : True := by\n  exact Old.map\n\nend B\n")
        start = text.index("Old.map")
        refs = [("Old.map", start, start + len("Old.map"))]
        written, _ = self.written(text, "Old.map", "Old.map", "B.map", refs=refs)
        self.assertEqual(written, "B.map")  # `map` alone is the binder

    def test_root_prefix_when_every_suffix_is_ambiguous(self) -> None:
        known = {"A.Turing.MultiTapeTM.ComputableInPolyTime", "A.ComputableInPolyTime",
                 "A.MultiTapeTM.ComputableInPolyTime"}
        written, _ = self.written(self.TEXT, "ComputableTidilyInPolyTime", POLY, PLAIN, known)
        self.assertEqual(written, "_root_." + PLAIN)

    def test_stale_spans_are_not_edited(self) -> None:
        text = "theorem t : True := completelyUnrelated\n"
        written, why = self.written(text, "completelyUnrelated", POLY, PLAIN)
        self.assertIsNone(written)
        self.assertIn("does not spell", why)
        self.assertTrue(t.spells("ComputableTidilyInPolyTime", POLY))
        self.assertTrue(t.spells("@MultiTapeTM.ComputableTidilyInPolyTime", POLY))
        self.assertFalse(t.spells("TidilyInPolyTime", POLY))
        self.assertFalse(t.spells("", POLY))


class CaptureTests(unittest.TestCase):
    """Review 5636433742: section variables, aliases, notations, selective opens and the types
    behind dot notation can capture a written name."""

    def written(self, text: str, token: str, old: str, new: str, known=(), nth: int = 0):
        start = -1
        for _ in range(nth + 1):
            start = text.index(token, start + 1)
        p, src = fake_planner(text, {old: {"m": "M"}, new: {"m": "M"}}, known,
                              refs=[(old, start, start + len(token))])
        return p.written("M", src, start, start + len(token), old, new)[0]

    def test_section_variables(self) -> None:
        text = ("open N\n\nsection\n\nvariable (bar : Nat)\n\ndef before : Nat := foo\n\n"
                "end\n\ndef later : Nat := foo\n")
        self.assertEqual(self.written(text, "foo", "N.foo", "N.bar"), "N.bar")
        # Outside the section the variable no longer binds `bar`.
        self.assertEqual(self.written(text, "foo", "N.foo", "N.bar", nth=1), "bar")
        self.assertEqual(t.binder_names(" {α : Type} (a b : ℕ) [Fintype α] [h : DecidableEq α]"),
                         {"α", "a", "b", "h"})

    def test_aliases_and_notations(self) -> None:
        for prefix in ("open M renaming baz → bar\n", "export M (bar)\n",
                       'local notation "bar" => 0\n'):
            text = prefix + "open N\n\ndef d : Nat := foo\n"
            self.assertEqual(self.written(text, "foo", "N.foo", "N.bar"), "N.bar", prefix)

    def test_opens_that_do_not_surely_make_the_target_visible(self) -> None:
        for line in ("open N (foo)", "open N hiding bar", "open scoped N"):
            text = line + "\n\ndef d : Nat := N.foo\n"
            self.assertEqual(self.written(text, "N.foo", "N.foo", "N.bar"), "N.bar", line)
        # A selective open that lists the new name makes it visible.
        text = "open N (foo bar)\n\ndef d : Nat := foo\n"
        self.assertEqual(self.written(text, "foo", "N.foo", "N.bar", nth=1), "bar")
        text = "open N (foo)\n\ndef d : Nat := foo\n"
        self.assertEqual(self.written(text, "foo", "N.foo", "N.bar", nth=1), "N.bar")

    def test_names_outside_the_references_capture_too(self) -> None:
        # `M.bar` exists in the import closure although nothing here refers to it.
        text = "open M N\n\ndef d : Nat := foo\n"
        self.assertEqual(self.written(text, "foo", "N.foo", "N.bar", known={"M.bar"}), "N.bar")

    def test_new_names_must_not_capture_other_references(self) -> None:
        text = "open A B\n\ndef d : Nat := x + B.x + n.x\n"
        spans = {"x ": "B.x", "B.x": "B.x", "x\n": "Nat.x"}
        usages = defaultdict(list)
        for token, name in spans.items():
            start = text.index(token) if token != "x\n" else text.index("n.x") + 2
            usages[name].append(("M", [2, start - text.index("def"), 2,
                                       start - text.index("def") + len(token.strip())]))
        p, src = fake_planner(text, {"A.y": {"m": "M"}}, known={"B.x", "Nat.x"})
        p.model.users = lambda name: usages.get(name, [])
        p.model.referenced_by_last = lambda last: [n for n in usages if n.endswith("." + last)]
        # Renaming `A.y` to `A.x` would make the bare `x` (now `B.x`) ambiguous.
        found = p.captures("A.y", "A.x")
        self.assertEqual(len(found), 1)
        self.assertIn("could capture `x` (`B.x`)", found[0])
        # Without the bare and dotted references, the qualified `B.x` is safe.
        usages["B.x"] = usages["B.x"][1:]
        del usages["Nat.x"]
        self.assertEqual(p.captures("A.y", "A.x"), [])

    def test_dot_notation(self) -> None:
        # `abbrev W := Nat` with `W.bar`: `.bar` and `x.bar` would select `W.bar`, not `Nat.bar`.
        known = {"W", "W.bar"}
        self.assertEqual(self.written("def a : W := .foo\n", ".foo", "Nat.foo", "Nat.bar",
                                      known), "Nat.bar")
        self.assertIsNone(self.written("def a := (0 : W).foo\n", "foo", "Nat.foo", "Nat.bar",
                                       known))
        # The tidy predicate's own namespace follows the restated type at the site.
        self.assertEqual(self.written("example := hf.comp hg\n", "comp", POLY + ".comp",
                                      PLAIN + ".comp"), "comp")


class VerificationTests(unittest.TestCase):
    """Review 5635891057: verification is strict, reports failures and exits nonzero."""

    def test_builds_are_strict(self) -> None:
        calls = []

        def runner(cmd, **_):
            calls.append(cmd)
            return SimpleNamespace(returncode=1, stdout="", stderr="")
        self.assertEqual(t.lake_build(["Complexity"], runner)[0], 1)
        self.assertEqual(calls, [["lake", "build", "--wfail", "--iofail", "Complexity"]])

    def check(self, output: str, code: int) -> dict:
        planner = SimpleNamespace(decls={}, force_wrap=frozenset())
        return t.check_build(planner, {}, output, code, 1)

    def test_status_is_passed_only_without_errors(self) -> None:
        self.assertEqual(self.check("", 0)["status"], "passed")
        self.assertEqual(self.check("", 1)["status"], "failed")
        error = "error: Complexity/Nope.lean:3:0: unknown identifier 'x'\n"
        self.assertEqual(self.check(error, 0)["status"], "failed")
        sorry = "warning: Complexity/Nope.lean:3:8: declaration uses `sorry`\n"
        self.assertEqual(self.check(sorry, 1)["status"], "failed")

    def test_rewrite_writes_reports_and_fails_honestly(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "M.lean"
            path.write_text("old\n")

            class FakePlanner:
                def __init__(self, *args):
                    self.decls, self.force_wrap = {}, frozenset()

                def plan(self):
                    return self

                def render(self):
                    return {path: "new\n"}

                def source(self, _):
                    return SimpleNamespace(text="old\n")

            def build(_):
                return 1, "warning: Complexity/M.lean:1:8: declaration uses `sorry`\n"
            original = t.Planner
            t.Planner = FakePlanner
            try:
                _, result = t.rewrite(None, [], {}, "Logics", True, 3, build)
            finally:
                t.Planner = original
            self.assertEqual(path.read_text(), "new\n")
            self.assertEqual(result["status"], "failed")
            self.assertEqual(len(result["history"]), 1)
            plans = [{"build": result}]
            self.assertEqual(t.exit_status(plans), 1)
            self.assertIn("FAILED", t.plan_markdown({"summary": {
                "area": "Logics", "declarations": 0, "modes": {}, "sites": {}, "imports": [],
                "manual": {}}, "manual": [], "build": result}))
            self.assertEqual(t.exit_status([{"build": None}]), 0)

    def test_measurement_stubs_and_unchecked_rewrites_are_refused(self) -> None:
        with tempfile.TemporaryDirectory() as tmp, \
                contextlib.redirect_stderr(io.StringIO()) as err:
            for argv in (["rewrite", "--area", "Logics", "--stub-failures"],
                         ["rewrite", "--area", "Logics", "--no-build-check"],
                         ["rewrite", "--area", "Logics", "--diff", "p.patch", "--verify"],
                         ["report", "--registry", str(pathlib.Path(tmp) / "missing.json")]):
                with self.assertRaises(SystemExit, msg=argv) as raised:
                    t.main(argv)
                self.assertEqual(raised.exception.code, 2)
        self.assertIn("--no-build-check is only for report", err.getvalue())
        self.assertIn("--diff previews without building", err.getvalue())
        self.assertIn("registry file not found", err.getvalue())


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
