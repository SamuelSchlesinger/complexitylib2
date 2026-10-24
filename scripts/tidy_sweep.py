#!/usr/bin/env python3
"""Plan and apply S2 of #456: remove tidy computability from public statements.

Usage: python3 scripts/tidy_sweep.py report [--area AREA]... [--json OUT] [--markdown OUT]
       python3 scripts/tidy_sweep.py rewrite --area AREA [--diff OUT | --verify [--rounds N]]
Common options: [--registry FILE] [--allowlist FILE] [--build-dir DIR]; report also accepts
[--no-build-check] and [--no-plan].

Plain computability is the API and tidy computability is how the machine layer proves it: outside
the raw machine constructions of the allowlist (`scripts/tidy_allowlist.txt`, from #608), no
public statement should mention a tidy notion. Every public declaration outside the allowlist
whose statement (its type, or the exposed body of a definition) mentions a tidy predicate falls
in one case of the S2 design
(https://github.com/cslib-community/complexitylib/issues/456#issuecomment-6376748411):

1. a theorem with a committed plain twin: proofs that become plain use the twin, and the
   original is left for S1/S3 to internalize;
2. any other theorem: it is renamed `computableTidily…` → `computable…` (the target name must be
   free) and restated with the plain predicates;
3. a definition, instance or structure field: it is listed for a hand-written plain redefinition.

The twin of a tidy theorem is the public plain theorem named by its plain rename (`exact` when its
statement is the syntactic plain transport, `by name` otherwise, for instance a broader canonical
rule). `--registry` adds pairs from a migration script: a JSON array of
`{"original": name, "plain": name, "module": module}` objects, validated strictly. A declaration
that fits none of the cases is *unclassifiable*: it mentions a tidy notion without a same-bound
plain equivalence, is a plain/tidy bridge or a deprecated alias, or its target name is taken (a
collision). `report` prints the classification with per-area counts (#587's areas) and each
area's rewrite plan, without writing anything.

`rewrite --area AREA` restates the area's case 2 declarations and rewrites every reference to them
in the three libraries, at the exact ranges recorded in the `.ilean` files (full names, names
relative to namespaces and `open`s, dot notation), and in comments and READMEs. No edit is made
at a span whose text does not spell the referenced constant, and a replacement name is written
only if it resolves to its target, and nothing else, from its position (namespaces, `open`s,
private names of the module, local binders); `rewrite` therefore needs current build outputs.

A declaration is *deferred* (left tidy, with its references unchanged) when its statement names
another tidy declaration, gets a tidy hypothesis from a `variable` command, or is written inside
a tidy namespace, and when a reference to it cannot be converted completely. A restated proof is
*translated* when every tidy declaration it names has a plain counterpart (a twin or a restated
lemma): those names are replaced in place. Otherwise it is *wrapped*: the old proof runs on tidy
hypotheses (`have h := h.tidy`) and its conclusion is converted (`refine .of_tidy ?_`);
statements that are not a bare predicate are transported with `simpa only [<plain ↔ tidy>]`. A
reference from a proof that stays tidy keeps its old type: the application becomes
`(lemma args).tidy`, with `.of_tidy` around tidy arguments; references to case 1 originals stay
there, and the plan counts them. `.of_tidy (x.tidy)` round trips are then removed.

With `--verify`, the three libraries are built strictly (`--wfail --iofail`) after the rewrite; a
translated proof that fails is wrapped instead and the build repeated. Failures that remain, such
as a tidy `fun_prop` that relied on a lemma the batch made plain, mark plain-calculus gaps: they
are reported, the status is `failed` and the exit code nonzero. `--diff` writes the plan as a
patch instead of rewriting files.

Declarations, statements and references come from `scripts/quality_report.py` and
`scripts/QualityReport.lean`, which read the build outputs of
`lake build Complexity ComplexityTests ComplexityAbstracts`.
"""

from __future__ import annotations

import argparse
import difflib
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import quality_report as qr  # noqa: E402
from proof_lengths import masks  # noqa: E402

ALLOWLIST = ROOT / "scripts/tidy_allowlist.txt"
TM = "Turing.MultiTapeTM."


@dataclass(frozen=True)
class Notion:
    """A tidy predicate with a same-bound plain counterpart and their equivalence."""
    tidy: str
    plain: str
    iff: str  # `plain ↔ tidy`

    @property
    def to_tidy(self) -> str:
        return self.plain + ".tidy"

    @property
    def of_tidy(self) -> str:
        return self.plain + ".of_tidy"

    @property
    def dot_of_tidy(self) -> str:
        """`Tidy.computable…`: `of_tidy` for dot notation on a tidy hypothesis."""
        last = self.plain.rsplit(".", 1)[1]
        return self.tidy + "." + last[0].lower() + last[1:]

    @property
    def bridges(self) -> set[str]:
        return {self.to_tidy, self.of_tidy, self.iff, self.dot_of_tidy}


NOTIONS = (
    Notion(TM + "ComputableTidilyInPolyTime", TM + "ComputableInPolyTime",
           TM + "computableInPolyTime_iff_computableTidilyInPolyTime"),
    Notion(TM + "ComputableTidilyInPolySpace", TM + "ComputableInPolySpace",
           TM + "computableInPolySpace_iff_computableTidilyInPolySpace"),
    Notion(TM + "ComputableTidilyInSpace", TM + "ComputableInSpace",
           TM + "computableInSpace_iff_computableTidilyInSpace"),
    Notion(TM + "ComputableTidilyInO", TM + "ComputableInO",
           TM + "computableInO_iff_computableTidilyInO"),
    Notion("Cslib.Complexity.ComputableTidilyInFPTTime", "Cslib.Complexity.ComputableInFPTTime",
           "Cslib.Complexity.computableInFPTTime_iff_computableTidilyInFPTTime"),
)
BY_TIDY = {n.tidy: n for n in NOTIONS}
BRIDGES = set().union(*(n.bridges for n in NOTIONS))
# `computableTidilyInPolyTime_foo` → `computableInPolyTime_foo`, for the supported notions only.
RENAME = re.compile(r"([cC])omputableTidily(In(?:PolyTime|PolySpace|Space|O|FPTTime))"
                    r"(?![A-Za-z0-9])")
# Name components that still say "tidy" after renaming mark a plain/tidy helper.
TIDY_WORD = re.compile(r"(?i)tid(?:y|ily)")


def plain_name(name: str) -> str:
    return RENAME.sub(r"\1omputable\2", name)


def is_tidy_constant(name: str) -> bool:
    """Mirror of `isTidy` in `scripts/QualityReport.lean`."""
    last = name.rsplit(".", 1)[-1]
    return last.startswith(("ComputableTidily", "ComputesTidily", "IsTidy"))


def load_allowlist(path: Path) -> set[str]:
    """Library source paths (relative to the repository root), one per line; `#` comments."""
    return {line.split("#", 1)[0].strip() for line in path.read_text().splitlines()} - {""}


def load_registry(path: Path | None) -> dict[str, str]:
    """original → plain twin, from a migration script's JSON: an array of
    `{"original": name, "plain": name, "module": module}` objects (`module` optional), or an
    object whose only key `"pairs"` holds that array. Malformed or ambiguous input is an error:
    a missing file, other keys, empty or blank names, an entry whose names agree, or two entries
    giving one original different twins."""
    if path is None:
        return {}
    if not path.is_file():
        raise ValueError(f"{path}: registry file not found")
    try:
        data = json.loads(path.read_text())
    except json.JSONDecodeError as error:
        raise ValueError(f"{path}: not JSON ({error})") from None
    if isinstance(data, dict):
        if set(data) != {"pairs"}:
            raise ValueError(f"{path}: expected an array of pairs or an object with exactly the "
                             f"key \"pairs\", found keys {sorted(data)}")
        data = data["pairs"]
    if not isinstance(data, list):
        raise ValueError(f"{path}: expected an array of pairs")
    registry: dict[str, str] = {}
    for i, row in enumerate(data):
        where = f"{path}: entry {i}"
        if not isinstance(row, dict):
            raise ValueError(f"{where}: expected an object, found {row!r}")
        if set(row) - {"original", "plain", "module"} or not {"original", "plain"} <= set(row):
            raise ValueError(f"{where}: expected the keys original, plain and optionally module, "
                             f"found {sorted(row)}")
        for key in row:
            value = row[key]
            if not isinstance(value, str) or not value or value != value.strip() \
                    or any(c.isspace() for c in value):
                raise ValueError(f"{where}: `{key}` must be a nonempty name, found {value!r}")
        original, plain = row["original"], row["plain"]
        if original == plain:
            raise ValueError(f"{where}: `{original}` is its own twin")
        if registry.get(original, plain) != plain:
            raise ValueError(f"{where}: `{original}` has two twins, `{registry[original]}` and "
                             f"`{plain}`")
        registry[original] = plain
    return registry


def discover_twins(constants: dict[str, dict]) -> dict[str, tuple[str, str]]:
    """The committed plain twins: for each public tidy theorem of the supported notions, the
    public theorem named by its plain rename whose statement mentions no tidy constant. The kind
    is `exact` when that statement is the syntactic plain transport and `by name` otherwise (for
    instance a broader canonical rule, which S1 checks)."""
    out = {}
    for name, const in constants.items():
        if const["k"] != "thm" or not const["e"] or not const.get("tidy") or name in BRIDGES:
            continue
        if any(t not in BY_TIDY for t in const["tidy"]):
            continue
        twin = plain_name(name)
        other = constants.get(twin)
        if twin != name and other and other["k"] == "thm" and other["e"] \
                and not other.get("tidy"):
            out[name] = (twin, "exact" if other.get("ph") == const.get("ph") else "by name")
    return out


def twin_map(constants: dict[str, dict], registry: dict[str, str]
             ) -> dict[str, tuple[str, str]]:
    """Discovered twins, overridden by explicit registry pairs."""
    twins = discover_twins(constants)
    for original, plain in registry.items():
        twins[original] = (plain, "registry")
    return twins


# --- Classification -----------------------------------------------------------------------------

@dataclass
class Entry:
    name: str
    module: str
    path: str  # relative to `Complexity/`
    area: str
    kind: str  # theorem, definition, structure field, constructor, instance
    case: str  # "1", "2", "3" or "unclassifiable"
    reason: str = ""
    target: str = ""  # the twin (case 1) or the new name (case 2)
    twin: str = ""  # case 1: `exact`, `by name` or `registry`
    notions: list[str] = field(default_factory=list)
    unsupported: list[str] = field(default_factory=list)
    body_only: bool = False  # mentions tidy only in its exposed body
    implicit: list[str] = field(default_factory=list)
    users: int = 0  # other modules that name it
    detail: str = ""
    collision: dict | None = None
    warnings: list[str] = field(default_factory=list)


def decl_kind(decl: dict) -> str:
    if decl["role"] == "member":
        return "constructor" if decl["kind"] == "ctor" else "structure field"
    if decl["keyword"] == "instance" or "instance" in decl["attrs"]:
        return "instance"
    if decl["kind"] == "thm":
        return "theorem"
    return "definition"


def classify_decl(decl: dict, const: dict, twins: dict[str, tuple[str, str]],
                  constants: dict[str, dict], private_names: dict[str, set[str]]) -> Entry:
    """The S2 case of one public declaration whose statement mentions a tidy constant."""
    name = decl["name"]
    tidy = sorted(set(const.get("tidy", [])) | set(const.get("tb", [])))
    entry = Entry(name=name, module=decl["module"], path=decl["path"], area=decl["area"],
                  kind=decl_kind(decl), case="unclassifiable",
                  notions=[t for t in tidy if t in BY_TIDY],
                  unsupported=[t for t in tidy if t not in BY_TIDY],
                  body_only=not const.get("tidy"), implicit=list(decl.get("implicit", [])),
                  users=len(decl.get("lib_refs", ())) + len(decl.get("test_refs", ()))
                  + len(decl.get("abstract_refs", ())))
    last = name.rsplit(".", 1)[-1]
    if "deprecated" in decl["attrs"]:
        entry.reason, entry.detail = "deprecated alias", "#588: delete, no aliases"
    elif is_tidy_constant(name) and entry.kind != "theorem":
        entry.reason = "tidy notion definition"
    elif name in BRIDGES or (entry.kind == "theorem" and TIDY_WORD.search(plain_name(last))):
        entry.reason, entry.detail = "bridge", "kept for proofs; S3 stores it internally"
    elif entry.unsupported:
        entry.reason = "unsupported notion"
        entry.detail = "no same-bound plain equivalence: " + ", ".join(
            f"`{t}`" for t in entry.unsupported)
    elif entry.kind != "theorem":
        entry.case = "3"
    elif name in twins:
        twin, kind = twins[name]
        entry.target, entry.twin = twin, kind
        if twin not in constants:
            entry.reason, entry.detail = "registered twin missing", f"`{twin}` is not built"
        elif constants[twin].get("tidy"):
            entry.reason, entry.detail = "registered twin missing", f"`{twin}` is tidy"
        else:
            entry.case = "1"
            if constants[twin].get("ph") != const.get("ph"):
                entry.warnings.append("the twin's statement is not the syntactic plain "
                                      "transport; proofs that use it are checked by the build")
    else:
        target = plain_name(name)
        entry.target = target
        taken = target in constants or target in private_names.get(decl["module"], set())
        if target != name and taken:
            existing = constants.get(target)
            entry.collision = {
                "target": target, "module": existing["m"] if existing else decl["module"],
                "private": existing is None or not existing["e"]}
            entry.reason = "collision"
            entry.detail = ("the target is private" if existing is None or not existing["e"]
                            else "the target is not a public plain theorem")
        else:
            entry.case = "2"
    return entry


def private_by_module(constants: dict[str, dict]) -> dict[str, set[str]]:
    """The user-facing names of private constants, by module."""
    out: dict[str, set[str]] = defaultdict(set)
    for name, const in constants.items():
        if name.startswith("_private."):
            rest = name.removeprefix("_private.").split(".0.", 1)
            if len(rest) == 2:
                out[const["m"]].add(rest[1])
    return out


def classify_all(model: "Model", twins: dict[str, tuple[str, str]]) -> list[Entry]:
    entries = []
    privates = private_by_module(model.constants)
    for name, decl in sorted(model.decls.items()):
        const = model.constants.get(name, {})
        if decl["role"] == "generated" or not (const.get("tidy") or const.get("tb")):
            continue
        if "Complexity/" + decl["path"] in model.allowlist:
            continue
        entries.append(classify_decl(decl, const, twins, model.constants, privates))
    targets = Counter(e.target for e in entries if e.case == "2" and e.target != e.name)
    for e in entries:
        if e.case == "2" and e.target != e.name and targets[e.target] > 1:
            e.case, e.reason = "unclassifiable", "collision"
            e.detail = "another declaration renames to the same target"
            e.collision = {"target": e.target, "module": e.module, "private": False}
    return entries


def registry_problems(registry: dict[str, str], constants: dict[str, dict]) -> list[str]:
    out = []
    for original, twin in sorted(registry.items()):
        if original not in constants:
            out.append(f"`{original}` is registered but not in the build")
        elif twin not in constants:
            out.append(f"twin `{twin}` of `{original}` is not in the build")
    return out


# --- Loading ------------------------------------------------------------------------------------

class Model:
    """Declarations, constants and references of the built libraries."""

    def __init__(self, build_dir: Path, allowlist: set[str]):
        pairs = ",".join(f"{n.tidy}={n.plain}" for n in NOTIONS)
        self.lib = qr.Library(build_dir, pairs)
        self.constants = self.lib.constants
        self.decls, self.owners, _ = qr.collect_declarations(self.lib)
        qr.annotate_headers(self.lib, self.decls)
        qr.collect_references(self.lib, self.decls, self.owners)
        qr.classify(self.decls)
        self.allowlist = allowlist
        self._users: dict[str, list[tuple[str, list]]] | None = None
        self._known: set[str] | None = None

    def users(self, name: str) -> list[tuple[str, list]]:
        """`(module, usage)` for every reference to `name` in the three libraries."""
        if self._users is None:
            self._users = defaultdict(list)
            for module in self.lib.ileans:
                for ref, _, info in self.lib.references(module):
                    for usage in info["usages"]:
                        self._users[ref].append((module, usage))
        return self._users.get(name, [])

    @property
    def known(self) -> set[str]:
        """Every constant name the build defines or references, for name resolution."""
        if self._known is None:
            self._known = set(self.constants)
            for module in self.lib.ileans:
                self._known.update(ref for ref, _, _ in self.lib.references(module))
        return self._known


# --- Report -------------------------------------------------------------------------------------

AREA_ORDER = [name for name, _, _ in qr.AREAS] + [qr.OTHER_AREA]


def summary(entries: list[Entry]) -> dict:
    by_area: dict[str, Counter] = defaultdict(Counter)
    reasons: Counter = Counter()
    for e in entries:
        by_area[e.area]["total"] += 1
        by_area[e.area][e.case] += 1
        if e.case == "unclassifiable":
            reasons[e.reason] += 1
    total = Counter()
    for counts in by_area.values():
        total.update(counts)
    return {"areas": {a: dict(by_area[a]) for a in AREA_ORDER if a in by_area},
            "total": dict(total), "unclassifiable_reasons": dict(reasons.most_common())}


def markdown_report(report: dict, limit: int = 40) -> str:
    s = report["summary"]
    dirty = " with uncommitted changes" if report["dirty"] else ""
    twins = ", ".join(f"{n} {k}" for k, n in sorted(report["twins"].items())) or "none"
    registry = (f" (`{report['registry']}`: {report['registry_size']} pairs)"
                if report["registry"] else "")
    out = [f"Revision `{report['revision']}`{dirty}; build outputs {report['outputs']}. "
           f"Allowlist: {report['allowlist_size']} modules. Plain twins of tidy theorems: "
           f"{twins}{registry}.", "",
           "### Public declarations whose statement mentions a tidy predicate", "",
           "| Area | Total | (1) Plain twin | (2) Rename and restate | "
           "(3) Definition or field | Unclassifiable |", "|---|--:|--:|--:|--:|--:|"]
    for area, c in list(s["areas"].items()) + [("Total", s["total"])]:
        out.append(f"| {area} | {c.get('total', 0):,} | {c.get('1', 0):,} | {c.get('2', 0):,} | "
                   f"{c.get('3', 0):,} | {c.get('unclassifiable', 0):,} |")
    out += ["", "Unclassifiable, by reason: " + "; ".join(
        f"{r} ({n})" for r, n in s["unclassifiable_reasons"].items()) + "."]
    collisions = [e for e in report["entries"] if e["collision"]]
    if collisions:
        out += ["", "### Collisions", "",
                "| Declaration | Target | Target module | Why |", "|---|---|---|---|"]
        for e in collisions[:limit]:
            c = e["collision"]
            out.append(f"| `{e['name']}` | `{c['target']}` | `{c['module']}` | {e['detail']} |")
        if len(collisions) > limit:
            out.append(f"| … {len(collisions) - limit} more in the JSON report | | | |")
    unsupported = Counter(t for e in report["entries"] for t in e["unsupported"])
    if unsupported:
        out += ["", "Tidy notions without a same-bound plain equivalence, by declarations "
                "mentioning them: " + ", ".join(f"`{t}` ({n})" for t, n in
                                                unsupported.most_common()) + "."]
    third = [e for e in report["entries"] if e["case"] == "3"]
    if third:
        out += ["", "### Case 3: definitions and structure fields", ""]
        out += [f"* `{e['name']}` ({e['kind']}, {e['area']})" for e in third[:limit]]
        if len(third) > limit:
            out.append(f"* … {len(third) - limit} more in the JSON report")
    if report["registry_problems"]:
        out += ["", "Registry problems: " + "; ".join(report["registry_problems"][:limit])]
    return "\n".join(out) + "\n"


# --- Lean source helpers (unit-tested in scripts/test_tidy_sweep.py) ----------------------------

OPENERS, CLOSERS = "([{⦃⟨‹", ")]}⦄⟩›"
IDENT = re.compile(qr.IDENT.pattern)
KEYWORDS = {"by", "fun", "λ", "with", "at", "using", "from", "then", "else", "do", "in", "if",
            "match", "show", "have", "let", "calc", "only", "generalizing", "says", "where",
            "deriving", "termination_by", "decreasing_by", "obtain", "rcases", "refine", "exact"}
COMMAND_KEYWORD = re.compile(r"#?[A-Za-z_]+")
NAME_ONLY_COMMANDS = {"#print", "#check", "#guard_msgs", "attribute", "open", "export", "#eval",
                      "#reduce", "#synth", "add_decl_doc", "#lint", "#help"}
LEMMA_LIST_TACTIC = re.compile(
    r"\b(?:simp|simp_all|dsimp|simp_rw|rw|rwa|rewrite|erw|nth_rewrite|nth_rw|simpa|fun_prop|"
    r"aesop|norm_num|field_simp|grind|polytime|positivity|unfold|delta|gcongr|subst_vars|"
    r"continuity|measurability|bound|decide|omega|linarith|nlinarith|exact\?|apply\?|"
    r"rw_mod_cast|push_cast|norm_cast|simp_arith|conv)\b[^\[\]\n]*$")


def match_bracket(mask: str, i: int, limit: int | None = None) -> int:
    """The index of the bracket closing the one at `mask[i]`, or -1."""
    depth, end = 0, len(mask) if limit is None else limit
    for j in range(i, end):
        char = mask[j]
        if char in OPENERS:
            depth += 1
        elif char in CLOSERS:
            depth -= 1
            if depth == 0:
                return j
    return -1


def find_top_level(mask: str, start: int, end: int, token: str) -> int:
    """The first `token` at bracket depth 0 in `mask[start:end]`, or -1. `:` excludes `:=`."""
    depth = 0
    for j in range(start, end):
        char = mask[j]
        if char in OPENERS:
            depth += 1
        elif char in CLOSERS:
            depth -= 1
        elif depth == 0 and mask.startswith(token, j):
            if token == ":" and (mask.startswith(":=", j) or mask.startswith("::", j)
                                 or (j and mask[j - 1] == ":")):
                continue
            return j
    return -1


def line_indent(text: str, offset: int) -> int:
    start = text.rfind("\n", 0, offset) + 1
    return len(text[start:]) - len(text[start:].lstrip(" "))


def column(text: str, offset: int) -> int:
    return offset - (text.rfind("\n", 0, offset) + 1)


def atom_end(mask: str, i: int, limit: int) -> int:
    """The end of the atom (identifier, number, `?_`, bracket group, `.ident`) at `i` together
    with directly attached projections (`.field`, `.1`), or `i` when no atom starts there."""
    if i >= limit:
        return i
    char = mask[i]
    if char in OPENERS:
        end = match_bracket(mask, i, limit)
        if end < 0:
            return i
        j = end + 1
    elif char == "." and i + 1 < limit and IDENT.match(mask, i + 1):
        j = IDENT.match(mask, i + 1).end()
    elif char == "?" and mask.startswith("?_", i):
        j = i + 2
    elif char == "@" and i + 1 < limit and IDENT.match(mask, i + 1):
        j = IDENT.match(mask, i + 1).end()
    elif char.isdigit():
        j = i
        while j < limit and (mask[j].isalnum() or mask[j] == "."):
            j += 1
    else:
        match = IDENT.match(mask, i)
        if not match or match[0].rstrip(".") in KEYWORDS:
            return i
        j = match.end()
    while j < limit and mask[j] == "." and j + 1 < limit and (
            mask[j + 1].isdigit() or IDENT.match(mask, j + 1)):
        j = IDENT.match(mask, j + 1).end() if IDENT.match(mask, j + 1) else j + 2
    return min(j, limit)


NAMED_ARG = re.compile(r"\(\s*[^\W\d][\w'₀-₉]*\s*:=")


def parse_args(mask: str, pos: int, limit: int, count: int, base_indent: int,
               named: list[tuple[int, int]] | None = None) -> list[tuple[int, int]]:
    """Up to `count` positional application arguments after `pos`: atoms separated by blanks,
    continuing onto lines indented more than `base_indent`. Named arguments `(x := e)` are
    skipped and, when `named` is given, appended to it."""
    args = []
    i = pos
    while len(args) < count and i < limit:
        j = i
        while j < limit and mask[j] in " \t":
            j += 1
        if j < limit and mask[j] == "\n":
            k = j
            while k < limit and mask[k] in " \t\n":
                k += 1
            if k >= limit or line_indent(mask, k) <= base_indent:
                break
            j = k
        if j == i and args:
            break  # no blank after the previous argument
        end = atom_end(mask, j, limit)
        if end == j:
            break
        if NAMED_ARG.match(mask, j):
            if named is not None:
                named.append((j, end))
        else:
            args.append((j, end))
        i = end
    return args


def strip_space(mask: str, start: int, end: int) -> tuple[int, int]:
    while start < end and mask[start].isspace():
        start += 1
    while end > start and mask[end - 1].isspace():
        end -= 1
    return start, end


def is_atomic_application(mask: str, start: int, end: int) -> tuple[int, int] | None:
    """For text `P args` in `mask[start:end]` made of atoms only, the span of `P`; else None."""
    start, end = strip_space(mask, start, end)
    head = atom_end(mask, start, end)
    if head == start:
        return None
    args = parse_args(mask, head, end, 10 ** 6, -1)
    last = args[-1][1] if args else head
    return (start, head) if strip_space(mask, last, end)[0] == end else None


@dataclass
class Binder:
    start: int
    end: int
    bracket: str
    names: list[str]
    type_start: int
    type_end: int
    default: bool


@dataclass
class DeclText:
    start: int
    sel_start: int
    sel_end: int
    end: int
    binders: list[Binder]
    colon: int  # the `:` before the type, or -1
    assign: int  # the `:=` before the body, or -1
    problems: list[str]


def parse_decl(mask: str, start: int, sel_start: int, sel_end: int, end: int) -> DeclText:
    """Binders, type and body of the declaration whose name ends at `sel_end`."""
    assign = find_top_level(mask, sel_end, end, ":=")
    stop = assign if assign >= 0 else end
    binders, problems, colon = [], [], -1
    i = sel_end
    if mask.startswith(".{", i):
        i = match_bracket(mask, i + 1, stop) + 1
    while i < stop:
        char = mask[i]
        if char.isspace():
            i += 1
        elif char in "([{⦃":
            close = match_bracket(mask, i, stop)
            if close < 0:
                problems.append("unbalanced binder")
                break
            inner = find_top_level(mask, i + 1, close, ":")
            default = find_top_level(mask, i + 1, close, ":=")
            if inner < 0:
                names, type_start = mask[i + 1:close].split(), close
            else:
                names, type_start = mask[i + 1:inner].split(), inner + 1
            type_end = default if default >= 0 else close
            binders.append(Binder(i, close + 1, char, names, type_start, type_end,
                                  default >= 0))
            i = close + 1
        elif char == ":":
            colon = i
            break
        else:
            problems.append("binder without brackets")
            break
    if assign < 0:
        problems.append("no `:=` (pattern-matching definition)")
    return DeclText(start, sel_start, sel_end, end, binders, colon, assign, problems)


def proof_parts(text: str, assign: int, end: int) -> tuple[str, bool]:
    """The text after `:=` and whether it is a tactic block."""
    body = text[assign + 2:end]
    return body, re.match(r"\s*by(?:\s|$)", body) is not None


def collapse(text: str) -> str:
    return " ".join(text.split())


# --- Scopes and names ---------------------------------------------------------------------------

SCOPE_COMMAND = re.compile(
    r"^(?P<mods>(?:@\[[^\]\n]*\]\s*)?(?:(?:public|private|noncomputable|protected|meta)\s+)*)"
    r"(?P<kw>namespace|section|end|open|mutual)\b(?P<rest>[^\n]*)", re.M)


def namespaces_of(names) -> set[str]:
    """Every name and every proper prefix of a name, as namespaces."""
    out = set()
    for name in names:
        parts = name.split(".")
        for i in range(1, len(parts) + 1):
            out.add(".".join(parts[:i]))
    return out


class Scopes:
    """The current namespace and opened namespaces at each offset of a masked source."""

    def __init__(self, mask: str, namespaces: set[str]):
        self.points: list[tuple[int, str, tuple[str, ...]]] = [(0, "", ())]
        self.once: list[tuple[int, int, tuple[str, ...]]] = []
        stack: list[tuple[str, str, list[str]]] = []
        starts = [m.start() for m in qr.COMMAND_START.finditer(mask)] + [len(mask)]
        for match in SCOPE_COMMAND.finditer(mask):
            kw, rest = match["kw"], match["rest"].split()
            namespace = ".".join(n for k, n, _ in stack if k == "namespace" and n)
            opens = [o for _, _, os in stack for o in os]
            if kw == "namespace" and rest:
                stack.append(("namespace", rest[0], []))
            elif kw in ("section", "mutual"):
                stack.append((kw, rest[0] if rest and kw == "section" else "", []))
            elif kw == "end":
                if stack:
                    stack.pop()
            elif kw == "open":
                one_shot = bool(rest) and rest[-1] == "in"
                words = [w for w in (rest[:-1] if one_shot else rest)
                         if w not in ("scoped", "hiding", "renaming", "→", "private")
                         and not w.startswith("(") and IDENT.fullmatch(w)]
                resolved = []
                for word in words:
                    prefixes = [".".join(namespace.split(".")[:i])
                                for i in range(len(namespace.split(".")), -1, -1)] if namespace \
                        else [""]
                    found = [p + "." + word if p else word for p in prefixes + opens + resolved
                             if (p + "." + word if p else word) in namespaces]
                    resolved += found or [word]
                if one_shot:
                    after = next((s for s in starts if s > match.end()), len(mask))
                    following = next((s for s in starts if s > after), len(mask))
                    self.once.append((match.start(), following, tuple(resolved)))
                    continue
                if not stack:
                    stack.append(("file", "", []))
                stack[-1][2].extend(resolved)
            namespace = ".".join(n for k, n, _ in stack if k == "namespace" and n)
            opens = [o for _, _, os in stack for o in os]
            self.points.append((match.end(), namespace, tuple(opens)))

    def at(self, offset: int) -> tuple[str, tuple[str, ...]]:
        namespace, opens = "", ()
        for point, ns, os in self.points:
            if point > offset:
                break
            namespace, opens = ns, os
        extra = tuple(o for start, end, os in self.once if start <= offset < end for o in os)
        return namespace, opens + extra

    def prefixes(self, offset: int) -> list[str]:
        """Namespaces a written name may be relative to, innermost first (`""` is the root)."""
        namespace, opens = self.at(offset)
        parts = namespace.split(".") if namespace else []
        return [".".join(parts[:i]) for i in range(len(parts), -1, -1)] + list(opens)


def written_name(target: str, prefixes: list[str], known: set[str]) -> str:
    """The shortest suffix of `target` that resolves to it, and to nothing else, from a position
    whose namespace prefixes and opened namespaces are `prefixes`."""
    parts = target.split(".")
    for k in range(1, len(parts) + 1):
        suffix = ".".join(parts[-k:])
        hits = {p + "." + suffix if p else suffix for p in prefixes}
        resolved = {h for h in hits if h in known or h == target}
        if resolved == {target}:
            return suffix
    return target


def renamed_token(token: str, old: str, new: str) -> str | None:
    """`token` (a written form of `old`) with the renamed part, when the written prefix still
    resolves the same way (`old = P.token` and `new = P.result`); otherwise None."""
    at = "@" if token.startswith("@") else ""
    bare = token[len(at):]
    root = "_root_." if bare.startswith("_root_.") else ""
    bare = bare[len(root):]
    if not (old == bare or old.endswith("." + bare)):
        return None
    prefix = old[:len(old) - len(bare)]
    if not new.startswith(prefix):
        return None
    result = new[len(prefix):]
    if not result or (prefix and result.startswith(".")):
        return None
    return at + root + result


# --- Edits --------------------------------------------------------------------------------------

@dataclass
class Replace:
    start: int
    end: int
    text: str


@dataclass
class Wrap:
    """Text inserted before `open` and after `close`; `site` orders wraps with equal spans (the
    wrap of the site that starts first is outermost)."""
    open: int
    close: int
    before: str
    after: str
    site: int


@dataclass
class Region:
    """A span whose edited text is then transformed by `build`."""
    start: int
    end: int
    build: object
    decl: str


def render(text: str, replaces: list[Replace], wraps: list[Wrap], lo: int, hi: int) -> str:
    """`text[lo:hi]` with the replacements and wraps inside it applied. At one position, wraps
    close (innermost first) before others open (outermost first), then a replacement starts."""
    reps = sorted((r for r in replaces if lo <= r.start and r.end <= hi),
                  key=lambda r: (r.start, r.end))
    ws = [w for w in wraps if lo <= w.open and w.close <= hi]
    points = sorted({r.start for r in reps} | {w.open for w in ws} | {w.close for w in ws})
    starting = defaultdict(list)
    for r in reps:
        starting[r.start].append(r)
    out, cur = [], lo
    for p in points:
        if p < cur:
            continue  # inside a replaced span
        out.append(text[cur:p])
        out += [w.after for w in sorted((w for w in ws if w.close == p),
                                        key=lambda w: (-w.open, -w.site))]
        out += [w.before for w in sorted((w for w in ws if w.open == p),
                                         key=lambda w: (-w.close, w.site))]
        cur = p
        for r in starting.get(p, []):
            out.append(r.text)
            cur = max(cur, r.end)
    out.append(text[cur:hi])
    return "".join(out)


def apply_edits(text: str, replaces: list[Replace], wraps: list[Wrap],
                regions: list[Region]) -> str:
    out, cur = [], 0
    for region in sorted(regions, key=lambda r: r.start):
        out.append(render(text, replaces, wraps, cur, region.start))
        out.append(region.build(render(text, replaces, wraps, region.start, region.end)))
        cur = region.end
    out.append(render(text, replaces, wraps, cur, len(text)))
    return "".join(out)


# --- Round trips --------------------------------------------------------------------------------

OF_TIDY = re.compile(r"(?<![\w.'])(?:(?:[\w.']*\.)?Computable(?:In(?:PolyTime|PolySpace|Space|O|"
                     r"FPTTime))\.|\.)of_tidy\b")
DOT_ROUND_TRIP = re.compile(r"\.tidy\.computableIn(?:PolyTime|PolySpace|Space|O|FPTTime)\b")


def cancel_round_trips(text: str) -> tuple[str, int]:
    """Remove `of_tidy (x.tidy)`, `of_tidy <| x.tidy` and `x.tidy.computableIn…` round trips,
    where `x` is an atom. Returns the new text and the number of removals."""
    count = 0
    while True:
        mask = masks(text)[1]
        change = None
        for match in DOT_ROUND_TRIP.finditer(mask):
            change = (match.start(), match.end(), "")
            break
        if change is None:
            for match in OF_TIDY.finditer(mask):
                i = match.end()
                while i < len(mask) and mask[i] in " \t":
                    i += 1
                pipe = mask.startswith("<|", i)
                if pipe:
                    i += 2
                    while i < len(mask) and mask[i] in " \t":
                        i += 1
                end = atom_end(mask, i, len(mask))
                if end == i:
                    continue
                inner = (i, end)
                if mask[i] == "(" and match_bracket(mask, i) == end - 1:
                    inner = strip_space(mask, i + 1, end - 1)
                start, stop = inner
                if not mask[start:stop].endswith(".tidy") or atom_end(mask, start, stop) != stop:
                    continue
                core_end = stop - len(".tidy")
                if atom_end(mask, start, core_end) != core_end:
                    continue
                if pipe:
                    after = end
                    while after < len(mask) and mask[after] in " \t":
                        after += 1
                    if after < len(mask) and mask[after] not in CLOSERS + "\n,":
                        continue
                change = (match.start(), end, text[start:core_end])
                break
        if change is None:
            return text, count
        start, end, new = change
        new_mask = masks(new)[1]
        if (start > 0 and text[start - 1] == "(" and end < len(text) and text[end] == ")"
                and atom_end(new_mask, 0, len(new)) == len(new) and not new.startswith("@")):
            start, end = start - 1, end + 1
        text = text[:start] + new + text[end:]
        count += 1


# --- Wrapping -----------------------------------------------------------------------------------

@dataclass
class Hyp:
    names: list[str]
    old_type: str  # one line
    simple: bool


def reindent(lines: list[str], delta: int) -> list[str] | None:
    """Shift lines by `delta` columns; None when that would remove non-blank text."""
    out = []
    for line in lines:
        if not line.strip():
            out.append("")
        elif delta >= 0:
            out.append(" " * delta + line)
        elif len(line) - len(line.lstrip(" ")) >= -delta:
            out.append(line[-delta:])
        else:
            return None
    return out


def wrap_proof(body: str, body_column: int, decl_indent: int, hyps: list[Hyp],
               conclusion: str | None, simple_conclusion: bool, iffs: str) -> str | None:
    """The new text after `:=` for a proof `body` of the old (tidy) statement, now stated plainly:
    tidy hypotheses are recovered, and the old conclusion converted. `body_column` is the column
    of the first character of `body`. None when the layout cannot be preserved."""
    stripped = body.lstrip()
    lead = body[:len(body) - len(stripped)]
    first_col = body_column + len(lead) if "\n" not in lead else len(lead.rsplit("\n", 1)[1])
    stripped = stripped.rstrip()
    tactic = re.match(r"by(?=\s|$)", stripped) is not None
    if not hyps and simple_conclusion and not tactic:
        return f"{lead}.of_tidy ({stripped})"
    k = decl_indent + 2
    rebind = []
    for hyp in hyps:
        for name in hyp.names:
            rebind.append(f"have {name} := {name}.tidy" if hyp.simple else
                          f"have {name} : {hyp.old_type} := by simpa only [{iffs}] using {name}")
    if tactic:
        rest = stripped[2:]
        if rest.lstrip(" \t").startswith("\n") or not rest.strip():
            lines = rest.lstrip(" \t")[1:].split("\n")
            nonblank = [ln for ln in lines if ln.strip()]
            if not nonblank:
                return None
            k = min(len(ln) - len(ln.lstrip(" ")) for ln in nonblank)
        else:
            first_line, _, tail = rest.lstrip(" \t").partition("\n")
            tactic_col = first_col + 2 + (len(rest) - len(rest.lstrip(" \t")))
            shifted = reindent(tail.split("\n"), k - tactic_col) if tail else []
            if shifted is None:
                return None
            lines = [" " * k + first_line] + shifted
        pad = " " * k
        out = [pad + line for line in rebind]
        if conclusion is None:
            out += lines
        elif simple_conclusion:
            out += [pad + "refine .of_tidy ?_"] + lines
        else:
            inner = reindent(lines, 2)
            out += [pad + f"have this : {conclusion} := by"] + inner + \
                [pad + f"simpa only [{iffs}] using this"]
        return " by\n" + "\n".join(out)
    first, _, tail = stripped.partition("\n")
    tail_lines = tail.split("\n") if tail else []
    nonblank = [ln for ln in tail_lines if ln.strip()]
    shift = 0
    if nonblank:
        least = min(len(ln) - len(ln.lstrip(" ")) for ln in nonblank)
        shift = max(0, k + 2 - least)
    tail_lines = reindent(tail_lines, shift) or tail_lines
    pad = " " * k
    out = [pad + line for line in rebind]
    term = "\n".join([first] + tail_lines)
    if conclusion is None:
        out.append(pad + "exact " + term)
    elif simple_conclusion:
        out.append(pad + "exact .of_tidy (" + term + ")")
    else:
        out += [pad + f"have this : {conclusion} :=", pad + "  " + term,
                pad + f"simpa only [{iffs}] using this"]
    return " by\n" + "\n".join(out)


# --- Planning -----------------------------------------------------------------------------------

@dataclass
class Manual:
    path: str
    line: int
    decl: str
    kind: str
    detail: str = ""


@dataclass
class Ref:
    name: str
    start: int
    end: int
    decl: str | None


class SourceFile:
    def __init__(self, path: Path, namespaces: set[str]):
        self.path = path
        self.text = path.read_text(encoding="utf-8")
        self.code, self.mask = masks(self.text) if path.suffix == ".lean" else (self.text,) * 2
        self.lines = self.text.split("\n")
        self.starts = [0]
        for line in self.lines:
            self.starts.append(self.starts[-1] + len(line) + 1)
        self.commands = [m.start() for m in qr.COMMAND_START.finditer(self.mask)]
        self._namespaces = namespaces
        self._scopes: Scopes | None = None

    @property
    def scopes(self) -> Scopes:
        if self._scopes is None:
            self._scopes = Scopes(self.mask, self._namespaces)
        return self._scopes

    def at(self, line: int, column16: int) -> int:
        """The offset of a 0-based line and UTF-16 column (`.ilean` positions)."""
        return self.starts[line] + qr.utf16_index(self.lines[line], column16)

    def at_range(self, line: int, column: int) -> int:
        """The offset of a 1-based line and code-point column (declaration ranges)."""
        return self.starts[line - 1] + column

    def line_of(self, offset: int) -> int:
        """The 1-based line of an offset."""
        return self.text.count("\n", 0, offset) + 1

    def command_keyword(self, offset: int) -> str:
        starts = [s for s in self.commands if s <= offset]
        if not starts:
            return ""
        match = COMMAND_KEYWORD.match(self.mask, starts[-1])
        return match[0] if match else ""

    def comment_spans(self) -> list[tuple[int, int]]:
        if self.path.suffix != ".lean":
            return [(0, len(self.text))]
        spans, i = [], 0
        while i < len(self.text):
            if self.code[i] != self.text[i]:
                j = i
                while j < len(self.text) and self.code[j] != self.text[j] or (
                        j < len(self.text) and self.text[j] == "\n" and j + 1 < len(self.text)
                        and self.code[j + 1] != self.text[j + 1]):
                    j += 1
                spans.append((i, j))
                i = j
            else:
                i += 1
        return spans


@dataclass
class FileEdits:
    replaces: list[Replace] = field(default_factory=list)
    wraps: list[Wrap] = field(default_factory=list)
    regions: list[Region] = field(default_factory=list)


class Planner:
    """The edits of one area's batch: case 2 declarations restated and renamed, the references
    to them converted, and case 1 twins used in proofs that become plain.

    No edit is made at a span whose text does not spell the referenced constant, and a
    replacement is written only when it resolves to its intended target, and nothing else, from
    its position. A declaration with a reference that cannot be converted completely is deferred
    (left tidy), so that skipped references stay unchanged."""

    def __init__(self, model: Model, entries: list[Entry], twins: dict[str, str], area: str,
                 force_wrap: frozenset[str] = frozenset()):
        self.model, self.area, self.force_wrap = model, area, force_wrap
        self.entries = {e.name: e for e in entries}
        self.batch = {e.name: e for e in entries if e.area == area and e.case == "2"}
        self.twins = {o: p for o, p in twins.items() if p in model.constants}
        self.privates = private_by_module(model.constants)
        self.known = model.known | {e.target for e in self.batch.values()}
        self.namespaces = namespaces_of(self.known)
        self.sources: dict[Path, SourceFile] = {}
        self.deferred: dict[str, list[str]] = {}
        self._refs: dict[str, list[Ref]] = {}
        self._locals: dict[tuple[str, int, int], set[str]] = {}
        self.reset()

    def reset(self) -> None:
        """Forget the edits of a planning pass."""
        self.renames = {n: e.target for n, e in self.batch.items() if n not in self.deferred}
        self.files: dict[Path, FileEdits] = defaultdict(FileEdits)
        self.manual: list[Manual] = []
        self.decls: dict[str, dict] = {}
        self.spans: dict[str, list[tuple[int, int, str]]] = defaultdict(list)
        self.needs: dict[str, dict[str, bool]] = defaultdict(dict)
        self.sites: Counter = Counter()
        self.twin_refs: Counter = Counter()
        self.imports: list[tuple[str, str, bool]] = []
        self.blockers: dict[str, list[str]] = defaultdict(list)
        self.round_trips = 0

    # Sources and references.

    def source(self, path: Path) -> SourceFile:
        if path not in self.sources:
            self.sources[path] = SourceFile(path, self.namespaces)
        return self.sources[path]

    def refs(self, module: str) -> list[Ref]:
        if module not in self._refs:
            src = self.source(qr.source_path(module))
            out = []
            for name, _, info in self.model.lib.references(module):
                for u in info["usages"]:
                    out.append(Ref(name, src.at(u[0], u[1]), src.at(u[2], u[3]),
                                   u[4] if len(u) == 5 else None))
            self._refs[module] = sorted(out, key=lambda x: x.start)
        return self._refs[module]

    def ref_kind(self, name: str) -> str:
        owner = qr.owner_of(name, self.model.owners) or name
        if name in BY_TIDY:
            return "pred"
        if owner in self.renames:
            return "renamed"
        if name in self.twins:
            return "twin"
        if name in BRIDGES:
            return "bridge"
        const = self.model.constants.get(name, {})
        if const.get("tidy") or const.get("tb") or is_tidy_constant(name):
            return "tidy"
        return "plain"

    def new_name(self, name: str) -> str:
        if name in BY_TIDY:
            return BY_TIDY[name].plain
        owner = qr.owner_of(name, self.model.owners) or name
        if owner in self.renames and (name == owner or name.startswith(owner + ".")):
            return self.renames[owner] + name[len(owner):]
        return self.twins.get(name, name)

    def note(self, path: Path, offset: int, decl: str | None, kind: str, detail: str = ""):
        src = self.source(path)
        self.manual.append(Manual(str(path.relative_to(ROOT)), src.line_of(offset), decl or "",
                                  kind, detail))

    def where(self, path: Path, offset: int) -> str:
        return f"{path.relative_to(ROOT)}:{self.source(path).line_of(offset)}"

    def need(self, module: str, constant: str, public: bool) -> None:
        defining = self.model.constants.get(constant, {}).get("m")
        if defining and defining != module:
            self.needs[module][defining] = self.needs[module].get(defining, False) or public

    def notions_of(self, name: str) -> list[Notion]:
        const = self.model.constants.get(name, {})
        return [BY_TIDY[t] for t in const.get("tidy", []) if t in BY_TIDY]

    # Names.

    def local_names(self, module: str, src: SourceFile, offset: int) -> set[str]:
        """Identifiers of the declaration (or command) around `offset` that are not references
        to constants: binders, local hypotheses, tactic names. A written name whose first
        component is one of them could be captured by a local."""
        ranges = self.model.lib.ileans.get(module, {}).get("decls", {}).values()
        span = next(((src.at(r[0], r[1]), src.at(r[2], r[3])) for r in ranges
                     if src.at(r[0], r[1]) <= offset < src.at(r[2], r[3])), None)
        if span is None:
            starts = src.commands + [len(src.mask)]
            start = max([s for s in starts if s <= offset], default=0)
            span = (start, min(s for s in starts if s > offset) if offset < len(src.mask)
                    else len(src.mask))
        key = (module, *span)
        if key not in self._locals:
            refs = [(x.start, x.end) for x in self.refs(module)
                    if span[0] <= x.start < span[1]]
            names = set()
            for match in IDENT.finditer(src.mask, *span):
                if not any(a <= match.start() < b for a, b in refs):
                    names.add(match[0].split(".")[0])
            self._locals[key] = names - KEYWORDS
        return self._locals[key]

    def resolves(self, module: str, src: SourceFile, offset: int, written: str) -> set[str]:
        """What `written` (without `@`) can denote at `offset`: constants reached through the
        enclosing namespaces and the opened namespaces, private constants of the module, and a
        local of the same name (as `"<local>"`)."""
        names = self.known | self.privates.get(module, set())
        if written.startswith("_root_."):
            return {written[len("_root_."):]} & names
        hits = {p + "." + written if p else written for p in src.scopes.prefixes(offset)}
        out = hits & names
        if written.split(".")[0] in self.local_names(module, src, offset):
            out.add("<local>")
        return out

    def written(self, module: str, src: SourceFile, start: int, end: int, old: str, new: str
                ) -> tuple[str | None, str]:
        """The text replacing the reference to `old` at `[start, end)` by one to `new`, or None
        and the reason it cannot be written."""
        token = src.text[start:end]
        if not spells(token, old):
            return None, f"the reference span `{token}` does not spell `{old}`"
        if old == new:
            return token, ""
        leading = token.startswith(".")
        if leading or (start and src.text[start - 1] == "."):  # leading-dot or field notation
            last = new.rsplit(".", 1)[-1]
            if old.rsplit(".", 1)[-1] == last:
                return token, ""
            if namespace_of(old) == namespace_of(new) and "." not in token.lstrip("."):
                return ("." if leading else "") + last, ""
            return None, "dot notation on a declaration whose namespace changes"
        at = "@" if token.startswith("@") else ""
        candidates = [renamed_token(token.removeprefix("@"), old, new)]
        parts = new.split(".")
        candidates += [".".join(parts[-k:]) for k in range(1, len(parts) + 1)]
        candidates.append("_root_." + new)
        for candidate in candidates:
            if candidate and self.resolves(module, src, start, candidate) == {new}:
                return at + candidate, ""
        return None, f"no written form of `{new}` resolves to it here"

    # Declarations.

    def plan(self) -> "Planner":
        analyses = {name: self.analyse_decl(self.batch[name]) for name in sorted(self.batch)}
        for name, a in analyses.items():
            if a is None:
                self.deferred[name] = ["declaration range missing"]
            elif a["defer"]:
                self.deferred[name] = list(a["defer"])
        while True:
            self.defer_statements(analyses)
            self.reset()
            for name in sorted(self.renames):
                self.plan_decl(self.batch[name], analyses[name])
            for name in sorted(self.renames):
                self.plan_clients(name)
            if not self.blockers:
                break
            for name, reasons in self.blockers.items():
                self.deferred[name] = sorted(set(reasons))
        for name in sorted(self.deferred):
            self.defer(name, analyses.get(name))
        self.plan_comments()
        self.plan_imports()
        return self

    def defer_statements(self, analyses: dict) -> None:
        """Defer, to a fixed point, the declarations whose statements name deferred ones."""
        changed = True
        while changed:
            changed = False
            for name, a in analyses.items():
                if name in self.deferred or a is None:
                    continue
                reasons = [f"statement names deferred `{x.name}`" for x in a["sig_refs"]
                           if (qr.owner_of(x.name, self.model.owners) or x.name)
                           in self.deferred]
                if reasons:
                    self.deferred[name] = reasons
                    changed = True

    def analyse_decl(self, entry: Entry) -> dict | None:
        """Parse a declaration and find what prevents restating it."""
        decl = self.model.decls[entry.name]
        module, path = decl["module"], qr.source_path(decl["module"])
        if not decl["range"]:
            return None
        src = self.source(path)
        r = decl["range"]
        start, end = src.at_range(r[0], r[1]), src.at_range(r[2], r[3])
        sel_start, sel_end = src.at_range(r[4], r[5]), src.at_range(r[6], r[7])
        dt = parse_decl(src.mask, start, sel_start, sel_end, end)
        refs = [x for x in self.refs(module) if start <= x.start < end]
        split = dt.assign if dt.assign >= 0 else end
        a = {"module": module, "path": path, "src": src, "dt": dt, "start": start, "end": end,
             "sig_refs": [x for x in refs if x.start < split],
             "proof_refs": [x for x in refs if x.start >= split], "defer": []}
        token = src.text[sel_start:sel_end]
        if not spells(token, entry.name):
            a["defer"].append(f"the declaration range `{token}` does not spell its name")
        elif entry.target != entry.name and renamed_token(token, entry.name,
                                                          entry.target) is None:
            a["defer"].append("name written inside a tidy namespace")
        for x in a["sig_refs"]:
            if self.ref_kind(x.name) in ("bridge", "tidy"):
                a["defer"].append(f"statement names tidy `{x.name}`")
        written = sum(1 for x in a["sig_refs"] if x.name in BY_TIDY)
        if not written or self.hidden_tidy(entry.name, src, dt, a["sig_refs"]):
            a["defer"].append("tidy predicate from a `variable` command or notation")
        return a

    def defer(self, name: str, a: dict | None) -> None:
        """A declaration left tidy in this batch; references to it stay unchanged."""
        decl = self.model.decls[name]
        path = qr.source_path(decl["module"])
        self.decls[name] = {"name": name, "target": self.batch[name].target,
                            "path": str(path.relative_to(ROOT)),
                            "line": decl["range"][0] if decl["range"] else 0,
                            "mode": "deferred", "blocking": [], "issues": self.deferred[name]}
        for reason in self.deferred[name]:
            self.note(path, a["start"] if a else 0, name, "deferred", reason)

    def plan_decl(self, entry: Entry, a: dict) -> None:
        module, path, src, dt = a["module"], a["path"], a["src"], a["dt"]
        start, end, sig_refs, proof_refs = a["start"], a["end"], a["sig_refs"], a["proof_refs"]
        info = {"name": entry.name, "target": entry.target, "path": str(path.relative_to(ROOT)),
                "line": src.line_of(start), "mode": "manual", "blocking": [], "issues": []}
        self.decls[entry.name] = info
        self.spans[module].append((start, end, entry.name))
        replaces: list[Replace] = []
        if entry.target != entry.name:
            token = src.text[dt.sel_start:dt.sel_end]
            replaces.append(Replace(dt.sel_start, dt.sel_end,
                                    renamed_token(token, entry.name, entry.target)))
        for x in sig_refs:
            if self.ref_kind(x.name) in ("pred", "renamed", "twin"):
                new, why = self.written(module, src, x.start, x.end, x.name,
                                        self.new_name(x.name))
                if new is None:
                    self.blockers[entry.name].append(
                        f"{self.where(path, x.start)}: statement reference: {why}")
                    return
                replaces.append(Replace(x.start, x.end, new))
        doc = src.text[start:dt.sel_start]
        if TIDY_WORD.search(doc.split("-/")[0] if "/--" in doc else ""):
            info["issues"].append("docstring mentions tidiness (review wording)")
            self.note(path, start, entry.name, "docstring mentions tidiness (review wording)")
        info["blocking"] = sorted({x.name for x in proof_refs
                                   if self.ref_kind(x.name) in ("bridge", "tidy")
                                   and x.name != entry.name})
        translation = []
        if not info["blocking"] and entry.name not in self.force_wrap and dt.assign >= 0:
            for x in proof_refs:
                if self.ref_kind(x.name) in ("pred", "renamed", "twin"):
                    new, _ = self.written(module, src, x.start, x.end, x.name,
                                          self.new_name(x.name))
                    if new is None:
                        translation = None
                        break
                    translation.append((x, new))
        wrap, problems = self.wrap_plan(entry, src, dt, sig_refs)
        if translation is not None and not info["blocking"] \
                and entry.name not in self.force_wrap and dt.assign >= 0:
            info["mode"] = "translate"
        elif wrap is not None:
            info["mode"] = "wrap"
        else:
            self.blockers[entry.name].append(
                f"{self.where(path, start)}: cannot wrap the proof: " + "; ".join(problems))
            return
        fe = self.files[path]
        fe.replaces += replaces
        for x in sig_refs:
            if self.ref_kind(x.name) in ("pred", "renamed", "twin"):
                self.need(module, self.new_name(x.name), True)
        if info["mode"] == "translate":
            for x, new in translation:
                if new != src.text[x.start:x.end]:
                    fe.replaces.append(Replace(x.start, x.end, new))
                if self.ref_kind(x.name) == "twin":
                    self.twin_refs["redirected"] += 1
                    self.need(module, self.new_name(x.name), False)
            return
        for x in proof_refs:
            kind = self.ref_kind(x.name)
            if kind == "twin":
                self.twin_refs["kept on the original"] += 1
            elif kind == "renamed" and x.name != entry.name:
                if x.name in self.renames:
                    self.convert(path, module, x.start, x.end, x.name, entry.name, "tidy")
                else:
                    self.blockers[entry.name].append(
                        f"{self.where(path, x.start)}: names generated constant `{x.name}`")
        fe.regions.append(Region(dt.assign + 2, end, wrap, entry.name))
        for notion in self.notions_of(entry.name):
            self.need(module, notion.of_tidy, False)
            self.need(module, notion.iff, False)

    def hidden_tidy(self, name: str, src: SourceFile, dt: DeclText, sig_refs: list[Ref]) -> bool:
        """Whether the statement has more tidy binders or conclusions than are written."""
        sg = self.model.constants.get(name, {}).get("sg")
        if not sg:
            return False
        lean = sum(1 for _, flag in sg[0] if flag) + (sg[1] != 0)
        written = 0
        for b in dt.binders:
            if any(b.type_start <= x.start < b.type_end and x.name in BY_TIDY for x in sig_refs):
                written += max(1, len(b.names))
        if dt.colon >= 0:
            written += sum(1 for x in sig_refs if x.start > dt.colon and x.name in BY_TIDY)
        return lean > written

    def wrap_plan(self, entry: Entry, src: SourceFile, dt: DeclText, sig_refs: list[Ref]):
        """The proof transformation of a wrapped declaration, or None and the problems."""
        problems = [p for p in dt.problems]
        preds = [x for x in sig_refs if x.name in BY_TIDY]
        hyps = []
        for b in dt.binders:
            inside = [x for x in preds if b.type_start <= x.start < b.type_end]
            if not inside:
                continue
            if b.bracket == "[" or not b.names or "_" in b.names:
                problems.append("unnamed or instance tidy hypothesis")
            if b.default:
                problems.append("tidy hypothesis with a default value")
            if src.mask[b.type_start:b.type_end] != src.text[b.type_start:b.type_end]:
                problems.append("comment inside a tidy hypothesis")
            head = is_atomic_application(src.mask, b.type_start, b.type_end)
            simple = head is not None and any(x.start == head[0] for x in inside)
            hyps.append(Hyp(b.names, collapse(src.text[b.type_start:b.type_end]), simple))
        conclusion, simple = None, False
        if dt.colon >= 0 and dt.assign >= 0:
            inside = [x for x in preds if x.start > dt.colon]
            if inside:
                conclusion = collapse(src.text[dt.colon + 1:dt.assign])
                head = is_atomic_application(src.mask, dt.colon + 1, dt.assign)
                simple = head is not None and any(x.start == head[0] for x in inside)
                if src.mask[dt.colon + 1:dt.assign] != src.text[dt.colon + 1:dt.assign]:
                    problems.append("comment inside the statement")
        if dt.assign >= 0 and re.search(r"(?m)^\s*(?:termination_by|decreasing_by|where)\b",
                                        src.mask[dt.assign:dt.end]):
            problems.append("termination or `where` clauses")
        if self.hidden_tidy(entry.name, src, dt, sig_refs):
            problems.append("tidy hypothesis from a `variable` command or notation")
        if problems:
            return None, problems
        prefixes = src.scopes.prefixes(dt.start)
        iffs = ", ".join(written_name(n.iff, prefixes, self.known)
                         for n in self.notions_of(entry.name))
        body_column = column(src.text, dt.assign + 2)
        indent = line_indent(src.text, dt.sel_start)
        args = (body_column, indent, hyps, conclusion, simple, iffs)
        if wrap_proof(src.text[dt.assign + 2:dt.end], *args) is None:
            return None, ["proof layout"]
        return (lambda body: wrap_proof(body, *args)), []

    # Clients.

    def in_batch_decl(self, module: str, offset: int) -> str | None:
        for start, end, name in self.spans.get(module, ()):
            if start <= offset < end:
                return name
        return None

    def plan_clients(self, name: str) -> None:
        for module, u in self.model.users(name):
            path = qr.source_path(module)
            src = self.source(path)
            start, end = src.at(u[0], u[1]), src.at(u[2], u[3])
            if self.in_batch_decl(module, start):
                continue
            context = "name" if src.command_keyword(start) in NAME_ONLY_COMMANDS else "tidy"
            self.convert(path, module, start, end, name, u[4] if len(u) == 5 else None, context)

    def convert(self, path: Path, module: str, start: int, end: int, old: str,
                decl: str | None, context: str) -> bool:
        """Rename a reference to a restated declaration; in a proof that stays tidy, keep the
        site's old type with `.tidy` around the application and `.of_tidy` around tidy
        arguments. The edits are made only when the whole conversion is supported; otherwise
        `old` is blocked (and will be deferred), and the site stays unchanged."""
        src = self.source(path)
        new = self.renames[old]
        written, why = self.written(module, src, start, end, old, new)
        wraps: list[Wrap] = []
        if written is not None and context == "tidy":
            why, wraps = self.convert_site(src, start, end, old)
        if written is None or why:
            self.blockers[old].append(f"{self.where(path, start)}: {why}")
            return False
        fe = self.files[path]
        if written != src.text[start:end]:
            fe.replaces.append(Replace(start, end, written))
        fe.wraps += wraps
        self.sites[context] += 1
        if wraps:
            for notion in self.notions_of(old):
                self.need(module, notion.of_tidy, False)
        return True

    def convert_site(self, src: SourceFile, start: int, end: int, old: str
                     ) -> tuple[str, list[Wrap]]:
        """The wraps that keep the old type of the application of `old` at `start`, or the
        reason it cannot be converted (and no wraps)."""
        sg = self.model.constants.get(old, {}).get("sg")
        if not sg:
            return "", []
        binders, conclusion = sg
        mask = src.mask
        opener = enclosing_opener(mask, start)
        if opener >= 0 and mask[opener] == "[" and LEMMA_LIST_TACTIC.search(
                mask[mask.rfind("\n", 0, opener) + 1:opener]):
            return "used in a tactic lemma list", []
        explicit_all = src.text[start:end].startswith("@") or (start and mask[start - 1] == "@")
        site_start = start - 1 if start and mask[start - 1] == "@" else start
        positions = [i for i, (bi, _) in enumerate(binders) if explicit_all or bi == 0]
        if not explicit_all and any(flag and bi != 0 for bi, flag in binders):
            return "implicit tidy hypothesis", []
        if conclusion == 2:
            return "conclusion is not a bare tidy predicate", []
        if src.text[start:end].startswith("."):
            if conclusion:  # the expected type changes with the conclusion
                return "leading-dot notation", []
        elif start and mask[start - 1] == ".":
            before = mask[start - 2] if start >= 2 else " "
            if before.isspace() or before in OPENERS or before in "<|$,":
                return "leading-dot notation", []
            site_start = receiver_start(mask, start - 1)
            if not positions or binders[positions[0]][1]:
                return "dot notation on a tidy receiver", []
            positions = positions[1:]
        named: list[tuple[int, int]] = []
        args = parse_args(mask, end, len(mask), len(positions), line_indent(mask, start), named)
        if len(args) < len(positions):
            return (f"partial application ({len(args)} of {len(positions)} explicit "
                    "arguments)"), []
        wraps = []
        for (a, b), i in zip(args, positions):
            if binders[i][1] == 2:
                return "tidy hypothesis under binders", []
            if binders[i][1] == 1:
                wraps.append(Wrap(a, b, "(.of_tidy ", ")", start))
        site_end = max([end] + [b for _, b in args + named])
        if conclusion == 1:
            left = site_start - 1
            while left >= 0 and mask[left] in " \t\n":
                left -= 1
            right = site_end
            while right < len(mask) and mask[right] in " \t\n":
                right += 1
            if left >= 0 and mask[left] == "(" and match_bracket(mask, left) == right:
                wraps.append(Wrap(left, right + 1, "", ".tidy", site_start))
            elif not args and site_start == start and IDENT.fullmatch(src.text[start:end]):
                wraps.append(Wrap(start, end, "", ".tidy", site_start))
            else:
                wraps.append(Wrap(site_start, site_end, "(", ").tidy", site_start))
        return "", wraps

    # Documentation.

    def plan_comments(self) -> None:
        renamed = {old: new for old, new in self.renames.items() if old != new}
        if not renamed:
            return
        by_last: dict[str, list[str]] = defaultdict(list)
        for old in renamed:
            by_last[old.rsplit(".", 1)[-1]].append(old)
        full = re.compile(r"(?<![\w.])(" + "|".join(
            re.escape(n) for n in sorted(renamed, key=len, reverse=True)) + r")(?![\w'])")
        lasts = re.compile("|".join(re.escape(last) for last in by_last))
        known_by_last: dict[str, list[str]] = defaultdict(list)
        for name in self.known:
            if name.rsplit(".", 1)[-1] in by_last:
                known_by_last[name.rsplit(".", 1)[-1]].append(name)
        paths = [qr.source_path(m) for m in self.model.lib.ileans] + \
            [ROOT / doc for doc in qr.EXTERNAL_DOCS]
        for path in paths:
            if not path.exists() or not lasts.search(path.read_text(encoding="utf-8")):
                continue
            src, fe = self.source(path), self.files[path]
            taken = {(r.start, r.end) for r in fe.replaces}
            for lo, hi in src.comment_spans():
                done = []
                for m in re.finditer(r"`([^`\s]+)`", src.text[lo:hi]):
                    token = m[1].lstrip("@.")
                    a = lo + m.start(1) + (len(m[1]) - len(token))
                    old = self.resolve_doc_token(src, a, token, known_by_last)
                    if old in renamed:
                        new = renamed_token(token, old, renamed[old])
                        if new and (a, a + len(token)) not in taken:
                            fe.replaces.append(Replace(a, a + len(token), new))
                            done.append((a, a + len(token)))
                for m in full.finditer(src.text, lo, hi):
                    if not any(s <= m.start() < e for s, e in done):
                        fe.replaces.append(Replace(m.start(), m.end(), renamed[m[1]]))

    def resolve_doc_token(self, src: SourceFile, offset: int, token: str,
                          known_by_last: dict[str, list[str]]) -> str | None:
        """The constant a documentation token names: the only one it is a suffix of, or the one
        it resolves to from the comment's namespace and opened namespaces."""
        candidates = [n for n in known_by_last.get(token.rsplit(".", 1)[-1], ())
                      if qr.matches(n, token)]
        if len(candidates) <= 1:
            return candidates[0] if candidates else None
        if src.path.suffix != ".lean":
            return None
        for prefix in src.scopes.prefixes(offset):
            full = prefix + "." + token if prefix else token
            if full in candidates:
                return full
        return None

    # Imports.

    def plan_imports(self) -> None:
        ileans = self.model.lib.ileans
        reexports: dict[str, set[str]] = {}

        def closure(module: str) -> set[str]:
            if module not in reexports:
                reexports[module] = {module}
                for dep, private, *_ in ileans.get(module, {}).get("directImports", []):
                    if not private:
                        reexports[module] |= closure(dep)
            return reexports[module]

        def imports_of(module: str) -> set[str]:
            seen, stack = set(), [module]
            while stack:
                for dep, *_ in ileans.get(stack.pop(), {}).get("directImports", []):
                    if dep not in seen:
                        seen.add(dep)
                        stack.append(dep)
            return seen

        for module, needed in sorted(self.needs.items()):
            direct = ileans.get(module, {}).get("directImports", [])
            public = {module}.union(*(closure(d) for d, private, *_ in direct if not private))
            available = public.union(*(closure(d) for d, *_ in direct))
            path = qr.source_path(module)
            src = self.source(path)
            is_module = re.search(r"(?m)^module\s*$", src.mask) is not None
            for dep, want_public in sorted(needed.items()):
                if dep in (public if want_public and is_module else available):
                    continue
                if module in imports_of(dep):
                    self.note(path, 0, None, "import cycle", f"needs `{dep}`")
                    continue
                self.imports.append((module, dep, want_public and is_module))
                header = list(re.finditer(r"(?m)^(public\s+)?(?:meta\s+)?import\s+\S+[^\n]*\n",
                                          src.mask))
                kind = [h for h in header if bool(h[1]) == (want_public and is_module)]
                at = (kind or header)[-1].end() if header else 0
                if want_public and is_module and not kind and header:
                    at = header[0].start()
                prefix = "public import " if want_public and is_module else "import "
                self.files[path].replaces.append(Replace(at, at, prefix + dep + "\n"))

    # Output.

    def render(self) -> dict[Path, str]:
        out = {}
        for path, fe in self.files.items():
            if not (fe.replaces or fe.wraps or fe.regions):
                continue
            src = self.source(path)
            text = apply_edits(src.text, fe.replaces, fe.wraps, fe.regions)
            text, removed = cancel_round_trips(text) if path.suffix == ".lean" else (text, 0)
            self.round_trips += removed
            if text != src.text:
                out[path] = text
        return out

    def summary(self) -> dict:
        modes = Counter(d["mode"] for d in self.decls.values())
        kinds = Counter(m.kind for m in self.manual)
        return {"area": self.area, "declarations": len(self.batch), "modes": dict(modes),
                "manual": dict(kinds.most_common()), "sites": dict(self.sites),
                "twin_references": dict(self.twin_refs),
                "imports": [list(i) for i in self.imports]}


def spells(token: str, name: str) -> bool:
    """Whether `token`, the text at a reference span, writes `name`: the name itself or a suffix
    of it on a component boundary, possibly after `@`, `_root_.` or the `.` of leading-dot
    notation (a field name after a receiver's `.` is such a suffix too)."""
    bare = token.removeprefix("@").removeprefix("_root_.")
    if bare.startswith(".") and not bare.startswith(".."):
        bare = bare[1:]
    return bool(bare) and (name == bare or name.endswith("." + bare))


def namespace_of(name: str) -> str:
    return name.rsplit(".", 1)[0] if "." in name else ""


def enclosing_opener(mask: str, pos: int) -> int:
    """The unmatched opening bracket before `pos`, or -1."""
    depth = 0
    for j in range(pos - 1, -1, -1):
        char = mask[j]
        if char in CLOSERS:
            depth += 1
        elif char in OPENERS:
            if depth == 0:
                return j
            depth -= 1
    return -1


def receiver_start(mask: str, dot: int) -> int:
    """The start of the atom ending just before the `.` at `dot`."""
    j = dot - 1
    if j >= 0 and mask[j] in CLOSERS:
        depth = 0
        while j >= 0:
            if mask[j] in CLOSERS:
                depth += 1
            elif mask[j] in OPENERS:
                depth -= 1
                if depth == 0:
                    return j
            j -= 1
        return 0
    while j >= 0 and (mask[j].isalnum() or mask[j] in "_'.!?₀₁₂₃₄₅₆₇₈₉" or ord(mask[j]) > 127
                      and mask[j] not in OPENERS + CLOSERS and not mask[j].isspace()):
        j -= 1
    return j + 1


def plan_markdown(plan: dict, limit: int = 40) -> str:
    s = plan["summary"]
    out = [f"### Rewrite plan for {s['area']}", "",
           f"{s['declarations']} case 2 declarations: " + ", ".join(
               f"{n} {m}" for m, n in sorted(s["modes"].items())) + ". References converted: "
           + ", ".join(f"{n} in {c} contexts" for c, n in sorted(s["sites"].items())) + "."]
    if s["imports"]:
        out.append(f"Imports added: {len(s['imports'])}.")
    if plan.get("round_trips"):
        out.append(f"Round trips removed: {plan['round_trips']}.")
    if s["manual"]:
        out += ["", "Manual work, by kind: " + "; ".join(f"{k} ({n})"
                                                          for k, n in s["manual"].items()) + ".",
                "", "| File | Line | Declaration | Kind | Detail |", "|---|--:|---|---|---|"]
        for m in plan["manual"][:limit]:
            out.append(f"| `{m['path']}` | {m['line']} | `{m['decl']}` | {m['kind']} | "
                       f"{m['detail']} |")
        if len(plan["manual"]) > limit:
            out.append(f"| … {len(plan['manual']) - limit} more in the JSON report | | | | |")
    if s.get("twin_references"):
        out.append("References to case 1 originals in restated proofs: " + ", ".join(
            f"{n} {k}" for k, n in sorted(s["twin_references"].items())) + ".")
    if plan.get("build"):
        b = plan["build"]
        errors = [d for d in b["diagnostics"] if d["level"] == "error"]
        out += ["", f"**Strict build: {b['status'].upper()}** (round {b['round']}, Lake exit "
                f"code {b['exit_code']}, {len(errors)} errors). Restated declarations failing: "
                f"{len(b['failing'])}; other declarations with errors: "
                f"{len({d['decl'] for d in b['client_errors']})}."]
        for d in errors[:limit]:
            out.append(f"* `{d['path']}:{d['line']}` `{d['decl']}`: {d['message'][:160]}")
    return "\n".join(out)


# --- Rewriting and verification -----------------------------------------------------------------

DIAGNOSTIC = re.compile(r"^(?P<level>error|warning): (?:\./)*(?P<path>[^\s:]+\.lean):"
                        r"(?P<line>\d+):(?P<col>\d+): (?P<msg>.*)$", re.M)
DECL_HEADER = re.compile(r"\b(?:theorem|lemma|def|abbrev|instance|example|structure|class|"
                         r"inductive|opaque)\b\s*([^\s(:{\[⦃]*)")


# Messages that report a consequence (axiom audits, `#guard_msgs` checks) rather than a proof
# the loop can repair.
CONSEQUENCE = re.compile(r"#guard_msgs|abstract audit|axiom audit|depends on disallowed axiom|"
                         r"declaration uses `sorry`")


def module_of(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    parts = rel.parts[1:] if rel.parts[0] == "abstracts" else rel.parts
    return ".".join(parts)


def diagnostics(output: str) -> list[dict]:
    return [{"level": m["level"], "path": m["path"], "line": int(m["line"]),
             "message": m["msg"]} for m in DIAGNOSTIC.finditer(output)]


def declaration_at(text: str, line: int) -> str:
    """The name in the header of the command containing a 1-based line; a line in the docstring
    or attributes before a declaration belongs to it."""
    mask = masks(text)[1]
    offset = sum(len(x) + 1 for x in text.split("\n")[:line - 1])
    after = next((m.start() for m in qr.COMMAND_START.finditer(mask, offset)), len(mask))
    if not mask[offset:after].strip() or mask[offset:after].lstrip().startswith("@["):
        offset = after
    starts = [m.start() for m in qr.COMMAND_START.finditer(mask) if m.start() <= offset]
    for start in reversed(starts):
        header = DECL_HEADER.search(mask, start, max(offset + 1, start + 400))
        if header:
            return header[1] or "(anonymous)"
    return ""


STRICT = ("--wfail", "--iofail")  # warnings fail the build, as in CI


def lake_build(targets: list[str], runner=subprocess.run) -> tuple[int, str]:
    proc = runner(["lake", "build", *STRICT, *targets], cwd=ROOT, text=True,
                  capture_output=True)
    return proc.returncode, proc.stdout + proc.stderr


def rewrite(model: Model, entries: list[Entry], twins: dict[str, str], area: str,
            verify: bool, rounds: int, build=lake_build) -> tuple[Planner, dict | None]:
    """Write the area's rewrite into the checkout. With `verify`, build the three libraries
    strictly and, up to `rounds` times, wrap the translated proofs that fail and rebuild.
    Remaining failures are reported, never patched over."""
    originals: dict[Path, str] = {}
    force: set[str] = set()
    result, history = None, []
    for round_ in range(1, rounds + 1):
        for path, text in originals.items():  # plan against the sources of the build
            path.write_text(text, encoding="utf-8")
        planner = Planner(model, entries, twins, area, frozenset(force)).plan()
        texts = planner.render()
        for path, text in texts.items():
            originals.setdefault(path, planner.source(path).text)
            path.write_text(text, encoding="utf-8")
        if not verify:
            return planner, None
        code, output = build(list(qr.ROOTS))
        result = check_build(planner, texts, output, code, round_)
        history.append({k: result[k] for k in ("round", "status", "failing", "forced_wrap")})
        retry = {d for d in result["failing"]
                 if planner.decls.get(d, {}).get("mode") == "translate"}
        if not retry or round_ == rounds:
            break
        force |= retry
    result["history"] = history
    return planner, result


def check_build(planner: Planner, texts: dict[Path, str], output: str, code: int,
                round_: int) -> dict:
    """The outcome of a strict build: `passed` only when Lake succeeded and reported no error.
    Errors are attributed to the restated declarations (`failing`) or to other declarations
    (`client_errors`)."""
    by_written = {}
    for name, info in planner.decls.items():
        by_written[(info["path"], name.rsplit(".", 1)[-1])] = name
        by_written[(info["path"], info["target"].rsplit(".", 1)[-1])] = name
    failing, clients, problems = set(), [], []
    for d in diagnostics(output):
        path = ROOT / d["path"]
        text = texts.get(path) or (path.read_text() if path.exists() else "")
        header = declaration_at(text, d["line"]) if text else ""
        decl = by_written.get((d["path"], header.rsplit(".", 1)[-1]))
        item = {**d, "decl": decl or header}
        if d["level"] == "error" and CONSEQUENCE.search(d["message"]):
            item["consequence"] = True
        elif d["level"] == "error" and decl:
            failing.add(decl)
            planner.decls[decl].setdefault("errors", []).append(d["message"])
        elif d["level"] == "error":
            clients.append(item)
        problems.append(item)
    errors = any(d["level"] == "error" for d in problems)
    return {"round": round_, "status": "passed" if code == 0 and not errors else "failed",
            "exit_code": code, "failing": sorted(failing), "client_errors": clients,
            "diagnostics": problems, "forced_wrap": sorted(planner.force_wrap)}


def unified_diff(planner: Planner) -> str:
    out = []
    for path, text in sorted(planner.render().items()):
        rel = str(path.relative_to(ROOT))
        out += difflib.unified_diff(planner.source(path).text.splitlines(True),
                                    text.splitlines(True), "a/" + rel, "b/" + rel)
    return "".join(out)


def exit_status(plans: list[dict]) -> int:
    """Nonzero when a verified rewrite did not build."""
    return int(any(p["build"] is not None and p["build"]["status"] != "passed" for p in plans))


# --- Command line -------------------------------------------------------------------------------

def entry_json(e: Entry) -> dict:
    return {k: v for k, v in e.__dict__.items()}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("command", choices=("report", "rewrite"))
    parser.add_argument("--area", action="append", default=[],
                        help="restrict to an area of #587 (repeatable for report)")
    parser.add_argument("--registry", type=Path,
                        help="extra original → twin pairs from a migration script (JSON)")
    parser.add_argument("--allowlist", type=Path, default=ALLOWLIST)
    parser.add_argument("--build-dir", type=Path, default=qr.DEFAULT_BUILD_DIR)
    parser.add_argument("--no-build-check", action="store_true",
                        help="report only: do not check that the build outputs are current")
    parser.add_argument("--json", type=Path, help="write the full report as JSON")
    parser.add_argument("--markdown", type=Path, help="write the report as Markdown")
    parser.add_argument("--no-plan", action="store_true", help="report: skip rewrite plans")
    parser.add_argument("--verify", action="store_true",
                        help="rewrite: build strictly, wrap failing translations, report the rest")
    parser.add_argument("--diff", type=Path,
                        help="rewrite: write a unified diff of the plan instead of the files")
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--limit", type=int, default=40, help="rows per Markdown table")
    args = parser.parse_args(argv)
    for area in args.area:
        if area not in AREA_ORDER:
            parser.error(f"unknown area {area}; choose from {', '.join(AREA_ORDER)}")
    if args.command == "rewrite" and len(args.area) != 1:
        parser.error("rewrite needs exactly one --area")
    if args.command == "rewrite" and args.no_build_check:
        parser.error("rewrite edits at the recorded reference spans, so it needs current build "
                     "outputs; --no-build-check is only for report")
    try:
        registry = load_registry(args.registry)
    except ValueError as error:
        parser.error(str(error))
    outputs = qr.check_outputs(args.build_dir, args.no_build_check)
    model = Model(args.build_dir, load_allowlist(args.allowlist))
    twins = twin_map(model.constants, registry)
    entries = classify_all(model, twins)
    shown = [e for e in entries if not args.area or e.area in args.area]
    revision = qr.run(["git", "rev-parse", "HEAD"], capture_output=True).stdout.strip()
    dirty = bool(qr.run(["git", "status", "--porcelain", "--", "Complexity", "ComplexityTests",
                         "abstracts"], capture_output=True).stdout.strip())
    report = {"revision": revision, "dirty": dirty, "outputs": outputs,
              "allowlist_size": len(model.allowlist),
              "registry": str(args.registry) if args.registry else None,
              "registry_size": len(registry),
              "twins": dict(Counter(kind for _, kind in twins.values())),
              "registry_problems": registry_problems(registry, model.constants),
              "summary": summary(shown), "entries": [entry_json(e) for e in shown]}
    plain_twins = {o: p for o, (p, _) in twins.items()}
    plans = []
    if args.command == "rewrite" and args.diff:
        planner = Planner(model, entries, plain_twins, args.area[0]).plan()
        args.diff.write_text(unified_diff(planner))
        plans.append((planner, None))
    elif args.command == "rewrite":
        plans.append(rewrite(model, entries, plain_twins, args.area[0], args.verify,
                             args.rounds))
    elif not args.no_plan:
        for area in args.area or AREA_ORDER:
            if any(e.area == area and e.case == "2" for e in entries):
                planner = Planner(model, entries, plain_twins, area).plan()
                planner.render()
                plans.append((planner, None))
    report["plans"] = [{"summary": p.summary(), "round_trips": p.round_trips,
                        "decls": list(p.decls.values()),
                        "manual": [m.__dict__ for m in p.manual], "build": b}
                       for p, b in plans]
    text = markdown_report(report, args.limit) + "".join(
        "\n" + plan_markdown(p, args.limit) + "\n" for p in report["plans"])
    if args.markdown:
        args.markdown.write_text(text)
    else:
        print(text)
    if args.json:
        args.json.write_text(json.dumps(report, indent=1, ensure_ascii=False) + "\n")
    return exit_status(report["plans"])


if __name__ == "__main__":
    sys.exit(main())
