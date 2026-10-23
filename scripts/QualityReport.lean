/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
-- upstream: local-only (project validation tooling)
import Lean

/-!
# Declaration data for `scripts/quality_report.py`

Run as `lake env lean --run scripts/QualityReport.lean <lib-dir> < modules.txt`, with one module
name per line on standard input. For every module it reads the three parts of the built `.olean`
(exported, server and private) without importing them, and prints one JSON line per constant:

* `n`, `m`: the constant and its module;
* `k`: its kind in the private part (`def`, `thm`, `induct`, `ctor`, `rec`, `opaque`, `quot`,
  `axiom`); `e`: its kind in the exported part, or `""` when it is not exported. Under the module
  system a public theorem is exported as an `axiom` (statement only), a definition whose body is not
  exposed as an `axiom`, and an exposed definition as a `def`;
* `doc`: whether it has a docstring (Markdown, Verso or `@[inherit_doc]`);
* `tidy`: the constants named `ComputableTidily…`, `ComputesTidily…` or `IsTidy…` in its type;
* `u`: for an exported constant, the other constants of the same module that its exported
  statement or exposed body mentions (these cannot become private while it stays public);
* `r`: its declaration range `[line, column, endLine, endColumn, selLine, selColumn, selEndLine,
  selEndColumn]`, with 1-based lines and code-point columns, when one is recorded.

It then prints `{"dup": [...], "k": ...}` lines grouping exported constants of different modules
whose types are alpha-equivalent (`k = "thm"`), or whose types and exposed bodies are
(`k = "def"`). Universe parameters are renamed positionally before comparing.
-/

open Lean

namespace ComplexityScripts.QualityReport

def kindOf : ConstantInfo → String
  | .defnInfo _ => "def"
  | .thmInfo _ => "thm"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def isTidy (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "ComputableTidily" || s.startsWith "ComputesTidily" ||
      s.startsWith "IsTidy"
  | _ => false

/-- The declarations named by entries of the extensions whose names end in one of `suffixes`.
Every such extension is a `MapDeclarationExtension`, whose entries are pairs headed by a name. -/
unsafe def entryNames (entries : Array (Name × Array EnvExtensionEntry)) (suffixes : List String) :
    NameSet := Id.run do
  let mut names : NameSet := {}
  for (ext, es) in entries do
    if let .str _ s := ext then
      if suffixes.contains s then
        for e in es do
          names := names.insert (unsafeCast e : Name × Unit).1
  return names

unsafe def declRanges (entries : Array (Name × Array EnvExtensionEntry)) :
    NameMap DeclarationRanges := Id.run do
  let mut ranges : NameMap DeclarationRanges := {}
  for (ext, es) in entries do
    if ext == `Lean.declRangeExt then
      for e in es do
        let (n, r) := (unsafeCast e : Name × DeclarationRanges)
        ranges := ranges.insert n r
  return ranges

def rangeJson (r : DeclarationRanges) : Json :=
  let a := r.range
  let s := r.selectionRange
  toJson #[a.pos.line, a.pos.column, a.endPos.line, a.endPos.column,
    s.pos.line, s.pos.column, s.endPos.line, s.endPos.column]

/-- Rename universe parameters positionally, so that alpha-equivalence ignores their names. -/
def normalize (c : ConstantInfo) (e : Expr) : Expr :=
  let us := c.levelParams.length.fold (fun i _ acc => acc.push (Level.param (.num `u i))) #[]
  e.instantiateLevelParams c.levelParams us.toList

unsafe def run (libDir : System.FilePath) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut theorems : Std.HashMap Expr (Array (String × Name)) := {}
  let mut defs : Std.HashMap (Expr × Expr) (Array (String × Name)) := {}
  -- The mapped regions must stay alive while `theorems` and `defs` refer to their expressions.
  let mut regions : Array CompactedRegion := #[]
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let mod := line.trimAscii.toString
    if mod.isEmpty then continue
    let base := (libDir / System.FilePath.mk (mod.replace "." "/")).addExtension "olean"
    let parts ← readModuleDataParts #[base, base.addExtension "server", base.addExtension "private"]
    let some (exportedData, r0) := parts[0]? | throw <| IO.userError s!"cannot read {base}"
    let some (fullData, r2) := parts[2]? | throw <| IO.userError s!"cannot read {base}.private"
    regions := regions ++ #[r0, r2]
    let mut exported : Std.HashMap Name ConstantInfo := {}
    for c in exportedData.constants do
      exported := exported.insert c.name c
    let docs := entryNames fullData.entries
      ["docStringExt", "versoDocStringExt", "inheritDocStringExt"]
    let ranges := declRanges fullData.entries
    let sameModule : NameSet := fullData.constNames.foldl (·.insert ·) {}
    for c in fullData.constants do
      let e := exported[c.name]?
      let tidy := c.type.getUsedConstants.filter isTidy |>.map (·.toString)
      let uses := match e with
        | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
        | some ec => ec.type.getUsedConstants
        | none => #[]
      let uses := uses.filter (fun n => n != c.name && sameModule.contains n) |>.toList.eraseDups
      stdout.putStrLn <| Json.compress <| Json.mkObj [
        ("n", c.name.toString), ("m", mod), ("k", kindOf c), ("e", (e.map kindOf).getD ""),
        ("doc", docs.contains c.name), ("tidy", toJson tidy),
        ("u", toJson (uses.map (·.toString))),
        ("r", (ranges.find? c.name).map rangeJson |>.getD .null)]
      if let some ec := e then
        unless c.name.isInternalDetail do
          match c, ec with
          | .thmInfo _, _ =>
            let key := normalize ec ec.type
            theorems := theorems.insert key ((theorems.getD key #[]).push (mod, c.name))
          | .defnInfo _, .defnInfo v =>
            let key := (normalize ec ec.type, normalize ec v.value)
            defs := defs.insert key ((defs.getD key #[]).push (mod, c.name))
          | _, _ => pure ()
  let emit (kind : String) (group : Array (String × Name)) : IO Unit := do
    if (group.map (·.1)).toList.eraseDups.length > 1 then
      stdout.putStrLn <| Json.compress <| Json.mkObj [
        ("dup", toJson (group.map fun (m, n) => #[m, n.toString])), ("k", kind)]
  for (_, group) in theorems do emit "thm" group
  for (_, group) in defs do emit "def" group
  -- Keep the regions reachable until every expression has been used.
  if regions.isEmpty then stdout.flush

end ComplexityScripts.QualityReport

unsafe def main (args : List String) : IO Unit :=
  ComplexityScripts.QualityReport.run (args.headD ".lake/build/lib/lean")
