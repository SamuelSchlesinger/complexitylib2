/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (project validation tooling)

import Lean.Elab.ParseImportsFast
import Lean.Data.Json.FromToJson.Basic

/-! Parse current source headers for quick validation without loading compiled project modules. -/

/-- Read a JSON array of source paths and emit their imports using Lean's header parser. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let json ← IO.ofExcept (Lean.Json.parse input)
  let paths ← IO.ofExcept (Lean.fromJson? json : Except String (Array String))
  let mut rows : Array Lean.Json := #[]
  for path in paths do
    let header ← Lean.parseImports' (← IO.FS.readFile path) path
    rows := rows.push <| Lean.Json.mkObj [
      ("path", Lean.toJson path),
      ("imports", Lean.toJson (header.imports.map fun i => i.module.toString))]
  IO.println (Lean.toJson rows).compress
