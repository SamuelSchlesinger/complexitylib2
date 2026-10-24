"""Regression checks for inventory completeness, snapshot coverage and result accounting."""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    "plain_certificate_inventory", Path(__file__).with_name("plain_certificate_inventory.py"))
assert spec and spec.loader
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


def record(name="cert", **kw):
    return {"declaration": {"name": name}, "status": "compared",
            "tidy_holdout": {"status": "success", "heartbeats_raw": 37},
            "plain_holdout": {"status": "failed", "heartbeats_raw": 41}, **kw}


class InventoryTests(unittest.TestCase):
    def test_all_libraries_and_custom_srcdir(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "lakefile.toml").write_text('''[[lean_lib]]
name = "Complexity"
[[lean_lib]]
name = "ComplexityTests"
[[lean_lib]]
name = "ComplexityAbstracts"
srcDir = "abstracts"
''')
            for name in ["Complexity.lean", "Complexity/A.lean", "ComplexityTests/Captured.lean",
                         "abstracts/ComplexityAbstracts/Bridge.lean"]:
                p = root / name
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text("-- fixture\n")
            sources = runner.discover_sources(root)
            self.assertEqual(set(sources), {"Complexity", "Complexity.A",
                                           "ComplexityTests.Captured", "ComplexityAbstracts.Bridge"})
            with self.assertRaises(FileNotFoundError):
                runner.validate_ileans(root, sources)
            for module in sources:
                p = root / ".lake/build/lib/lean" / Path(*module.split("."))
                p = p.with_suffix(".ilean")
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(json.dumps({"version": 5, "module": module}))
            runner.validate_ileans(root, sources)
            p.write_text(json.dumps({"version": 4, "module": module}))
            with self.assertRaisesRegex(ValueError, "unsupported"):
                runner.validate_ileans(root, sources)

    def test_truncation_is_not_coverage(self):
        with self.assertRaisesRegex(ValueError, "truncated"):
            runner.validate_rows([{"inventory_total": 2, "limit": 0}, record()])

    def test_debug_subset_is_explicitly_incomplete(self):
        summary = runner.validate_rows([{"inventory_total": 5, "limit": 1}, record()])
        self.assertFalse(summary["inventory_complete"])
        self.assertEqual(summary["inventory_total"], 5)

    def test_duplicates_cannot_fill_missing_rows(self):
        with self.assertRaisesRegex(ValueError, "duplicate"):
            runner.validate_rows([{"inventory_total": 2, "limit": 0}, record(), record()])

    def test_unsupported_exact_bounds_remain_visible(self):
        row = {"declaration": {"name": "exact"}, "status": "unsupported_tidy",
               "residual_tidy": ["ComputableTidilyInTimeAndSpace"]}
        summary = runner.validate_rows([{"inventory_total": 1, "limit": 0}, row])
        self.assertTrue(summary["inventory_complete"])
        self.assertEqual(summary["statuses"], {"unsupported_tidy": 1})
        self.assertEqual(summary["holdout_pairs"], {})

    def test_registration_does_not_count_as_synthesis(self):
        row = record(plain_registration={"status": "success", "heartbeats_raw": 2})
        summary = runner.validate_rows([{"inventory_total": 1, "limit": 0}, row])
        self.assertEqual(summary["registration_probes"], 1)
        self.assertEqual(summary["holdout_pairs"], {"tidy:success/plain:failed": 1})

    def test_unknown_status_fails_closed(self):
        with self.assertRaises(ValueError):
            runner.validate_rows([{"inventory_total": 1, "limit": 0}, record(status="skipped")])



def native_probes():
    """Opt-in checked Lean fixtures: private/local inventory and independent self-exclusion."""
    import os
    import subprocess
    import sys
    root = Path(__file__).resolve().parents[1]
    lean = subprocess.check_output(["lake", "env", "which", "lean"], cwd=root, text=True).strip()
    leanpath = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                       cwd=root, text=True).strip()
    fixture = r"""
import scripts.PlainCertificateInventory
import Mathlib.Tactic.FunProp
open Lean Meta Mathlib.Meta.FunProp PlainCertificateInventory
@[fun_prop] def TidyInventoryProperty (f : ℕ → ℕ) : Prop := ∀ x, f x = f x
opaque uniqueFunction : ℕ → ℕ := id
abbrev HiddenProperty := TidyInventoryProperty
@[fun_prop] theorem isolated_source : TidyInventoryProperty uniqueFunction := fun _ => rfl
@[fun_prop] theorem indirect_source : TidyInventoryProperty uniqueFunction := isolated_source
theorem hidden_source : HiddenProperty uniqueFunction := isolated_source
private theorem captured_source (f : ℕ → ℕ) (hf : TidyInventoryProperty f) :
    TidyInventoryProperty f := by
  have localRoutine : TidyInventoryProperty f := hf
  have hiddenRoutine : HiddenProperty f := localRoutine
  exact hiddenRoutine
run_meta do
  let type := mkApp (mkConst `TidyInventoryProperty) (mkConst `uniqueFunction)
  let leaf := Expr.letE `localRoutine type (mkConst `isolated_source) (mkConst `True.intro) true
  for depth in #[8, 16, 24] do
    let mut dag := leaf
    for _ in [:depth] do dag := .app dag dag
    let (certificates, stats) := localCertificatesWithStats id `ownerA dag
    unless certificates.size == 1 && stats.visits == depth + 3 do
      throwError "shared DAG was revisited as a tree: {stats.visits} visits at depth {depth}"
  let withoutTidy := Expr.letE `value (mkConst `Nat) (mkNatLit 0) (mkConst `True.intro) true
  let (noneFound, zeroWalk) := localCertificatesWithStats id `irrelevant withoutTidy
  unless noneFound.isEmpty && zeroWalk.visits == 0 do
    throwError "irrelevant proof body should not need local-certificate traversal"
  let underTwoBinders := Expr.app (.lam `left (mkConst `Nat) leaf .default)
    (.lam `right (mkConst `Nat) leaf .default)
  unless (localCertificates id `ownerA underTwoBinders).size == 2 do
    throwError "distinct binder contexts were merged"
  let otherOwner := localCertificates id `ownerB leaf
  unless otherOwner.size == 1 && otherOwner.all (fun c => c.owner == `ownerB) do
    throwError "different owner declarations were merged"
  let bad : Std.HashSet Name := .ofArray #[`blocked]
  let entry : GeneralTheorem := { (default : GeneralTheorem) with thmName := `blocked }
  let node : Lean.Meta.RefinedDiscrTree.Trie GeneralTheorem := {
    (default : Lean.Meta.RefinedDiscrTree.Trie GeneralTheorem) with
    values := #[entry]
    pending := #[(default, entry)] }
  let tree : GeneralTheorems := { theorems := { tries := #[node] } }
  let env ← getEnv
  let f : FunctionTheorem := {
    funPropName := `P, thmOrigin := .decl `blocked, funOrigin := .decl `f,
    mainArgs := #[], appliedArgs := 1, form := .uncurried }
  let l : LambdaTheorem := { funPropName := `P, thmName := `blocked, thmArgs := .id }
  let env := functionTheoremsExt.modifyState env fun s => { s with
    theorems := s.theorems.insert `f ((s.theorems.getD `f {}).insert `P #[f]) }
  let env := lambdaTheoremsExt.modifyState env fun s => { s with
    theorems := s.theorems.insert (`P, .id) #[l] }
  let env := transitionTheoremsExt.modifyState env fun _ => tree
  let env := morTheoremsExt.modifyState env fun _ => tree
  let filtered := exclude env bad
  unless (((functionTheoremsExt.getState filtered).theorems.getD `f {}).getD `P #[]).isEmpty do
    throwError "function database exclusion failed"
  unless ((lambdaTheoremsExt.getState filtered).theorems.getD (`P, .id) #[]).isEmpty do
    throwError "lambda database exclusion failed"
  for state in #[transitionTheoremsExt.getState filtered, morTheoremsExt.getState filtered] do
    unless state.theorems.tries[0]!.values.isEmpty &&
        state.theorems.tries[0]!.pending.isEmpty do
      throwError "lazy/evaluated general database exclusion failed"
  let reverse := ({} : Std.HashMap Name (List Name)).insert `blocked [`dependent]
    |>.insert `dependent [`transitive]
  unless (closure reverse #[`blocked]).contains `transitive do
    throwError "indirect exclusion failed"
"""
    fixture += "\nnamespace Mathlib.InventoryFixture\ntheorem denseRoot : True := True.intro\n"
    fixture += "".join(f"theorem denseNode{i} : True := denseRoot\n" for i in range(1000))
    fixture += "end Mathlib.InventoryFixture\n"
    with tempfile.TemporaryDirectory(prefix="plain-inventory-native-") as td:
        tmp = Path(td)
        lib = tmp / "lib"
        (lib / "scripts").mkdir(parents=True)
        env = {**os.environ, "LEAN_PATH": str(lib) + ":" + leanpath, "LEAN_NUM_THREADS": "2"}
        subprocess.run([lean, "-o", str(lib / "scripts/PlainCertificateInventory.olean"),
                        "scripts/PlainCertificateInventory.lean"], cwd=root, env=env, check=True)
        (tmp / "PlainInventoryProbe.lean").write_text(fixture)
        subprocess.run([lean, "-o", str(lib / "PlainInventoryProbe.olean"),
                        "PlainInventoryProbe.lean"], cwd=tmp, env=env, check=True)
        checker = r"""
import scripts.PlainCertificateInventory
import PlainInventoryProbe
open Lean Meta PlainCertificateInventory
run_meta do
  let env ← getEnv
  let modules : Std.HashSet Name := .ofArray #[`PlainInventoryProbe]
  let reverse := reverseDependencies env modules
  let incoming := reverse.getD `Mathlib.InventoryFixture.denseRoot []
  unless incoming.length == 1000 do throwError "lost dense dependency edges: {incoming.length}"
  let actual := closure reverse #[`Mathlib.InventoryFixture.denseRoot]
  unless actual.size == 1001 do throwError "wrong closure size: {actual.size}"
  for i in [:1000] do
    unless actual.contains (`Mathlib.InventoryFixture ++ s!"denseNode{i}".toName) do
      throwError "lost dependent {i}"
  for dependent in reverse.getD `True [] do
    let some idx := env.getModuleIdxFor? dependent | throwError "unclassified dependency"
    unless env.header.moduleNames[idx.toNat]! == `PlainInventoryProbe do
      throwError "indexed an upstream owner instead of a project dependent"
"""
        (tmp / "CheckDense.lean").write_text(checker)
        subprocess.run([lean, "CheckDense.lean"], cwd=tmp, env=env, check=True)
        modules, output = tmp / "modules.txt", tmp / "rows.jsonl"
        modules.write_text("PlainInventoryProbe\n")
        subprocess.run([lean, "--run", str(root / runner.RUNNER), str(modules),
                        str(output), "20000", "0"], cwd=root, env=env, check=True)
        rows = [json.loads(line) for line in output.read_text().splitlines()]
        runner.validate_rows(rows)
        records = rows[1:]
        isolated = next(r for r in records if r["declaration"]["name"] == "isolated_source")
        assert isolated["tidy_holdout"]["status"] != "success", isolated
        assert isolated["excluded_count"] >= 2
        assert any(r["declaration"]["name"] == "hidden_source" for r in records)
        local = [r for r in records if r["declaration"].get("local_path")]
        assert local and all(r["declaration"]["private"] for r in local)
        assert any("localRoutine" in r["declaration"]["name"] for r in local)
        assert all(sum(r["declaration"]["type"].count(n) for n in
                       ("TidyInventoryProperty", "HiddenProperty")) >= 2 for r in local)
        print("Native probes passed: contextual DAG memo, dense fan-in/closure, actual-module owners, four databases, private/local/alias capture")


if __name__ == "__main__":
    import sys
    if sys.argv[1:] == ["--native"]:
        native_probes()
    else:
        unittest.main()
