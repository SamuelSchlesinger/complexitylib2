/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Basic

/-!
# Native linear-workspace compact-graph routines

All runtime numbers use binary encodings. The table and register indices are fixed, so the
algorithms below use finitely many linear-workspace arithmetic routines. These certificates
charge no copy of the original input word: the edge routine receives only its length, two IDs,
and the single supplied symbol. The time bound is unrestricted.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.queryIndex_inSpace`: compute the only input query.
* `Turing.MultiTapeNTM.ConfigurationGraph.edgeWithSymbol_inSpace`: evaluate an edge locally.
* `Turing.MultiTapeNTM.ConfigurationGraph.bad_inSpace`: recognize an accepting halted vertex.
* `Turing.MultiTapeNTM.ConfigurationGraph.startID_inSpace`: initialize the compact graph.
-/

@[expose] public section

namespace Turing.MultiTapeNTM.ConfigurationGraph

open MultiTapeTM ComputableInSpace

variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}

private theorem and_inSpace {f g : α → Bool}
    (hf : ComputableInSpace f enc encBool S) (hg : ComputableInSpace g enc encBool S) :
    ComputableInSpace (fun a => f a && g a) enc encBool S :=
  budget_finite (fun p : Bool × Bool => p.1 && p.2) (budget_prod hf hg)

private theorem or_inSpace {f g : α → Bool}
    (hf : ComputableInSpace f enc encBool S) (hg : ComputableInSpace g enc encBool S) :
    ComputableInSpace (fun a => f a || g a) enc encBool S :=
  budget_finite (fun p : Bool × Bool => p.1 || p.2) (budget_prod hf hg)

private theorem all_inSpace {ι : Type} (l : List ι) {f : ι → α → Bool}
    (hf : ∀ i, ComputableInSpace (f i) enc encBool S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => (l.map fun i => f i a).all id) enc encBool S := by
  induction l with
  | nil => exact budget_const true hin
  | cons i l ih => exact and_inSpace (hf i) ih

private theorem any_inSpace {ι : Type} (l : List ι) {f : ι → α → Bool}
    (hf : ∀ i, ComputableInSpace (f i) enc encBool S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => l.any fun i => f i a) enc encBool S := by
  induction l with
  | nil => exact budget_const false hin
  | cons i l ih => exact or_inSpace (hf i) ih

variable {k : ℕ} {State : Type} [Fintype State] {D : ℕ}
  {n u v : α → ℕ} {symbol : α → Option Bool}

/-- The fixed radix power is computable in space linear in the binary length parameter. -/
theorem radix_budget (hn : ComputableInSpace n enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => radix D (n a)) enc encNat S :=
  budget_natPow (budget_natAdd hn (budget_const 2 hin)) hin D

/-- Reading any fixed register preserves a common space budget. -/
theorem readRegisters_budget (hn : ComputableInSpace n enc encNat S)
    (hu : ComputableInSpace u enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) (i : Register k) :
    ComputableInSpace (fun a => readRegisters D (n a) (u a) i) enc encNat S :=
  budget_comp_linear (component_inSpace i) (budget_prod (radix_budget hn hin) hu)

private theorem valid_budget (hn : ComputableInSpace n enc encNat S)
    (hu : ComputableInSpace u enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => valid (k := k) (State := State) D (n a) (u a))
      enc encBool S := by
  have hr := readRegisters_budget (D := D) (k := k) hn hu hin
  have hB := radix_budget (D := D) hn hin
  have hb := budget_natPow hB hin (Fintype.card (Register k))
  have hi := budget_natLt (hr .inputPos) (budget_natAdd hn (budget_const 2 hin))
  have hc := budget_natLt (hr .control) (budget_const (Fintype.card (Option State)) hin)
  have ho := budget_natLt (hr .output) (budget_const 3 hin)
  have hh := all_inSpace (List.ofFn fun i : Fin k => i)
    (fun i => budget_natLt (hr (.head i)) (budget_const 3 hin)) hin
  apply (and_inSpace (and_inSpace (and_inSpace
    (and_inSpace (budget_natLt hu hb) hi) hc) ho) hh).of_enc_eq
  intro a
  congr 1
  dsimp only [valid, vertexBound]
  rw [List.map_ofFn]
  rfl

private theorem inputSymbol_budget {p : α → ℕ}
    (hn : ComputableInSpace n enc encNat S)
    (hp : ComputableInSpace p enc encNat S)
    (hs : ComputableInSpace symbol enc (encOption encBool) S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => inputSymbol (n a) (p a) (symbol a))
      enc (encOption encBool) S := by
  have hc := or_inSpace (budget_natIsZero hp) (budget_natEq hp (budget_natSucc hn))
  simpa only [inputSymbol, Bool.or_eq_true, decide_eq_true_eq] using
    budget_ite hc (budget_const none hin) hs

private theorem nextRegisters_budget {r : α → Register k → ℕ}
    (hn : ComputableInSpace n enc encNat S)
    (hr : ∀ i, ComputableInSpace (fun a => r a i) enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) (act : Action k Bool State) (i : Register k) :
    ComputableInSpace (fun a => nextRegisters (n a) (r a) act i) enc encNat S := by
  cases i with
  | inputPos =>
    cases hm : act.inputTape with
    | neg => simpa only [nextRegisters, hm, inputMove] using budget_natPred (hr .inputPos)
    | zero => simpa only [nextRegisters, hm, inputMove] using hr .inputPos
    | pos =>
      have hp := budget_natSucc (hr .inputPos)
      have hn' := budget_natSucc hn
      exact (budget_ite (budget_natLt hp hn') hp hn').of_enc_eq fun a => by
        simp only [nextRegisters, hm, inputMove, decide_eq_true_eq]
        congr 1
        split_ifs <;> omega
  | control => exact budget_const _ hin
  | output =>
    cases ho : act.output with
    | none => simpa only [nextRegisters, ho, outputStep] using hr .output
    | some b =>
      simpa only [nextRegisters, ho, outputStep, decide_eq_true_eq] using
        budget_ite (budget_natIsZero (hr .output))
          (budget_const (encB := encNat) (if b then 1 else 2) hin) (budget_const 2 hin)
  | head i | left i | right i =>
    have hh : ComputableInSpace
        (fun a => (act.workTapes i).1.elim (r a (.head i)) symbolCode) enc encNat S := by
      cases (act.workTapes i).1 with
      | none => exact hr (.head i)
      | some b => exact budget_const _ hin
    have hthree : ComputableInSpace (fun _ : α => 3) enc encNat S := budget_const 3 hin
    cases hm : (act.workTapes i).2 <;>
      simp only [nextRegisters, tapeStep, hm] <;>
      first
      | exact hh
      | exact hr _
      | exact budget_natMod (hr _) hthree
      | exact budget_natDiv (hr _) hthree
      | exact budget_natAdd hh (budget_natMul hthree (hr _))

private theorem matchesEntry_budget {r : α → Register k → ℕ}
    (hn : ComputableInSpace n enc encNat S)
    (hr : ∀ i, ComputableInSpace (fun a => r a i) enc encNat S)
    (hs : ComputableInSpace symbol enc (encOption encBool) S)
    (hin : (fun a => (enc a).length) ≼ S) (t : Instruction k State) :
    ComputableInSpace (fun a => matchesEntry (n a) (r a) (symbol a) t) enc encBool S := by
  have hc := budget_natEq (hr .control) (budget_const (stateCode (some t.1)) hin)
  have hi := budget_finite (encC := encBool) (fun b : Option Bool => decide (b = t.2.1))
    (inputSymbol_budget hn (hr .inputPos) hs hin)
  have hh := all_inSpace (List.ofFn fun i : Fin k => i)
    (fun i => budget_natEq (hr (.head i)) (budget_const (symbolCode (t.2.2.1 i)) hin)) hin
  apply (and_inSpace (and_inSpace hc hi) hh).of_enc_eq
  intro a
  congr 1
  dsimp only [matchesEntry]
  rw [List.map_ofFn]
  rfl

private theorem fitsB_budget {B : α → ℕ} {r : α → Register k → ℕ}
    (hB : ComputableInSpace B enc encNat S)
    (hr : ∀ i, ComputableInSpace (fun a => r a i) enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => fitsB (B a) (r a)) enc encBool S := by
  simpa only [fitsB, List.all_map, Function.comp_def, id_eq] using
    all_inSpace (Finset.univ.toList : List (Register k)) (fun i => budget_natLt (hr i) hB) hin

/-- Local edge evaluation preserves any budget covering the short arguments. -/
theorem edgeWithSymbol_budget (ntm : MultiTapeNTM k Bool State)
    (hn : ComputableInSpace n enc encNat S)
    (hu : ComputableInSpace u enc encNat S)
    (hv : ComputableInSpace v enc encNat S)
    (hs : ComputableInSpace symbol enc (encOption encBool) S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableInSpace (fun a => edgeWithSymbol ntm D (n a) (u a) (v a) (symbol a))
      enc encBool S := by
  have hr := readRegisters_budget (D := D) (k := k) hn hu hin
  have hB := radix_budget (D := D) hn hin
  have hh := and_inSpace
    (budget_natEq (hr .control) (budget_const (stateCode (none : Option State)) hin))
    (budget_natEq hv hu)
  have hentry (t : Instruction k State) :=
    let hnxt := nextRegisters_budget hn hr hin t.2.2.2
    and_inSpace (and_inSpace (matchesEntry_budget hn hr hs hin t) (fitsB_budget hB hnxt hin))
      (budget_natEq hv (pack_inSpace hB hnxt hin))
  exact and_inSpace (and_inSpace (valid_budget hn hu hin) (valid_budget hn hv hin))
    (or_inSpace hh (any_inSpace (instructions ntm) hentry hin))

/-- Encoded length and one ID. -/
abbrev encVertex : ℕ × ℕ ↪ List Bool := encPair encNat encNat

/-- Encoded length, source, target, and the one supplied input symbol. -/
abbrev encEdge : ℕ × ℕ × ℕ × Option Bool ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat (encOption encBool)))

/-- Compute the only input query in native deterministic linear workspace. -/
theorem queryIndex_inSpace (D : ℕ) :
    ComputableInSpace (fun a : ℕ × ℕ => queryIndex (k := k) D a.1 a.2)
      encVertex encNat fun a => (encVertex a).length :=
  budget_natPred (readRegisters_budget (fst _ _) (snd _ _) (.refl _) .inputPos)

/-- Evaluate an edge using native deterministic linear workspace in binary short arguments. -/
theorem edgeWithSymbol_inSpace (ntm : MultiTapeNTM k Bool State) (D : ℕ) :
    ComputableInSpace
      (fun a : ℕ × ℕ × ℕ × Option Bool => edgeWithSymbol ntm D a.1 a.2.1 a.2.2.1 a.2.2.2)
      encEdge encBool fun a => (encEdge a).length := by
  have hn : ComputableInSpace (fun a : ℕ × ℕ × ℕ × Option Bool => a.1)
      encEdge encNat fun a => (encEdge a).length := fst _ _
  have hrest : ComputableInSpace (fun a : ℕ × ℕ × ℕ × Option Bool => a.2)
      encEdge (encPair encNat (encPair encNat (encOption encBool)))
      (fun a => (encEdge a).length) := snd _ _
  have hu := budget_comp_linear (fst _ _) hrest
  have hvs := budget_comp_linear (snd _ _) hrest
  exact edgeWithSymbol_budget ntm hn hu (budget_comp_linear (fst _ _) hvs)
    (budget_comp_linear (snd _ _) hvs) (.refl _)

/-- Recognize the accepting halted vertices in native deterministic linear workspace. -/
theorem bad_inSpace (D : ℕ) :
    ComputableInSpace (fun a : ℕ × ℕ => bad (State := State) (k := k) D a.1 a.2)
      encVertex encBool fun a => (encVertex a).length := by
  have hn : ComputableInSpace (fun a : ℕ × ℕ => a.1) encVertex encNat
      (fun a => (encVertex a).length) := fst _ _
  have hu : ComputableInSpace (fun a : ℕ × ℕ => a.2) encVertex encNat
      (fun a => (encVertex a).length) := snd _ _
  have hr := readRegisters_budget (D := D) (k := k) hn hu (.refl _)
  exact and_inSpace (and_inSpace (valid_budget hn hu (.refl _))
    (budget_natEq (hr .control) (budget_const (stateCode (none : Option State)) (.refl _))))
    (budget_natEq (hr .output) (budget_const 1 (.refl _)))

/-- The polynomial ambient graph size is computable from the binary input length. -/
theorem vertexBound_inSpace (D : ℕ) :
    ComputableInSpace (vertexBound (k := k) D) encNat encNat
      (fun n => (encNat n).length) := by
  have hn : ComputableInSpace (fun n : ℕ => n) encNat encNat
      (fun n => (encNat n).length) := of_inO (.of_linear (.of_eq fun _ => rfl))
  exact budget_natPow (radix_budget hn (.refl _)) (.refl _) (Fintype.card (Register k))

/-- Compute the input-independent start ID from the binary input length. -/
theorem startID_inSpace (ntm : MultiTapeNTM k Bool State) (D : ℕ) :
    ComputableInSpace (startID ntm D) encNat encNat fun n => (encNat n).length := by
  have hn : ComputableInSpace (fun n : ℕ => n) encNat encNat
      (fun n => (encNat n).length) := of_inO (.of_linear (.of_eq fun _ => rfl))
  exact pack_inSpace (radix_budget hn (.refl _)) (fun _ => budget_const _ (.refl _)) (.refl _)

end Turing.MultiTapeNTM.ConfigurationGraph
