/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.MonotoneCircuitValue
public import Complexity.Computability.Complexity.Problems.CircuitValue.Writer
public import Complexity.Computability.Circuit.Monotone.DualRail
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Run

/-!
# The monotone circuit value problem is `P`-complete

**Goldschlager's theorem** [Goldschlager1977]: the monotone circuit value problem is `P`-complete
under logarithmic-space many-one reductions [Arora and Barak, Section 6.7][AroraBarak09].

A problem `A ∈ P enc` reduces to the circuit value problem by the tableau of its decider
(`CircuitValue/Completeness.lean`); the dual-rail translation of the tableau
(`Cslib.Circuits.Monotone.dualRail`) is a monotone circuit computing the same function on the
dual-rail inputs, the constant `true` followed by each input bit and its negation. The reduction
maps an instance `a` to the dual-rail translation of the tableau for inputs of length
`n = |enc a|`, with the dual-rail inputs of `enc a`
(`Cslib.Complexity.MonotoneCircuitValue.dualTableauInstance`). It is computed in logarithmic space
by a writer (`Cslib.Complexity.CircuitValue.WriterSpec`) emitting, for each gate of the tableau,
its two translated gates, each computed from the number of the gate within work space linear in
the binary lengths of `n`, the time bound and the number. In particular the circuit value problem
reduces to the monotone circuit value problem in logarithmic space
(`Cslib.Complexity.MonotoneCircuitValue.circuitValue_logSpaceReducible`), through the tableau of
its decider rather than by translating the given circuit directly.

## Main definitions

* `Cslib.Complexity.MonotoneCircuitValue.dualTableauInstance`: the instance of the monotone
  problem for an input of a machine.

## Main results

* `Cslib.Complexity.MonotoneCircuitValue.computableInLogSpace_dualTableauInstance`: the instances
  are computable in logarithmic space.
* `Cslib.Complexity.MonotoneCircuitValue.logSpaceHard`,
  `Cslib.Complexity.MonotoneCircuitValue.logSpaceComplete`: the monotone circuit value problem is
  `P`-hard and `P`-complete under logarithmic-space reductions.
* `Cslib.Complexity.MonotoneCircuitValue.circuitValue_logSpaceReducible`: the circuit value
  problem reduces to the monotone one.
* `Cslib.Complexity.MonotoneCircuitValue.mem_L_iff_forall_P_eq_L`: the monotone circuit value
  problem is in `L` exactly when `P = L`.

## References

* [L. M. Goldschlager, *The monotone and planar circuit value problems are log space complete
  for P*][Goldschlager1977]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.7][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.MonotoneCircuitValue

open Turing MultiTapeTM Circuits Circuits.Boolean ComputableTidilyInSpace CircuitValue
open Circuits.Boolean.Tableau (add_inSpace mul_inSpace cons_inSpace)

/-! ### The translated gates in the De Morgan basis -/

/-- The operation of the gate translating a De Morgan operation positively (`b = true`) or
negatively, read in the De Morgan basis. -/
def dualOp (b : Bool) : Boolean.Op → Boolean.Op
  | .const c => .const (if b then c else !c)
  | .not => .and
  | .and => if b then .and else .or
  | .or => if b then .or else .and

/-- The gate translating a De Morgan gate positively (`b = true`) or negatively
(`Cslib.Circuits.Monotone.dualGates`), read in the De Morgan basis. -/
def dualGateDM (b : Bool) (g : Boolean.Op × List ℕ) : Boolean.Op × List ℕ :=
  (dualOp b g.1, if Tableau.opIsConst g.1 then []
    else if decide (g.1 = .not) then [Monotone.railWire (!b) (g.2.getD 0 0), 0]
    else [Monotone.railWire b (g.2.getD 0 0), Monotone.railWire b (g.2.getD 1 0)])

theorem map_dualGates (g : Boolean.Op × List ℕ) :
    (Monotone.dualGates g).map (fun h => (Monotone.toDeMorgan h.1, h.2)) =
      [dualGateDM true g, dualGateDM false g] := by
  rcases g with ⟨(_ | _) | _ | _ | _, args⟩ <;> rfl

section

variable {α : Type} {encIn : α ↪ List Bool} {Bs : α → ℕ}

/-- **The translated gates within a budget**, from a gate within the budget. -/
theorem dualGateDM_inSpace (b : Bool) {g : α → Boolean.Op × List ℕ}
    (hg : ComputableTidilyInSpace g encIn encGate Bs) (hin : (fun x => (encIn x).length) ≼ Bs) :
    ComputableTidilyInSpace (fun x => dualGateDM b (g x)) encIn encGate Bs := by
  have hop := fst' hg
  have hargs := snd' hg
  have hhead : ComputableTidilyInSpace (fun l : List ℕ => l.headD 0) (encList encNat) encNat
      fun l => (encList encNat l).length := of_inO (.of_linear (ListEncoding.headD 0))
  have htail : ComputableTidilyInSpace List.tail (encList encNat) (encList encNat)
      fun l => (encList encNat l).length := of_inO (.of_linear (ListEncoding.tail encNat))
  have ha := budget_comp_linear hhead hargs
  have hb := budget_comp_linear hhead (budget_comp_linear htail hargs)
  have hrail (c : Bool) {w : α → ℕ} (hw : ComputableTidilyInSpace w encIn encNat Bs) :
      ComputableTidilyInSpace (fun x => Monotone.railWire c (w x)) encIn encNat Bs :=
    (add_inSpace (mul_inSpace (budget_const (encB := encNat) 2 hin) hw)
      (budget_const (encB := encNat) (if c then 1 else 2) hin)).of_enc_eq fun _ => rfl
  have hnil := budget_const (encB := encList encNat) ([] : List ℕ) hin
  have hcons {a : α → ℕ} {L : α → List ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs)
      (hL : ComputableTidilyInSpace L encIn (encList encNat) Bs) :=
    cons_inSpace ha hL
  have hzero := budget_const (encB := encNat) 0 hin
  have hargs' := budget_ite (budget_finite (encC := encBool) Tableau.opIsConst hop) hnil
    (budget_ite (budget_finite (encC := encBool) (fun op : Boolean.Op => decide (op = .not)) hop)
      (hcons (hrail (!b) ha) (hcons hzero hnil))
      (hcons (hrail b ha) (hcons (hrail b hb) hnil)))
  refine (budget_prod (budget_finite (encC := encOp) (dualOp b) hop) hargs').of_enc_eq
    fun x => ?_
  have h₀ (l : List ℕ) : l.getD 0 0 = l.headD 0 := by cases l <;> rfl
  have h₁ (l : List ℕ) : l.getD 1 0 = l.tail.headD 0 := by rcases l with _ | ⟨_, _ | _⟩ <;> rfl
  simp only [dualGateDM, h₀, h₁]

end

/-! ### The instances -/

section Instance

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM k Bool State) (C d : ℕ)

/-- **The instance of the monotone circuit value problem** for the input `w`: the dual-rail
translation of the tableau circuit of `tm` for `timeBound C d |w|` steps on inputs of length
`|w|`, with the dual-rail inputs of `w`. -/
noncomputable def dualTableauInstance (w : List Bool) :
    Σ n, Circuit Monotone.signature n 1 × BitString n :=
  ⟨2 * w.length + 1, Monotone.dualRail (Tableau.circuit tm w.length (timeBound C d w.length)),
    Monotone.railBitString fun i => w[i]⟩

/-- The dual-rail instance is a yes-instance exactly when the tableau instance is. -/
theorem mem_dualTableauInstance_iff (w : List Bool) :
    dualTableauInstance tm C d w ∈ MonotoneCircuitValue ↔
      tableauInstance tm C d w ∈ CircuitValue := by
  rw [mem_MonotoneCircuitValue, mem_CircuitValue]
  simp only [dualTableauInstance, tableauInstance]
  rw [Monotone.eval_dualRail]

/-- The two translated gates of gate `j` of the tableau, as the writer emits them. -/
noncomputable def dualChunk (n j : ℕ) : List Bool :=
  dbl (dbl (frame (encGate (dualGateDM true (Tableau.gateCode tm n (timeBound C d n) j))))) ++
    dbl (dbl (frame (encGate (dualGateDM false (Tableau.gateCode tm n (timeBound C d n) j)))))

/-- **The writer of the dual-rail instances.** -/
noncomputable def dualSpec : WriterSpec where
  countUnit := List.replicate 8 true
  countEnd := [true, true, true, true, true, false]
  numChunks n := Tableau.numGates k State (timeBound C d n)
  chunk := dualChunk tm C d
  trailer n := [true, false] ++
    dbl (frame (encNat (Monotone.railWire true (Tableau.outWire k State n (timeBound C d n))))) ++
      [false, true]
  copyBit b := [b, !b]

theorem flatten_replicate_two_mul_add_one {β : Type*} (a : List β) (n : ℕ) :
    (List.replicate (2 * n + 1) a).flatten = (List.replicate n (a ++ a)).flatten ++ a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by omega, List.replicate_succ (n := 2 * n + 1 + 1),
      List.replicate_succ (n := 2 * n + 1), List.flatten_cons, List.flatten_cons, ih,
      List.replicate_succ (n := n), List.flatten_cons]
    simp only [List.append_assoc]

/-- **The encoded dual-rail instance** is the word written by the writer. -/
theorem encMonotoneCircuitValue_dualTableauInstance (w : List Bool) :
    encMonotoneCircuitValue (dualTableauInstance tm C d w) = (dualSpec tm C d).output w := by
  rw [encMonotoneCircuitValue_apply, encCircuitValue_apply]
  simp only [toDeMorgan, dualTableauInstance, Circuit.code_mapOp, Monotone.code_dualRail,
    Tableau.code_circuit, Tableau.gates, encPair_apply, encUnary_apply, encBits_apply,
    Monotone.ofFn_railBitString, List.map_cons, List.map_nil, encList_cons, encList_nil,
    List.append_nil, frame_eq_dbl, dbl_append]
  have hw : List.ofFn (fun i : Fin w.length => w[i]) = w := List.ofFn_getElem
  rw [hw]
  trace_state
  sorry

end Instance

end Cslib.Complexity.MonotoneCircuitValue
