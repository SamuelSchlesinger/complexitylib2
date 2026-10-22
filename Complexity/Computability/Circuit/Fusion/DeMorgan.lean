/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Fusion.Boolean
public import Complexity.Computability.Circuit.Fusion.Quadratic
public import Complexity.Computability.Circuit.Boolean.AltFormula
public import Complexity.Computability.Circuit.Monotone.DualRail
public import Cslib.Computability.Circuit.Boolean.Complexity
import Complexity.Computability.Circuit.MapOp
import Complexity.Computability.Circuit.Monotone.Set
import Complexity.Computability.Circuit.Pi
import Complexity.Computability.Circuit.Simulation
import Mathlib.Data.List.GetD

/-!
# Fusion covers and De Morgan circuit size

The Fusion bounds for Boolean functions are stated for monotone circuits that read positive
and negative literals for free, charging only AND gates. This module transfers them to the
ordinary size of circuits over the De Morgan basis, where negations may occur anywhere and every
gate, constants included, is charged.

Let `ρ(f)` be the pair-cover complexity of the true set of `f` from the true sets of its `2 n`
literals. For the lower bound, the dual-rail translation `Monotone.dualRail` turns a De Morgan
circuit of size `s` into a monotone circuit of size `2 s` on the dual-rail inputs, and these are
obtained from the literals by wiring and one free constant. Its AND gates give `ρ(f) ≤ 2 s`,
for any admissible class of semifilters. For the upper bound, the quadratic compiler turns an
unrestricted `t`-pair cover into a monotone circuit with at most `4 (t + 1)² (2 n + t + 1)` gates;
adding `n` negations for the literals gives a De Morgan circuit. In the same terms, monotone AND
complexity from literals lies between `ρ(f)` and `ρ(f)²`.

The upper bound is cubic in the cover size rather than quadratic, because the compiler's free
unions are now charged. These are formalizations of known correspondences, not new lower bounds.

## Main definitions

* `Cslib.Circuits.Fusion.railCircuit`: the dual-rail inputs from the literals.
* `Cslib.Circuits.Fusion.deMorganLiterals`: the literals in the De Morgan basis.

## Main results

* `Cslib.Circuits.Fusion.andComplexity_bounds`: `ρ(f) ≤ C_∧(f) ≤ ρ(f)²` for monotone AND
  complexity from literals.
* `Cslib.Circuits.Fusion.pairCoverComplexity_le_two_mul_size`: every De Morgan circuit computing
  `f` has at least `ρ(f) / 2` gates.
* `Cslib.Circuits.Fusion.PairCover.exists_computes_size_le`: a `t`-pair cover gives a De Morgan
  circuit of size at most `4 (t + 1)² (2 n + t + 1) + n`.
* `Cslib.Circuits.Fusion.pairCoverComplexity_complexity_bounds`: `ρ(f)` is finite and
  polynomially equivalent to De Morgan circuit complexity.

## References

* [B. P. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and Two-Dimensional Cover
  Problems*][CavalarOliveira2025], Theorem 24, for the quadratic compiler.
* [L. M. Goldschlager, *The monotone and planar circuit value problems are log space complete
  for P*][Goldschlager1977], for the dual-rail translation.
* [A. A. Razborov, *On the method of approximations*][Razborov1989].
-/

@[expose] public section

namespace Cslib.Circuits.Fusion

variable {n : ℕ}

/-! ### Dual-rail inputs from literals -/

/-- Where the dual-rail input `k` is found among the literals followed by the constant `true`:
input `0` is the constant, input `2 i + 1` the literal `x i` and input `2 i + 2` its negation. -/
def railSelect (k : Fin (2 * n + 1)) : Fin (n + n + 1) :=
  if h : k.val = 0 then Fin.natAdd (n + n) 0
  else if (k.val - 1) % 2 = 0 then
    Fin.castAdd 1 (Fin.castAdd n ⟨(k.val - 1) / 2, by have := k.isLt; omega⟩)
  else Fin.castAdd 1 (Fin.natAdd n ⟨(k.val - 1) / 2, by have := k.isLt; omega⟩)

/-- The dual-rail inputs are a selection from the literals and the constant `true`. -/
theorem railBitString_eq (x : BitString n) (k : Fin (2 * n + 1)) :
    Monotone.railBitString x k =
      Fin.append (Boolean.AltFormula.literals x) (fun _ : Fin 1 => true) (railSelect k) := by
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hx (i : ℕ) (hi : i < n) : (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
    rw [List.getD_eq_getElem _ _ (by omega), List.getElem_ofFn]
  rw [Monotone.railBitString, railSelect]
  split_ifs with h0 hpar
  · simp only [h0, Monotone.getD_railBits_zero, Fin.append_right]
  · have h := Monotone.getD_railBits_true (List.ofFn x) (w := (k.val - 1) / 2) (by omega)
    rw [show Monotone.railWire true ((k.val - 1) / 2) = k.val by
      simp only [Monotone.railWire, ite_true]; omega] at h
    rw [h, hx _ (by omega), Fin.append_left, Boolean.AltFormula.literals, Fin.append_left]
  · have h := Monotone.getD_railBits_false (List.ofFn x) (w := (k.val - 1) / 2) (by omega)
    rw [show Monotone.railWire false ((k.val - 1) / 2) = k.val by
      simp only [Monotone.railWire, Bool.false_eq_true, ite_false]; omega] at h
    rw [h, hx _ (by omega), Fin.append_left, Boolean.AltFormula.literals, Fin.append_right]

/-- A monotone circuit producing the dual-rail inputs from the literals, using a single constant
gate and no conjunction. -/
noncomputable def railCircuit (n : ℕ) : Circuit Monotone.signature (n + n) (2 * n + 1) :=
  (Circuit.wiring _ railSelect).comp
    ((Circuit.wiring _ id).append (Monotone.const true : Formula _ (n + n)).toCircuit)

theorem eval_railCircuit (x : BitString n) :
    (railCircuit n).eval Monotone.interpretation (Boolean.AltFormula.literals x) =
      Monotone.railBitString x := by
  funext k
  have hconst : (Monotone.const true : Formula _ (n + n)).toCircuit.eval Monotone.interpretation
      (Boolean.AltFormula.literals x) = fun _ => true := by
    funext j
    rw [Formula.eval_toCircuit, Monotone.eval_const]
  rw [railCircuit, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_wiring, hconst,
    Circuit.eval_wiring, railBitString_eq]
  rfl

@[simp] theorem cost_railCircuit :
    (railCircuit n).program.cost Monotone.andCost = 0 := by
  rw [railCircuit, Circuit.cost_program_comp, Circuit.cost_program_wiring,
    Circuit.cost_program_append, Circuit.cost_program_wiring, Formula.cost_toCircuit]
  simp [Monotone.const]

/-! ### Monotone AND complexity from literals -/

open Boolean in
/-- An unrestricted cover compiles to a monotone circuit computing `f` from its literals. -/
theorem PairCover.computesFrom_toCircuit {f : BooleanFunction n}
    (c : PairCover {x | f x = true} (fun i => {x | AltFormula.literals x i = true})) :
    c.toCircuit.ComputesFrom Monotone.interpretation (fun x (_ : Fin 1) => f x)
      AltFormula.literals :=
  (Monotone.eval_setOf_iff_computesFrom _ _ _).mp c.eval_toCircuit

open Boolean in
/-- **Monotone AND complexity from literals is polynomially equivalent to cover complexity**:
it lies between `ρ(f)` and `ρ(f)²`, with OR gates and constants free. -/
theorem andComplexity_bounds (f : BooleanFunction n) :
    let ρ := pairCoverComplexity {x | f x = true} (fun i => {x | AltFormula.literals x i = true})
    let C := ecomplexityFrom Monotone.interpretation Monotone.andCost (fun x (_ : Fin 1) => f x)
      AltFormula.literals
    ρ ≤ C ∧ C ≤ ρ ^ 2 := by
  refine ⟨pairCoverComplexity_le_ecomplexityFrom_bool AltFormula.literals
    (fun x (_ : Fin 1) => f x) 0, ?_⟩
  by_cases htop : pairCoverComplexity {x | f x = true}
      (fun i => {x | AltFormula.literals x i = true}) = ⊤
  · simp [htop]
  have : Nonempty (PairCover {x | f x = true} (fun i => {x | AltFormula.literals x i = true})) :=
    ENat.iInf_natCast_ne_top.mp htop
  obtain ⟨c, hc⟩ := ENat.exists_eq_iInf (fun c : PairCover {x | f x = true}
    (fun i => {x | AltFormula.literals x i = true}) => (c.pairs.length : ℕ∞))
  refine (ecomplexityFrom_le_of_computesFrom _ c.computesFrom_toCircuit).trans ?_
  rw [pairCoverComplexity, ← hc, PairCover.cost_toCircuit, Nat.cast_pow]

/-! ### De Morgan circuit size -/

open Boolean in
/-- **Fusion lower bound for De Morgan circuits.** Every circuit over the De Morgan basis
computing `f`, with negations anywhere, has at least half as many gates as the cover complexity
of `f` from its literals, for any admissible class of semifilters. -/
theorem pairCoverComplexity_le_two_mul_size {f : BooleanFunction n}
    (c : Circuit Boolean.signature n 1) (hc : c.Computes Boolean.interpretation (single f))
    (admissible : Semifilter ↥({x | f x = true}ᶜ) → Prop := fun _ => True) :
    pairCoverComplexity {x | f x = true} (fun i => {x | AltFormula.literals x i = true})
      admissible ≤ (2 * c.size : ℕ) := by
  let d := (Monotone.dualRail c).comp (railCircuit n)
  have hd : d.ComputesFrom Monotone.interpretation (fun x (_ : Fin 1) => f x)
      AltFormula.literals := fun x => by
    funext o
    rw [Circuit.eval_comp, eval_railCircuit, Monotone.eval_dualRail, hc x, single_apply]
  refine (pairCoverComplexity_le_ecomplexityFrom_bool AltFormula.literals
    (fun x (_ : Fin 1) => f x) 0 admissible).trans
    ((ecomplexityFrom_le_of_computesFrom d hd).trans ?_)
  have hcost := (Monotone.dualRail c).program.cost_le_mul (cost := Monotone.andCost) (b := 1)
    (fun op => by cases op <;> simp [Monotone.andCost])
  have hsize : 1 * (Monotone.dualRail c).size = 2 * c.size := by
    rw [one_mul, Monotone.size_dualRail]
  simp only [d, Circuit.cost_program_comp, cost_railCircuit, zero_add]
  exact_mod_cast hcost.trans_eq hsize

/-- The positive and negative literals (`Boolean.AltFormula.literals`) in the De Morgan basis:
wiring and one negation per variable. -/
def deMorganLiterals (n : ℕ) : Circuit Boolean.signature n (n + n) :=
  (Circuit.wiring _ id).append (Circuit.pi fun i => Circuit.oneGate .not fun _ => i)

theorem eval_deMorganLiterals (x : BitString n) :
    (deMorganLiterals n).eval Boolean.interpretation x = Boolean.AltFormula.literals x := by
  rw [deMorganLiterals, Circuit.eval_append, Circuit.eval_pi]
  rfl

@[simp] theorem size_deMorganLiterals (n : ℕ) : (deMorganLiterals n).size = n := by
  simp [deMorganLiterals]

open Boolean in
/-- **Fusion upper bound for De Morgan circuits.** A `t`-pair cover yields a De Morgan circuit of
at most `4 (t + 1)² (2 n + t + 1) + n` gates computing `f`. -/
theorem PairCover.exists_computes_size_le {f : BooleanFunction n}
    (c : PairCover {x | f x = true} (fun i => {x | AltFormula.literals x i = true})) :
    ∃ d : Circuit Boolean.signature n 1, d.Computes Boolean.interpretation (single f) ∧
      d.size ≤ 4 * (c.pairs.length + 1) ^ 2 * (2 * n + c.pairs.length + 1) + n := by
  refine ⟨(c.toCircuit.mapOp Monotone.toDeMorgan).comp (deMorganLiterals n), fun x => ?_, ?_⟩
  · funext o
    rw [Circuit.eval_comp, eval_deMorganLiterals,
      Circuit.eval_mapOp (I := Monotone.interpretation),
      c.computesFrom_toCircuit x, single_apply]
  · rw [Circuit.size_comp, Circuit.size_mapOp, size_deMorganLiterals, two_mul]
    have := c.size_toCircuit_le
    lia

open Boolean in
/-- **Cover complexity and De Morgan circuit size are polynomially equivalent.** The cover
complexity `t = ρ(f)` of `f` from its literals over unrestricted semifilters is finite, at most
twice the circuit complexity `C(f)` over the De Morgan basis, and
`C(f) ≤ 4 (t + 1)² (2 n + t + 1) + n`. -/
theorem pairCoverComplexity_complexity_bounds (f : BooleanFunction n) :
    ∃ t : ℕ, pairCoverComplexity {x | f x = true}
        (fun i => {x | AltFormula.literals x i = true}) = t ∧
      t ≤ 2 * complexity Boolean.interpretation (single f) ∧
      complexity Boolean.interpretation (single f) ≤ 4 * (t + 1) ^ 2 * (2 * n + t + 1) + n := by
  obtain ⟨c, hc, hsize⟩ :=
    exists_computes_size_eq_complexity (I := Boolean.interpretation) (f := single f)
  have hlow := pairCoverComplexity_le_two_mul_size c hc
  have htop : pairCoverComplexity {x | f x = true}
      (fun i => {x | AltFormula.literals x i = true}) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hlow
  have : Nonempty (PairCover {x | f x = true} (fun i => {x | AltFormula.literals x i = true})) :=
    ENat.iInf_natCast_ne_top.mp htop
  obtain ⟨p, hp⟩ := ENat.exists_eq_iInf (fun c : PairCover {x | f x = true}
    (fun i => {x | AltFormula.literals x i = true}) => (c.pairs.length : ℕ∞))
  refine ⟨p.pairs.length, hp.symm, ?_, ?_⟩
  · rw [← hsize]
    exact_mod_cast hp.trans_le hlow
  · obtain ⟨d, hd, hdsize⟩ := p.exists_computes_size_le
    exact (complexity_le_of_computes d hd).trans hdsize

end Cslib.Circuits.Fusion
