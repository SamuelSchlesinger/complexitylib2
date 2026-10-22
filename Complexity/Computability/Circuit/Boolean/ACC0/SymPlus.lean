/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.ACC0.Basic
public import Complexity.Foundations.Data.BitString.Zeta

/-!
# Depth-two `Sym⁺` (`Sym ∘ AND`) circuits and Williams's fast multipoint evaluation

A `SymPlusCircuit n s` (`Sym⁺` / `Sym ∘ AND` circuit) evaluates a symmetric function
`sym : ℕ → Bool` on the number `activeCount` of satisfied positive conjunction masks
`masks : Fin s → BitString n` [Yao1990], [BeigelTarui1994], [Williams2014].

Splitting the `n = n₁ + n₂` input variables factors each mask into left and right sub-masks
(`BitString.evalMask_append`), expressing `C.activeCount (Fin.append x₁ x₂)` as the Boolean-lattice
Zeta transform `BitString.zetaTransform (C.coeffTable x₂) x₁` of a `2 ^ n₁`-entry coefficient table
accumulated from `x₂` (`SymPlusCircuit.zetaTransform_coeffTable_eq_activeCount`). Applying the
divide-and-conquer Fast Zeta Transform (`BitString.fastZeta`) evaluates `C` on all `2 ^ (n₁ + n₂)`
inputs (`SymPlusCircuit.fastSymPlusEval_eq_eval`) and characterizes satisfiability
(`SymPlusCircuit.isSatisfiable_iff_exists_fastSymPlusEval`).

## Main definitions

* `Cslib.Circuits.Boolean.SymPlusCircuit`: depth-two `Sym ∘ AND` circuits.
* `Cslib.Circuits.Boolean.SymPlusCircuit.coeffTable`,
  `Cslib.Circuits.Boolean.SymPlusCircuit.fastSymPlusEval`: split-variable coefficient table and
  fast multipoint evaluation of a `Sym⁺` circuit.

## Main results

* `Cslib.Circuits.Boolean.SymPlusCircuit.zetaTransform_coeffTable_eq_activeCount`: bilinear
  Zeta-transform identity for `Sym⁺` circuits.
* `Cslib.Circuits.Boolean.SymPlusCircuit.fastSymPlusEval_eq_eval`,
  `Cslib.Circuits.Boolean.SymPlusCircuit.isSatisfiable_iff_exists_fastSymPlusEval`: correctness of
  Williams's fast `Sym⁺` evaluation.

## References

* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
* [A. C.-C. Yao, *On ACC and threshold circuits*][Yao1990]
* [R. Beigel, J. Tarui, *On ACC*][BeigelTarui1994]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Set Finset BitString Unbounded

/-- **A depth-two `Sym⁺` (`Sym ∘ AND`) circuit** on `n` Boolean inputs with `s` positive
conjunction gates [Yao1990], [BeigelTarui1994], [Williams2014]: consists of `s` conjunction masks
`masks : Fin s → BitString n` and a symmetric output function `sym : ℕ → Bool` applied to the
number of satisfied conjunctions. -/
structure SymPlusCircuit (n s : ℕ) where
  /-- The `s` positive conjunction masks. -/
  masks : Fin s → BitString n
  /-- The symmetric output gate on the count of satisfied masks in `{0, …, s}`. -/
  sym : ℕ → Bool

namespace SymPlusCircuit

variable {n n₁ n₂ s : ℕ}

/-- The number of conjunction gates of `C` satisfied by `x`. -/
def activeCount (C : SymPlusCircuit n s) (x : BitString n) : ℕ :=
  ∑ j : Fin s, if BitString.evalMask (C.masks j) x then 1 else 0

theorem activeCount_eq_card_filter (C : SymPlusCircuit n s) (x : BitString n) :
    C.activeCount x = #(univ.filter fun j : Fin s => BitString.evalMask (C.masks j) x = true) := by
  rw [activeCount, Finset.card_filter]

theorem activeCount_le (C : SymPlusCircuit n s) (x : BitString n) :
    C.activeCount x ≤ s := by
  rw [activeCount_eq_card_filter]
  exact (card_filter_le _ _).trans_eq (by simp)

/-- Evaluation of a `Sym⁺` circuit on input `x : BitString n`. -/
def eval (C : SymPlusCircuit n s) (x : BitString n) : Bool :=
  C.sym (C.activeCount x)

/-- `C` computes the Boolean function `f : BitString n → Bool`. -/
def Computes (C : SymPlusCircuit n s) (f : BitString n → Bool) : Prop :=
  ∀ x : BitString n, C.eval x = f x

/-- Whether `C` is satisfiable on `{0, 1} ^ n`. -/
def IsSatisfiable (C : SymPlusCircuit n s) : Prop :=
  ∃ x : BitString n, C.eval x = true

/-- Negating a `Sym⁺` circuit by negating its outer symmetric lookup table. -/
def not (C : SymPlusCircuit n s) : SymPlusCircuit n s where
  masks := C.masks
  sym := fun w => !C.sym w

@[simp] theorem eval_not (C : SymPlusCircuit n s) (x : BitString n) :
    C.not.eval x = !C.eval x :=
  rfl

/-- A constant `b : Bool` as a `Sym⁺` circuit with `0` conjunctions. -/
def ofConst (n : ℕ) (b : Bool) : SymPlusCircuit n 0 where
  masks := Fin.elim0
  sym := fun _ => b

@[simp] theorem eval_ofConst (n : ℕ) (b : Bool) (x : BitString n) :
    (ofConst n b).eval x = b :=
  rfl

/-- An `n`-ary conjunction `.and n` as a `Sym⁺` circuit with `1` mask. -/
def ofAnd (n : ℕ) : SymPlusCircuit n 1 where
  masks := fun _ _ => true
  sym := fun w => decide (w = 1)

@[simp] theorem eval_ofAnd (n : ℕ) (x : BitString n) :
    (ofAnd n).eval x = Unbounded.interpretation (.and n) x := by
  simp [ofAnd, eval, activeCount, BitString.evalMask]

/-- The `j`-th singleton mask, reading only input coordinate `j`. -/
def singleMask (n : ℕ) (j : Fin n) : BitString n :=
  fun i => decide (i = j)

@[simp] theorem evalMask_singleMask (n : ℕ) (j : Fin n) (x : BitString n) :
    BitString.evalMask (singleMask n j) x = x j := by
  rw [Bool.eq_iff_iff, BitString.evalMask_eq_true_iff]
  simp [singleMask]

theorem activeCount_singleMask {sym : ℕ → Bool} (x : BitString n) :
    activeCount ⟨singleMask n, sym⟩ x = BitString.weight x := by
  rw [activeCount_eq_card_filter]
  simp only [evalMask_singleMask]
  rfl

/-- Any symmetric gate `g : ℕ → Bool` of the Hamming weight on `n` bits is computed by a `Sym⁺`
circuit with `n` singleton masks. -/
def ofSymmetric (n : ℕ) (g : ℕ → Bool) : SymPlusCircuit n n where
  masks := singleMask n
  sym := g

@[simp] theorem eval_ofSymmetric (n : ℕ) (g : ℕ → Bool) (x : BitString n) :
    (ofSymmetric n g).eval x = g (BitString.weight x) := by
  simp [ofSymmetric, eval, activeCount_singleMask]

/-- `modGate q n` as a `Sym⁺` circuit of size `n`. -/
def ofModGate (q n : ℕ) : SymPlusCircuit n n :=
  ofSymmetric n fun w => decide (w % q ≠ 0)

@[simp] theorem eval_ofModGate (q n : ℕ) (x : BitString n) :
    (ofModGate q n).eval x = modGate q n x := by
  rw [ofModGate, eval_ofSymmetric, modGate_eq_modCount, modCount]

/-- Unbounded disjunction `.or n` as a `Sym⁺` circuit of size `n`. -/
def ofOr (n : ℕ) : SymPlusCircuit n n :=
  ofSymmetric n fun w => decide (w ≠ 0)

@[simp] theorem eval_ofOr (n : ℕ) (x : BitString n) :
    (ofOr n).eval x = Unbounded.interpretation (.or n) x := by
  rw [ofOr, eval_ofSymmetric, ← modGate_zero, modGate_eq_modCount, modCount, Nat.mod_zero]

/-- Input projection `fun x => x i` as a `Sym⁺` circuit with `1` singleton mask. -/
def ofProj (n : ℕ) (i : Fin n) : SymPlusCircuit n 1 where
  masks := fun _ => singleMask n i
  sym := fun w => decide (w = 1)

@[simp] theorem eval_ofProj (n : ℕ) (i : Fin n) (x : BitString n) :
    (ofProj n i).eval x = x i := by
  simp [ofProj, eval, activeCount]

/-- Push a conjunction mask `p : BitString m` forward along a wire map `w : Fin m → Fin n`:
coordinate `i : Fin n` is required to be `true` iff some wire `j : Fin m` with `p j = true`
reads input `w j = i`. -/
def pullMask {m n : ℕ} (w : Fin m → Fin n) (p : BitString m) : BitString n :=
  fun i => decide (∃ j : Fin m, p j = true ∧ w j = i)

@[simp] theorem evalMask_pullMask {m n : ℕ} (w : Fin m → Fin n) (p : BitString m)
    (x : BitString n) :
    BitString.evalMask (pullMask w p) x = BitString.evalMask p (x ∘ w) := by
  rw [Bool.eq_iff_iff, BitString.evalMask_eq_true_iff, BitString.evalMask_eq_true_iff]
  simp only [pullMask, decide_eq_true_eq, Function.comp_apply, forall_exists_index, and_imp]
  exact ⟨fun h j hj => h (w j) j hj rfl, fun h i j hj hij => hij ▸ h j hj⟩

/-- Precompose a `Sym⁺` circuit `C : SymPlusCircuit m s` with an input wiring `w : Fin m → Fin n`
without increasing the number of conjunction gates `s`. -/
def comap {m n s : ℕ} (C : SymPlusCircuit m s) (w : Fin m → Fin n) : SymPlusCircuit n s where
  masks := fun j => pullMask w (C.masks j)
  sym := C.sym

@[simp] theorem activeCount_comap {m n s : ℕ} (C : SymPlusCircuit m s) (w : Fin m → Fin n)
    (x : BitString n) :
    (C.comap w).activeCount x = C.activeCount (x ∘ w) := by
  simp [comap, activeCount]

@[simp] theorem eval_comap {m n s : ℕ} (C : SymPlusCircuit m s) (w : Fin m → Fin n)
    (x : BitString n) :
    (C.comap w).eval x = C.eval (x ∘ w) := by
  rw [eval, activeCount_comap, eval]
  rfl

/-- Size of the `Sym⁺` circuit representing a single `AC⁰[q]` operation `op`. -/
def extOpSize : ExtOp → ℕ
  | .ac .not => 1
  | .ac (.and _) => 1
  | .ac (.or m) => m
  | .gate m => m

/-- Every single gate `op : ExtOp` of the `AC⁰[q]` basis is computed by a `Sym⁺` circuit of size
`extOpSize op`. -/
def ofExtOp (q : ℕ) : (op : ExtOp) → SymPlusCircuit (extSignature.Arity op) (extOpSize op)
  | .ac .not => (ofAnd 1).not
  | .ac (.and m) => ofAnd m
  | .ac (.or m) => ofOr m
  | .gate m => ofModGate q m

@[simp] theorem eval_ofExtOp (q : ℕ) (op : ExtOp) (x : BitString (extSignature.Arity op)) :
    (ofExtOp q op).eval x = extInterpretation (modGate q) op x := by
  cases op with
  | ac op =>
    cases op with
    | not =>
      change (!(ofAnd 1).eval x) = Unbounded.interpretation .not x
      rw [eval_ofAnd]
      simp [Unbounded.interpretation]
    | and m => exact eval_ofAnd m x
    | or m => exact eval_ofOr m x
  | gate m => exact eval_ofModGate q m x

/-- Every single-gate `AC⁰[q]` circuit `Circuit.oneGate op w` is computed by the `Sym⁺` circuit
`(ofExtOp q op).comap w` of size `extOpSize op`. -/
theorem eval_ofExtOp_comap (q : ℕ) (op : ExtOp) {n : ℕ}
    (w : Fin (extSignature.Arity op) → Fin n) (x : BitString n) :
    ((ofExtOp q op).comap w).eval x =
      (Circuit.oneGate (σ := extSignature) op w).eval (extInterpretation (modGate q)) x 0 := by
  rw [eval_comap, eval_ofExtOp, Circuit.eval_oneGate]
  rfl

/-! ### Variable splitting and Williams's fast `Sym⁺` evaluation -/

/-- The left `n₁`-bit submask of the `j`-th conjunction mask of
`C : SymPlusCircuit (n₁ + n₂) s`. -/
def leftMask (C : SymPlusCircuit (n₁ + n₂) s) (j : Fin s) : BitString n₁ :=
  fun i => C.masks j (Fin.castAdd n₂ i)

/-- The right `n₂`-bit submask of the `j`-th conjunction mask of
`C : SymPlusCircuit (n₁ + n₂) s`. -/
def rightMask (C : SymPlusCircuit (n₁ + n₂) s) (j : Fin s) : BitString n₂ :=
  fun i => C.masks j (Fin.natAdd n₁ i)

/-- **Williams's partial-evaluation coefficient table** [Williams, Section 3.2][Williams2014]:
for a right half-assignment `x₂ : BitString n₂` and a left pattern `p : BitString n₁`, counts how
many gates `j : Fin s` have left mask `p` and are satisfied on the right by `x₂`. The table has
`2 ^ n₁` entries regardless of the circuit size `s`. -/
def coeffTable (C : SymPlusCircuit (n₁ + n₂) s) (x₂ : BitString n₂) (p : BitString n₁) : ℕ :=
  ∑ j : Fin s, if C.leftMask j = p && BitString.evalMask (C.rightMask j) x₂ then 1 else 0

/-- **Bilinear Zeta-transform identity for `Sym⁺` circuits**: the Zeta transform of
`C.coeffTable x₂` at `x₁` equals `C.activeCount (Fin.append x₁ x₂)`. -/
theorem zetaTransform_coeffTable_eq_activeCount (C : SymPlusCircuit (n₁ + n₂) s)
    (x₁ : BitString n₁) (x₂ : BitString n₂) :
    BitString.zetaTransform (C.coeffTable x₂) x₁ = C.activeCount (Fin.append x₁ x₂) := by
  simp only [BitString.zetaTransform, coeffTable, activeCount]
  have hite (p : BitString n₁) :
      (if BitString.evalMask p x₁ = true then
        ∑ j : Fin s,
          (if (C.leftMask j = p && BitString.evalMask (C.rightMask j) x₂) = true then 1 else 0)
      else 0) =
      ∑ j : Fin s,
        if BitString.evalMask p x₁ = true then
          (if (C.leftMask j = p && BitString.evalMask (C.rightMask j) x₂) = true then 1 else 0)
        else 0 := by
    split_ifs <;> simp
  simp_rw [hite]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_eq_single (C.leftMask j)]
  · rw [BitString.evalMask_append]
    change (if BitString.evalMask (C.leftMask j) x₁ = true then
        if (decide (C.leftMask j = C.leftMask j) &&
            BitString.evalMask (C.rightMask j) x₂) = true then
          1
        else 0
      else 0) =
      if (BitString.evalMask (C.leftMask j) x₁ &&
          BitString.evalMask (C.rightMask j) x₂) = true then 1 else 0
    cases BitString.evalMask (C.leftMask j) x₁ <;>
      cases BitString.evalMask (C.rightMask j) x₂ <;> simp
  · intro p hp
    simp [hp.symm]

/-- **Fast multipoint evaluation of a `Sym⁺` circuit** [Williams, Theorem 3.2][Williams2014]:
evaluates `C` on `(x₁, x₂)` by applying the Fast Zeta Transform `fastZeta` to the coefficient
table `C.coeffTable x₂` and looking up the result in `C.sym`. -/
def fastSymPlusEval (C : SymPlusCircuit (n₁ + n₂) s)
    (x₁ : BitString n₁) (x₂ : BitString n₂) : Bool :=
  C.sym (BitString.fastZeta (C.coeffTable x₂) x₁)

/-- **Correctness of `fastSymPlusEval`**: `fastSymPlusEval` agrees with `C.eval` on every split
assignment `Fin.append x₁ x₂`. -/
@[simp] theorem fastSymPlusEval_eq_eval (C : SymPlusCircuit (n₁ + n₂) s)
    (x₁ : BitString n₁) (x₂ : BitString n₂) :
    C.fastSymPlusEval x₁ x₂ = C.eval (Fin.append x₁ x₂) := by
  rw [fastSymPlusEval, BitString.fastZeta_eq_zetaTransform,
    zetaTransform_coeffTable_eq_activeCount, eval]

/-- **Satisfiability of a `Sym⁺` circuit via `fastSymPlusEval`**: `C` is satisfiable on
`{0, 1} ^ (n₁ + n₂)` iff `C.fastSymPlusEval x₁ x₂ = true` for some `x₁ : BitString n₁` and
`x₂ : BitString n₂`. -/
theorem isSatisfiable_iff_exists_fastSymPlusEval (C : SymPlusCircuit (n₁ + n₂) s) :
    C.IsSatisfiable ↔ ∃ (x₁ : BitString n₁) (x₂ : BitString n₂),
      C.fastSymPlusEval x₁ x₂ = true := by
  simp only [IsSatisfiable, fastSymPlusEval_eq_eval]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun i => x (Fin.castAdd n₂ i), fun i => x (Fin.natAdd n₁ i), ?_⟩
    convert hx using 2
    funext k
    refine Fin.addCases (fun i => by simp [Fin.append_left])
      (fun i => by simp [Fin.append_right]) k
  · rintro ⟨x₁, x₂, h⟩
    exact ⟨Fin.append x₁ x₂, h⟩

end SymPlusCircuit

@[deprecated (since := "2026-10-22")] alias evalMask := Cslib.BitString.evalMask
@[deprecated (since := "2026-10-22")] alias evalMask_eq_true_iff :=
  Cslib.BitString.evalMask_eq_true_iff
@[deprecated (since := "2026-10-22")] alias evalMask_false := Cslib.BitString.evalMask_false
@[deprecated (since := "2026-10-22")] alias evalMask_self := Cslib.BitString.evalMask_self
@[deprecated (since := "2026-10-22")] alias evalMask_cons_false :=
  Cslib.BitString.evalMask_cons_false
@[deprecated (since := "2026-10-22")] alias evalMask_cons_true := Cslib.BitString.evalMask_cons_true
@[deprecated (since := "2026-10-22")] alias evalMask_append := Cslib.BitString.evalMask_append
@[deprecated (since := "2026-10-22")] alias zetaTransform := Cslib.BitString.zetaTransform
@[deprecated (since := "2026-10-22")] alias fastZeta := Cslib.BitString.fastZeta
@[deprecated (since := "2026-10-22")] alias fastZeta_eq_zetaTransform :=
  Cslib.BitString.fastZeta_eq_zetaTransform

end Cslib.Circuits.Boolean
