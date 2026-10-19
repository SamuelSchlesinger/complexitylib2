/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Boolean.Complexity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.InformationTheory.Hamming
import Complexity.Computability.Circuit.Boolean.SparseSynthesis

/-!
# The modulus of continuity of circuit complexity

Over a finite carrier `U` and a complete interpretation `I`, the *modulus of continuity* of circuit
complexity, `ω_{I,n,m}(r)` (`Cslib.Circuits.complexityModulus`), is the largest change
`|C_I(f) - C_I(g)|` in the complexity of two functions with `n` inputs and `m` outputs that differ
on at most `r` inputs, that is, at Hamming distance at most `r` as functions of their inputs. It is
a natural number, it is attained (`Cslib.Circuits.exists_dist_complexity_eq_complexityModulus`), it
increases with `r` and vanishes at `r = 0`, and it is subadditive,
`ω(r + s) ≤ ω(r) + ω(s)` (`Cslib.Circuits.complexityModulus_add_le`): a change on `r + s` inputs
is a change on `r` inputs followed by a change on `s` inputs. In particular `ω(r) ≤ r ω(1)`.

For the De Morgan basis on `n = 2 p` inputs, the sparse synthesis bounds of
`Complexity.Computability.Circuit.Boolean.SparseSynthesis` locate the modulus at the square root
`2 ^ p` of the number of inputs: for every `ε > 0` and all large `p`,

* `ω_{2p,1}(2 ^ p) ≤ (1 + ε) 2 ^ p` for a single output
  (`Cslib.Circuits.Boolean.complexityModulus_one_le`);
* `ω_{2p,m}(2 ^ p) ≤ (3 + ε) 2 ^ p` for `m ≤ 2 p` outputs
  (`Cslib.Circuits.Boolean.complexityModulus_le`);
* `2 ^ p ≤ 16 ω_{2p,1}(2 ^ p)` for `p ≥ 4`, so the order `2 ^ p` is optimal
  (`Cslib.Circuits.Boolean.two_pow_le_sixteen_mul_complexityModulus`).

These restate `Cslib.Circuits.Boolean.SparseSynthesis.dist_complexity_single_le`,
`Cslib.Circuits.Boolean.SparseSynthesis.dist_complexity_le` and
`Cslib.Circuits.Boolean.SparseSynthesis.exists_hammingDist_eq_le_dist_complexity` in terms of the
modulus.

## Main definitions

* `Cslib.Circuits.complexityModulus`: the modulus of continuity of circuit complexity.

## Main results

* `Cslib.Circuits.dist_complexity_le_complexityModulus`,
  `Cslib.Circuits.complexityModulus_le_iff`,
  `Cslib.Circuits.exists_dist_complexity_eq_complexityModulus`: the modulus is the least bound and
  is attained.
* `Cslib.Circuits.complexityModulus_mono`, `Cslib.Circuits.complexityModulus_zero`,
  `Cslib.Circuits.complexityModulus_add_le`, `Cslib.Circuits.complexityModulus_le_mul`: monotone,
  zero at zero, subadditive.
* `Cslib.Circuits.Boolean.complexityModulus_one_le`, `Cslib.Circuits.Boolean.complexityModulus_le`,
  `Cslib.Circuits.Boolean.two_pow_le_sixteen_mul_complexityModulus`: square-root continuity for
  the De Morgan basis, and its optimality.

## References

* [A. V. Chashkin, *On computing partial Boolean functions*][Chashkin2024]
-/

@[expose] public section

namespace Cslib.Circuits

open Finset

variable {σ : Signature} {U : Type*} [Fintype U] [DecidableEq U] (I : Interpretation σ U)
  [I.IsComplete] {n m r s : ℕ}

/-- The **modulus of continuity** `ω_{I,n,m}(r)` of circuit complexity: the largest change
`|C_I(f) - C_I(g)|` in the complexity of two functions with `n` inputs and `m` outputs over a
finite carrier `U` that differ on at most `r` inputs. -/
noncomputable def complexityModulus (n m r : ℕ) : ℕ :=
  ((univ : Finset (((Fin n → U) → Fin m → U) × ((Fin n → U) → Fin m → U))).filter
    fun fg => hammingDist fg.1 fg.2 ≤ r).sup fun fg =>
      Nat.dist (complexity I fg.1) (complexity I fg.2)

variable {I}

/-- Functions that differ on at most `r` inputs have complexities at most `ω(r)` apart. -/
theorem dist_complexity_le_complexityModulus {f g : (Fin n → U) → Fin m → U}
    (h : hammingDist f g ≤ r) :
    Nat.dist (complexity I f) (complexity I g) ≤ complexityModulus I n m r :=
  le_sup (f := fun fg : ((Fin n → U) → Fin m → U) × ((Fin n → U) → Fin m → U) =>
    Nat.dist (complexity I fg.1) (complexity I fg.2)) (mem_filter.2 ⟨mem_univ (f, g), h⟩)

/-- The modulus is the least bound on the change in complexity over changes on at most `r`
inputs. -/
theorem complexityModulus_le_iff {k : ℕ} :
    complexityModulus I n m r ≤ k ↔ ∀ f g : (Fin n → U) → Fin m → U, hammingDist f g ≤ r →
      Nat.dist (complexity I f) (complexity I g) ≤ k := by
  simp only [complexityModulus, Finset.sup_le_iff, mem_filter, mem_univ, true_and, Prod.forall]

/-- **The modulus is attained.** -/
theorem exists_dist_complexity_eq_complexityModulus [Nonempty U] :
    ∃ f g : (Fin n → U) → Fin m → U, hammingDist f g ≤ r ∧
      Nat.dist (complexity I f) (complexity I g) = complexityModulus I n m r := by
  have hne : ((univ : Finset (((Fin n → U) → Fin m → U) × ((Fin n → U) → Fin m → U))).filter
      fun fg => hammingDist fg.1 fg.2 ≤ r).Nonempty :=
    ⟨(fun _ _ => Classical.arbitrary U, fun _ _ => Classical.arbitrary U), by simp⟩
  obtain ⟨⟨f, g⟩, hfg, heq⟩ := exists_mem_eq_sup _ hne fun fg =>
    Nat.dist (complexity I fg.1) (complexity I fg.2)
  exact ⟨f, g, (mem_filter.1 hfg).2, heq.symm⟩

/-- The modulus increases with the number of changed inputs. -/
theorem complexityModulus_mono : Monotone (complexityModulus I n m) := fun _ _ hrs =>
  complexityModulus_le_iff.2 fun _ _ h => dist_complexity_le_complexityModulus (h.trans hrs)

/-- Changing no input does not change the complexity. -/
@[simp] theorem complexityModulus_zero : complexityModulus I n m 0 = 0 :=
  Nat.le_zero.1 <| complexityModulus_le_iff.2 fun f g h => by
    rw [Nat.le_zero, hammingDist_eq_zero] at h
    rw [h, Nat.dist_self]

/-- A change on at most `r + s` inputs is a change on at most `r` inputs followed by a change on
at most `s` inputs. -/
private theorem exists_hammingDist_le_le {f g : (Fin n → U) → Fin m → U}
    (h : hammingDist f g ≤ r + s) :
    ∃ k, hammingDist f k ≤ r ∧ hammingDist k g ≤ s := by
  classical
  set D := univ.filter fun x => f x ≠ g x
  obtain ⟨A, hAD, hA⟩ := exists_subset_card_eq (min_le_right r #D)
  refine ⟨fun x => if x ∈ A then g x else f x, ?_, ?_⟩
  · have hfilter : (univ.filter fun x => f x ≠ if x ∈ A then g x else f x) = A := by
      ext x
      by_cases hx : x ∈ A
      · simpa [hx] using (mem_filter.1 (hAD hx)).2
      · simp [hx]
    rw [hammingDist, hfilter, hA]
    exact min_le_left _ _
  · have hfilter : (univ.filter fun x => (if x ∈ A then g x else f x) ≠ g x) = D \ A := by
      ext x
      by_cases hx : x ∈ A <;> simp [hx, D]
    have hD : #D ≤ r + s := h
    rw [hammingDist, hfilter, card_sdiff_of_subset hAD, hA]
    omega

/-- **The modulus is subadditive**: `ω(r + s) ≤ ω(r) + ω(s)`. -/
theorem complexityModulus_add_le :
    complexityModulus I n m (r + s) ≤ complexityModulus I n m r + complexityModulus I n m s :=
  complexityModulus_le_iff.2 fun _ _ h => by
    obtain ⟨k, hfk, hkg⟩ := exists_hammingDist_le_le h
    exact (Nat.dist.triangle_inequality _ (complexity I k) _).trans
      (add_le_add (dist_complexity_le_complexityModulus hfk)
        (dist_complexity_le_complexityModulus hkg))

/-- The change in complexity is at most `ω(1)` per changed input. -/
theorem complexityModulus_le_mul : complexityModulus I n m r ≤ r * complexityModulus I n m 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.succ_mul]
    exact (complexityModulus_add_le (r := r) (s := 1)).trans (Nat.add_le_add_right ih _)

end Cslib.Circuits

namespace Cslib.Circuits.Boolean

open Finset

/-- A function with one output is at the Hamming distance of its single values. -/
private theorem hammingDist_single {n : ℕ} (f g : BooleanFunction n) :
    hammingDist (single f) (single g) = hammingDist f g := by
  unfold hammingDist
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, ne_eq]
  exact not_congr ⟨fun h => congrFun h 0, fun h => funext fun _ => h⟩

/-- A function with one output is the single-valued function of its output. -/
private theorem single_apply_zero {n : ℕ} (f : BitString n → Fin 1 → Bool) :
    single (fun x => f x 0) = f :=
  funext fun x => funext fun o => by rw [Subsingleton.elim o 0]; rfl

/-- **Square-root continuity for a single output**: for every `ε > 0` and all large `p`, changing
a Boolean function on at most `2 ^ p` of its `2 ^ (2 p)` inputs changes its De Morgan complexity
by at most `(1 + ε) 2 ^ p`, that is, `ω_{2p,1}(2 ^ p) ≤ (1 + ε) 2 ^ p`. -/
theorem complexityModulus_one_le (ε : ℝ) (hε : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀,
      (complexityModulus interpretation (2 * p) 1 (2 ^ p) : ℝ) ≤ (1 + ε) * 2 ^ p := by
  obtain ⟨p₀, hp₀⟩ := SparseSynthesis.dist_complexity_single_le ε hε
  refine ⟨p₀, fun p hp => ?_⟩
  obtain ⟨f, g, hfg, heq⟩ :=
    exists_dist_complexity_eq_complexityModulus (I := interpretation) (n := 2 * p) (m := 1)
      (r := 2 ^ p)
  rw [← heq, ← single_apply_zero f, ← single_apply_zero g]
  rw [← single_apply_zero f, ← single_apply_zero g, hammingDist_single] at hfg
  exact hp₀ p hp _ _ hfg

/-- **Square-root continuity**: for every `ε > 0` and all large `p`, changing a Boolean function
with at most `2 p` outputs on at most `2 ^ p` of its `2 ^ (2 p)` inputs changes its De Morgan
complexity by at most `(3 + ε) 2 ^ p`, that is, `ω_{2p,m}(2 ^ p) ≤ (3 + ε) 2 ^ p` for
`m ≤ 2 p`. -/
theorem complexityModulus_le (ε : ℝ) (hε : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ m ≤ 2 * p,
      (complexityModulus interpretation (2 * p) m (2 ^ p) : ℝ) ≤ (3 + ε) * 2 ^ p := by
  obtain ⟨p₀, hp₀⟩ := SparseSynthesis.dist_complexity_le ε hε
  refine ⟨p₀, fun p hp m hm => ?_⟩
  obtain ⟨f, g, hfg, heq⟩ :=
    exists_dist_complexity_eq_complexityModulus (I := interpretation) (n := 2 * p) (m := m)
      (r := 2 ^ p)
  rw [← heq]
  exact hp₀ p hp m f g hfg ((hammingDist_le_card_fintype).trans (by simpa using hm))

/-- **Square-root continuity is optimal**: for `p ≥ 4`, `2 ^ p ≤ 16 ω_{2p,1}(2 ^ p)`, witnessed
by a function differing from the constant `false` on exactly `2 ^ p` inputs. -/
theorem two_pow_le_sixteen_mul_complexityModulus {p : ℕ} (hp : 4 ≤ p) :
    2 ^ p ≤ 16 * complexityModulus interpretation (2 * p) 1 (2 ^ p) := by
  obtain ⟨f, hf, hle⟩ := SparseSynthesis.exists_hammingDist_eq_le_dist_complexity hp
  refine hle.trans (Nat.mul_le_mul_left 16 (dist_complexity_le_complexityModulus ?_))
  rw [hammingDist_single, hf]

end Cslib.Circuits.Boolean
