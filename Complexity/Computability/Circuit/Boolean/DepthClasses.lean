/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.ModGates
public import Complexity.Computability.Circuit.Boolean.TC0
public import Cslib.Computability.Circuit.Boolean.Basic

/-!
# The NC, AC and TC hierarchies

`PolylogDepth I i` is the class of languages decided, at every input length `n`, by circuits over
the Boolean basis `I` of polynomially bounded size and depth `O((log n) ^ i)`, with the explicit
envelope `c (⌊log₂ n⌋ + 1) ^ i`. Over the De Morgan basis of fan-in two this is **NCⁱ**, over the
unbounded fan-in basis **ACⁱ**, with majority gates **TCⁱ**, and with `MOD_q` gates **ACⁱ[q]**
[Arora and Barak, Section 6.7][AroraBarak09], [Vollmer, Chapter 4][Vollmer1999]. For `i = 0` these
are the constant-depth classes (`polylogDepth_zero`). Every hierarchy is monotone in `i`
(`PolylogDepth.mono_exponent`), and a meaning-preserving map of bases embeds the classes
(`PolylogDepth.mono`), so `NCⁱ ⊆ ACⁱ ⊆ TCⁱ` and `ACⁱ ⊆ ACⁱ[q]`. These classes are nonuniform.

## Main definitions

* `Cslib.Circuits.Boolean.PolylogDepth`: polynomial size and depth `O((log n) ^ i)`.
* `Cslib.Circuits.Boolean.NC`, `AC`, `TC`, `ACMod`: the hierarchies.
* `Cslib.Circuits.Boolean.deMorganToUnbounded`: the De Morgan basis inside the unbounded fan-in
  basis.

## Main results

* `Cslib.Circuits.Boolean.NC_subset_AC`, `AC_subset_TC`, `AC_subset_ACMod`: the inclusions.
* `Cslib.Circuits.Boolean.AC_zero`, `TC_zero`, `ACMod_zero`: the constant-depth classes.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

variable {σ τ : Signature}

/-- The languages over `Bool` decided, at every input length `n`, by circuits over `I` of
polynomially bounded size and depth at most `c (⌊log₂ n⌋ + 1) ^ i` for a constant `c`. -/
def PolylogDepth (I : Interpretation σ Bool) (i : ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (s : ℕ → ℕ), PolynomiallyBounded s ∧ ∀ n,
    ∃ C : Circuit σ n 1, C.Computes I (single (L.slice n)) ∧
      C.depth ≤ c * (Nat.log 2 n + 1) ^ i ∧ C.size ≤ s n}

namespace PolylogDepth

variable {I : Interpretation σ Bool} {i j : ℕ}

/-- The hierarchy is monotone in the exponent. -/
theorem mono_exponent (hij : i ≤ j) : PolylogDepth I i ⊆ PolylogDepth I j := by
  rintro L ⟨c, s, hs, hC⟩
  refine ⟨c, s, hs, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  exact ⟨C, hCc, hCd.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hij)), hCs⟩

/-- A meaning-preserving map of bases embeds the classes. -/
theorem mono (φ : σ.Hom τ) {J : Interpretation τ Bool} [φ.Preserves I J] :
    PolylogDepth I i ⊆ PolylogDepth J i := by
  rintro L ⟨c, s, hs, hC⟩
  refine ⟨c, s, hs, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  exact ⟨C.mapOp φ, hCc.mapOp, by simpa using hCd, by simpa using hCs⟩

end PolylogDepth

/-- For exponent zero, polynomial size and constant depth. -/
theorem polylogDepth_zero (I : Interpretation σ Bool) : PolylogDepth I 0 = ConstDepth I := by
  ext L
  simp only [PolylogDepth, pow_zero, mul_one, Set.mem_ofPred_eq, ConstDepth.mem_iff]

/-- **NCⁱ**: polynomial size and depth `O((log n) ^ i)` over the De Morgan basis of fan-in two. -/
def NC (i : ℕ) : Set (Language Bool) :=
  PolylogDepth interpretation i

/-- **ACⁱ**: polynomial size and depth `O((log n) ^ i)` with unbounded fan-in. -/
def AC (i : ℕ) : Set (Language Bool) :=
  PolylogDepth Unbounded.interpretation i

/-- **TCⁱ**: polynomial size and depth `O((log n) ^ i)` with majority gates. -/
def TC (i : ℕ) : Set (Language Bool) :=
  PolylogDepth (Unbounded.extInterpretation majority) i

/-- **ACⁱ[q]**: polynomial size and depth `O((log n) ^ i)` with `MOD_q` gates. -/
def ACMod (q i : ℕ) : Set (Language Bool) :=
  PolylogDepth (Unbounded.extInterpretation (modGate q)) i

theorem AC_zero : AC 0 = AC0 :=
  polylogDepth_zero _

theorem TC_zero : TC 0 = TC0 :=
  polylogDepth_zero _

theorem ACMod_zero (q : ℕ) : ACMod q 0 = AC0Mod q :=
  polylogDepth_zero _

/-- The operations of the De Morgan basis as operations of the unbounded fan-in basis: the
constants as the conjunction and disjunction of nothing. -/
def deMorganOp : Op → Unbounded.Op
  | .const true => .and 0
  | .const false => .or 0
  | .not => .not
  | .and => .and 2
  | .or => .or 2

/-- The De Morgan basis inside the unbounded fan-in basis. -/
def deMorganToUnbounded : signature.Hom Unbounded.signature :=
  ⟨deMorganOp, fun op => by rcases op with (_ | _) | _ | _ | _ <;> rfl⟩

@[simp] theorem deMorganToUnbounded_apply (op : Op) : deMorganToUnbounded op = deMorganOp op :=
  rfl

instance : deMorganToUnbounded.Preserves interpretation Unbounded.interpretation :=
  ⟨fun op x => by
    rcases op with (_ | _) | _ | _ | _
    · exact decide_eq_false fun ⟨j, _⟩ => j.elim0
    · exact decide_eq_true fun j => j.elim0
    · rfl
    · change decide (∀ j : Fin 2, x (Fin.cast rfl j) = true) = (x 0 && x 1)
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, Fin.forall_fin_two]
      exact Iff.rfl
    · change decide (∃ j : Fin 2, x (Fin.cast rfl j) = true) = (x 0 || x 1)
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.or_eq_true, Fin.exists_fin_two]
      exact Iff.rfl⟩

/-- **NCⁱ ⊆ ACⁱ.** -/
theorem NC_subset_AC (i : ℕ) : NC i ⊆ AC i :=
  PolylogDepth.mono deMorganToUnbounded

/-- **ACⁱ ⊆ TCⁱ.** -/
theorem AC_subset_TC (i : ℕ) : AC i ⊆ TC i :=
  PolylogDepth.mono Unbounded.toExt

/-- **ACⁱ ⊆ ACⁱ[q].** -/
theorem AC_subset_ACMod (q i : ℕ) : AC i ⊆ ACMod q i :=
  PolylogDepth.mono Unbounded.toExt

theorem NC_mono {i j : ℕ} (hij : i ≤ j) : NC i ⊆ NC j :=
  PolylogDepth.mono_exponent hij

theorem AC_mono {i j : ℕ} (hij : i ≤ j) : AC i ⊆ AC j :=
  PolylogDepth.mono_exponent hij

theorem TC_mono {i j : ℕ} (hij : i ≤ j) : TC i ⊆ TC j :=
  PolylogDepth.mono_exponent hij

end Cslib.Circuits.Boolean
