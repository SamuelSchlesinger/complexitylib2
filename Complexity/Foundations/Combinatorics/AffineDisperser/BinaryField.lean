/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.AffineDisperser.TensorBasis
public import Mathlib.FieldTheory.Finite.GaloisField
import Complexity.Foundations.Combinatorics.AffineDisperser
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot

/-!
# Explicit binary fields of composite degree

A binary polynomial is coded by the natural number whose binary digits, least significant first,
are its coefficients (`Cslib.AffineDisperser.polyOfCode`). The irreducible polynomial of degree `p`
with the least code (`Cslib.AffineDisperser.leastIrreducible`) is found by exhaustive search
through the `2 ^ p` codes in `[2 ^ p, 2 ^ (p + 1))`.

For distinct primes `mᵢ` with product `n`, each `leastIrreducible mᵢ` has a root `αᵢ` in
`𝔽_{2 ^ n} = GaloisField 2 n` (`Cslib.AffineDisperser.binaryRoot`), and the monomials
`∏ᵢ αᵢ ^ Jᵢ`, `Jᵢ < mᵢ`, form a basis of `𝔽_{2 ^ n}` over `𝔽₂`
(`Cslib.AffineDisperser.compositeBasis`). Arithmetic in this basis is arithmetic in
`𝔽₂[X₁, …, Xₖ] / (g₁(X₁), …, gₖ(Xₖ))`, which needs only the polynomials of small degree `mᵢ`.
When every prime factor of `n` exceeds `L`, proper subfields of `𝔽_{2 ^ n}` have at most
`2 ^ (n / (L + 1))` elements (`Cslib.AffineDisperser.card_subfield_le_of_lt_prime`).

## Main definitions

* `Cslib.AffineDisperser.polyOfCode`: the binary polynomial with a given code.
* `Cslib.AffineDisperser.leastIrreducible`: the irreducible binary polynomial of degree `p` with the
  least code.
* `Cslib.AffineDisperser.binaryRoot`: a root of `leastIrreducible p` in `GaloisField 2 n`, `p ∣ n`.
* `Cslib.AffineDisperser.compositeBasis`: the monomial basis of `GaloisField 2 (∏ᵢ mᵢ)` for distinct
  primes `mᵢ`.

## Main results

* `Cslib.AffineDisperser.irreducible_leastIrreducible`,
  `Cslib.AffineDisperser.natDegree_leastIrreducible`: `leastIrreducible p` is irreducible of degree
  `p`.
* `Cslib.AffineDisperser.exists_code_leastIrreducible`: the code of `leastIrreducible p` lies in
  `[2 ^ p, 2 ^ (p + 1))`, and no smaller code is irreducible of degree `p`.
* `Cslib.AffineDisperser.card_subfield_le_of_lt_prime`: the subfield bound.
-/

@[expose] public section

namespace Cslib.AffineDisperser

open Module Polynomial

/-- The binary polynomial whose coefficients, from the constant term up, are the binary digits of
`m`, least significant first. -/
noncomputable def polyOfCode (m : ℕ) : (ZMod 2)[X] :=
  if m = 0 then 0 else C (m : ZMod 2) + X * polyOfCode (m / 2)
decreasing_by omega

@[simp]
theorem polyOfCode_zero : polyOfCode 0 = 0 := by
  rw [polyOfCode, ite_eq_left rfl]

/-- Appending the bit `b` below the code `m` multiplies by `X` and adds the constant `b`. -/
theorem polyOfCode_two_mul_add (m : ℕ) (b : ZMod 2) :
    polyOfCode (2 * m + b.val) = C b + X * polyOfCode m := by
  have hb : b.val < 2 := ZMod.val_lt b
  rcases Nat.eq_zero_or_pos (2 * m + b.val) with h | h
  · have hm : m = 0 := by omega
    have hb0 : b = 0 := (ZMod.val_eq_zero b).1 (by omega)
    subst hm hb0
    simp [polyOfCode_zero]
  · rw [polyOfCode, ite_eq_right h.ne', show (2 * m + b.val) / 2 = m by omega]
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add, ZMod.natCast_zmod_val]

/-- The code `m ≠ 0` gives a nonzero polynomial of degree `⌊log₂ m⌋`. -/
theorem polyOfCode_ne_zero_and_natDegree {m : ℕ} (hm : m ≠ 0) :
    polyOfCode m ≠ 0 ∧ (polyOfCode m).natDegree = Nat.log 2 m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases lt_or_ge m 2 with h | h
    · obtain rfl : m = 1 := by omega
      have h1 : polyOfCode 1 = 1 := by
        simpa [polyOfCode_zero, ZMod.val_one] using polyOfCode_two_mul_add 0 1
      rw [h1, Nat.log_one_right]
      exact ⟨one_ne_zero, natDegree_one⟩
    · obtain ⟨hne, hdeg⟩ := ih (m / 2) (by omega) (by omega)
      have heq : polyOfCode m = X * polyOfCode (m / 2) + C (m : ZMod 2) := by
        rw [polyOfCode, ite_eq_right hm, add_comm]
      have hd : (polyOfCode m).natDegree = Nat.log 2 m := by
        rw [heq, natDegree_add_C, natDegree_X_mul hne, hdeg,
          ← Nat.log_of_one_lt_of_le one_lt_two h]
      refine ⟨fun h0 => ?_, hd⟩
      rw [h0, natDegree_zero, Nat.log_of_one_lt_of_le one_lt_two h] at hd
      omega

theorem natDegree_polyOfCode {m : ℕ} (hm : m ≠ 0) : (polyOfCode m).natDegree = Nat.log 2 m :=
  (polyOfCode_ne_zero_and_natDegree hm).2

/-- Every binary polynomial has a code. -/
theorem polyOfCode_surjective : Function.Surjective polyOfCode := by
  intro g
  induction hd : g.natDegree using Nat.strong_induction_on generalizing g with
  | _ d ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · refine ⟨(g.coeff 0).val, ?_⟩
      have := polyOfCode_two_mul_add 0 (g.coeff 0)
      rw [mul_zero, zero_add, polyOfCode_zero, mul_zero, add_zero] at this
      rw [this, ← eq_C_of_natDegree_eq_zero hd]
    · obtain ⟨m, hm⟩ := ih (d - 1) (by omega) g.divX
        (by rw [natDegree_divX_eq_natDegree_tsub_one, hd])
      refine ⟨2 * m + (g.coeff 0).val, ?_⟩
      rw [polyOfCode_two_mul_add, hm, add_comm, X_mul_divX_add]

/-- There is an irreducible binary polynomial of every positive degree `p`: the minimal polynomial
of a primitive element of `𝔽_{2 ^ p}`. -/
theorem exists_irreducible_natDegree_eq {p : ℕ} (hp : p ≠ 0) :
    ∃ g : (ZMod 2)[X], Irreducible g ∧ g.natDegree = p := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_top (ZMod 2) (GaloisField 2 p)
  have hint : IsIntegral (ZMod 2) α := .of_finite _ α
  refine ⟨minpoly (ZMod 2) α, minpoly.irreducible hint, ?_⟩
  rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top',
    GaloisField.finrank 2 hp]

open Classical in
/-- The irreducible binary polynomial of degree `p` with the least code (`X` when `p = 0`, where no
irreducible polynomial exists). -/
noncomputable def leastIrreducible (p : ℕ) : (ZMod 2)[X] :=
  if h : ∃ m, Irreducible (polyOfCode m) ∧ (polyOfCode m).natDegree = p then
    polyOfCode (Nat.find h)
  else X

theorem exists_code_irreducible {p : ℕ} (hp : p ≠ 0) :
    ∃ m, Irreducible (polyOfCode m) ∧ (polyOfCode m).natDegree = p := by
  obtain ⟨g, hg, hgp⟩ := exists_irreducible_natDegree_eq hp
  obtain ⟨m, rfl⟩ := polyOfCode_surjective g
  exact ⟨m, hg, hgp⟩

open Classical in
theorem leastIrreducible_eq {p : ℕ} (hp : p ≠ 0) :
    leastIrreducible p = polyOfCode (Nat.find (exists_code_irreducible hp)) := by
  rw [leastIrreducible, dite_eq_left (exists_code_irreducible hp)]

theorem irreducible_leastIrreducible {p : ℕ} (hp : p ≠ 0) : Irreducible (leastIrreducible p) := by
  classical
  rw [leastIrreducible_eq hp]
  exact (Nat.find_spec (exists_code_irreducible hp)).1

theorem natDegree_leastIrreducible {p : ℕ} (hp : p ≠ 0) : (leastIrreducible p).natDegree = p := by
  classical
  rw [leastIrreducible_eq hp]
  exact (Nat.find_spec (exists_code_irreducible hp)).2

/-- **The exhaustive search**: `leastIrreducible p` is `polyOfCode m` for a code
`2 ^ p ≤ m < 2 ^ (p + 1)` such that no smaller code is irreducible of degree `p`. -/
theorem exists_code_leastIrreducible {p : ℕ} (hp : p ≠ 0) :
    ∃ m, 2 ^ p ≤ m ∧ m < 2 ^ (p + 1) ∧ leastIrreducible p = polyOfCode m ∧
      ∀ m' < m, ¬ (Irreducible (polyOfCode m') ∧ (polyOfCode m').natDegree = p) := by
  classical
  have hspec := Nat.find_spec (exists_code_irreducible hp)
  set m := Nat.find (exists_code_irreducible hp)
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, polyOfCode_zero] at hspec
    exact hspec.1.ne_zero rfl
  have hlog := (natDegree_polyOfCode hm0).symm.trans hspec.2
  refine ⟨m, ?_, ?_, leastIrreducible_eq hp, fun m' hm' => Nat.find_min _ hm'⟩
  · exact hlog ▸ Nat.pow_log_le_self 2 hm0
  · exact hlog ▸ Nat.lt_pow_succ_log_self one_lt_two m

/-- `leastIrreducible p` is monic, as every nonzero binary polynomial is. -/
theorem monic_leastIrreducible {p : ℕ} (hp : p ≠ 0) : (leastIrreducible p).Monic :=
  (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _
    (leadingCoeff_ne_zero.2 (irreducible_leastIrreducible hp).ne_zero)

/-- `leastIrreducible p` has a root in `𝔽_{2 ^ n}` when `p ∣ n`. -/
theorem exists_aeval_leastIrreducible_eq_zero {p n : ℕ} (hp : p ≠ 0) (hn : n ≠ 0) (hpn : p ∣ n) :
    ∃ α : GaloisField 2 n, aeval α (leastIrreducible p) = 0 := by
  have : Fact (Irreducible (leastIrreducible p)) := ⟨irreducible_leastIrreducible hp⟩
  have hdeg : finrank (ZMod 2) (AdjoinRoot (leastIrreducible p)) = p := by
    rw [(AdjoinRoot.powerBasis (irreducible_leastIrreducible hp).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, natDegree_leastIrreducible hp]
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod 2) (K := AdjoinRoot (leastIrreducible p)) (L := GaloisField 2 n)
    (by rw [hdeg, GaloisField.finrank 2 hn]; exact hpn)
  exact ⟨φ (AdjoinRoot.root _), by rw [aeval_algHom_apply, AdjoinRoot.aeval_eq,
    AdjoinRoot.mk_self, map_zero]⟩

open Classical in
/-- A root of `leastIrreducible p` in `𝔽_{2 ^ n}`, which exists when `p ∣ n` and `p, n ≠ 0`
(`0` when there is none). -/
noncomputable def binaryRoot (p n : ℕ) : GaloisField 2 n :=
  if h : ∃ α : GaloisField 2 n, aeval α (leastIrreducible p) = 0 then h.choose else 0

theorem minpoly_binaryRoot {p n : ℕ} (hp : p ≠ 0) (hn : n ≠ 0) (hpn : p ∣ n) :
    minpoly (ZMod 2) (binaryRoot p n) = leastIrreducible p := by
  have h := exists_aeval_leastIrreducible_eq_zero hp hn hpn
  rw [binaryRoot, dite_eq_left h]
  exact (minpoly.eq_of_irreducible_of_monic (irreducible_leastIrreducible hp) h.choose_spec
    (monic_leastIrreducible hp)).symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The monomial basis of `𝔽_{2 ^ n}`**, `n = ∏ᵢ mᵢ` for distinct primes `mᵢ`: the monomials
`∏ᵢ αᵢ ^ Jᵢ`, `Jᵢ < mᵢ`, in roots `αᵢ = binaryRoot mᵢ n` of the irreducible polynomials
`leastIrreducible mᵢ`. -/
noncomputable def compositeBasis (m : ι → ℕ) (hm : ∀ i, (m i).Prime)
    (hinj : Function.Injective m) :
    Basis ((i : ι) → Fin (m i)) (ZMod 2) (GaloisField 2 (∏ i, m i)) :=
  have hn : ∏ i, m i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (hm i).ne_zero
  prodPowBasis (α := fun i => binaryRoot (m i) (∏ i, m i))
    (fun i j hij => (Nat.coprime_primes (hm i) (hm j)).2 (hinj.ne hij))
    (GaloisField.finrank 2 hn) fun i => by
      rw [minpoly_binaryRoot (hm i).ne_zero hn (Finset.dvd_prod_of_mem m (Finset.mem_univ i)),
        natDegree_leastIrreducible (hm i).ne_zero]

theorem compositeBasis_apply (m : ι → ℕ) (hm : ∀ i, (m i).Prime) (hinj : Function.Injective m)
    (J : (i : ι) → Fin (m i)) :
    compositeBasis m hm hinj J = ∏ i, binaryRoot (m i) (∏ i, m i) ^ (J i : ℕ) := by
  unfold compositeBasis
  exact prodPowBasis_apply _ _ _ J

/-- **Subfields of `𝔽_{2 ^ n}`**: if every prime factor of `n` exceeds `L`, every proper subfield
of a field with `2 ^ n` elements has at most `2 ^ (n / (L + 1))` elements. -/
theorem card_subfield_le_of_lt_prime {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    {n L : ℕ} (hn : finrank (ZMod 2) F = n) (hL : ∀ q, q.Prime → q ∣ n → L < q)
    (K : Subfield F) (hK : K ≠ ⊤) : Nat.card K ≤ 2 ^ (n / (L + 1)) := by
  have : CharP F 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  cases nonempty_fintype F
  have : CharP K 2 := K.subtype.charP Subtype.val_injective 2
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨a, -, ha⟩ := FiniteField.card K 2
  have hF : Nat.card F = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F), Nat.card_zmod, hn]
  -- `|F| = |K| ^ e` with `e = [F : K] ≥ 2`, so `n = a e`
  have hFe : Nat.card F = Nat.card K ^ finrank K F := Module.natCard_eq_pow_finrank (K := K)
  rw [hF, Nat.card_eq_fintype_card (α := K), ha, ← pow_mul] at hFe
  have hne : n = a * finrank K F := Nat.pow_right_injective le_rfl hFe
  have hsq := card_sq_le_of_ne_top hK
  rw [Nat.card_eq_fintype_card (α := K), ha, hF, ← pow_mul] at hsq
  have he2 : 2 ≤ finrank K F := by
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hsq
    rw [hne] at this
    exact Nat.le_of_mul_le_mul_left this a.pos
  -- a prime factor `q` of `e` divides `n`, so `q > L` and `a ≤ n / q`
  have hq := Nat.minFac_prime (by omega : finrank K F ≠ 1)
  have hqL : L < (finrank K F).minFac :=
    hL _ hq ((Nat.minFac_dvd _).trans (hne ▸ dvd_mul_left _ _))
  rw [Nat.card_eq_fintype_card (α := K), ha]
  refine Nat.pow_le_pow_right two_pos ((Nat.le_div_iff_mul_le (by omega)).2 ?_)
  calc a * (L + 1) ≤ a * finrank K F :=
        Nat.mul_le_mul_left _ (hqL.trans_le (Nat.minFac_le (by omega)))
    _ = n := hne.symm

end Cslib.AffineDisperser
