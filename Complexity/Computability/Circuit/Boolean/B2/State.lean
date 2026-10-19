/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.B2.SemiCircuit
public import Complexity.Foundations.Data.BitString.AffineDisperser
public import Mathlib.Data.Finset.Sort

/-!
# States of gate elimination and their potential

A *state* of the gate elimination of [Mishra and Santhanam, Section 2.4][MishraSanthanam2026]
for a Boolean function `f` on `n` bits consists of a fair semi-circuit reading parameters, a set
of disjoint pairs of parameters and an injective map `Φ` from parameter values to inputs of `f`
such that the semi-circuit computes `f ∘ Φ` (`State.Valid`). The source keeps `Φ` in the form

  `Φ(u) = b + L u + ∑_{{p, r} ∈ P} c_{pr} p r`  (form (1) of the source),

an affine map plus quadratic terms over the pairs. We record only the property of this form
that the proof uses: along every affine family of parameter assignments on which each pair has a
constant member, or a constant sum, `Φ` is affine (`State.Valid.phi_affine`). The map `Φ` is
stored as a function of all internal values that depends only on the parameters.

A state has `m` parameters, `q` pairs, `a = m - q` and size `s`, the number of gates plus the
number of equations. The *weight* of an unpaired parameter of degree `k` is `0`, `6` or `7` for
`k = 0`, `k = 1` and `k ≥ 2`, and the *potential* is

  `W = 2 s + 3 q + ∑_{x unpaired} wt(x)`  (equation (5) of the source).

Proposition 2.2 of the source: the image of `Φ` contains an affine subspace of dimension `a`
(`State.Valid.exists_affine_embedding`), so the output of a valid state for an affine disperser
for dimension `d ≤ a` is not constant (`State.Valid.exists_out_ne_of_le`). Restricting one more
parameter to an affine function of the others keeps dimension `a - 1`, so when `d < a` the output
is not constant there either (`State.Valid.false_of_fix`); in particular it is not an affine
function of the parameters (`State.Valid.out_not_affine`, part of Lemma 2.3 of the source).

## Main definitions

* `Cslib.Circuits.Boolean.B2.State`, `Cslib.Circuits.Boolean.B2.State.Valid`: states.
* `Cslib.Circuits.Boolean.B2.State.m`, `q`, `a`, `s`, `W`: the counted quantities and the
  potential, with `Cslib.Circuits.Boolean.B2.weight`.

## Main results

* `Cslib.Circuits.Boolean.B2.State.Valid.exists_affine_embedding`: Proposition 2.2.
* `Cslib.Circuits.Boolean.B2.State.Valid.false_of_fix`,
  `Cslib.Circuits.Boolean.B2.State.Valid.out_not_affine`: Lemma 2.3.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.B2

open Finset Cslib.BitString

/-- The weight of an unpaired parameter of degree `k`: `0` if it is unused, `6` if it is
isolated and `7` otherwise (equation (4) of [Mishra and Santhanam][MishraSanthanam2026]). -/
def weight (k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then 6 else 7

theorem weight_mono {k l : ℕ} (h : k ≤ l) : weight k ≤ weight l := by
  unfold weight; split_ifs <;> omega

theorem weight_le_seven (k : ℕ) : weight k ≤ 7 := by
  unfold weight; split_ifs <;> omega

@[simp] theorem weight_zero : weight 0 = 0 := rfl

@[simp] theorem weight_one : weight 1 = 6 := rfl

theorem weight_of_two_le {k : ℕ} (hk : 2 ≤ k) : weight k = 7 := by
  unfold weight; split_ifs <;> omega

theorem six_le_weight {k : ℕ} (hk : 1 ≤ k) : 6 ≤ weight k := by
  unfold weight; split_ifs <;> omega

/-- Along the family `σ` of assignments, the pair `pr` contributes an affine term to a quadratic
map: one of its members, or their sum, is constant. -/
def PairTame {α : Type*} (σ : α → ℕ → Bool) (pr : ℕ × ℕ) : Prop :=
  (∀ x y, σ x pr.1 = σ y pr.1) ∨ (∀ x y, σ x pr.2 = σ y pr.2) ∨
    ∀ x y, σ x pr.1 + σ x pr.2 = σ y pr.1 + σ y pr.2

/-- A state of gate elimination for a function of `n` bits: a semi-circuit, disjoint pairs of
parameters and the parameter map `Φ`. -/
structure State (n : ℕ) extends SemiCircuit where
  /-- The pairs of parameters that may occur together in a quadratic term of `Φ`. -/
  pairs : Finset (ℕ × ℕ)
  /-- The parameter map, as a function of the values of all internal values. -/
  phi : (ℕ → Bool) → BitString n

namespace State

variable {n : ℕ} (S : State n)

/-- `x` belongs to one of the pairs. -/
def Paired (x : ℕ) : Prop :=
  ∃ pr ∈ S.pairs, pr.1 = x ∨ pr.2 = x

instance : DecidablePred S.Paired :=
  fun _ => inferInstanceAs (Decidable (∃ pr ∈ S.pairs, _))

/-- The unpaired parameters. -/
def unpaired : Finset ℕ :=
  S.params.filter fun x => ¬ S.Paired x

/-- The number of parameters. -/
def m : ℕ :=
  S.params.card

/-- The number of pairs. -/
def q : ℕ :=
  S.pairs.card

/-- The number of parameters minus the number of pairs. -/
def a : ℕ :=
  S.m - S.q

/-- The size of the semi-circuit: gates plus equations. -/
def s : ℕ :=
  S.size

/-- The potential `W = 2 s + 3 q + ∑ wt(x)` over the unpaired parameters `x`. -/
def W : ℕ :=
  2 * S.s + 3 * S.q + ∑ x ∈ S.unpaired, weight (S.deg x)

/-- A valid state for `f`: a well-formed fair semi-circuit, disjoint pairs of distinct
parameters, and an injective parameter map that depends only on the parameters and is affine
along every affine family of assignments on which each pair has a constant member or a constant
sum, such that the output of every consistent assignment is the value of `f` at its image. -/
structure Valid (f : BooleanFunction n) : Prop where
  wf : S.WellFormed
  pair_mem : ∀ pr ∈ S.pairs, pr.1 ∈ S.params ∧ pr.2 ∈ S.params ∧ pr.1 ≠ pr.2
  pairs_disjoint : ∀ pr ∈ S.pairs, ∀ pr' ∈ S.pairs, pr ≠ pr' →
    pr.1 ≠ pr'.1 ∧ pr.1 ≠ pr'.2 ∧ pr.2 ≠ pr'.1 ∧ pr.2 ≠ pr'.2
  phi_congr : ∀ val val', (∀ j ∈ S.params, val j = val' j) → S.phi val = S.phi val'
  phi_affine : ∀ (k : ℕ) (σ : BitString k → ℕ → Bool), IsAffine σ →
    (∀ pr ∈ S.pairs, PairTame σ pr) → IsAffine (S.phi ∘ σ)
  phi_injective : ∀ val val', S.phi val = S.phi val' → ∀ j ∈ S.params, val j = val' j
  computes : ∀ val, S.Consistent val → S.out.eval val = f (S.phi val)

/-! ### Spreading bits over a finite set of names -/

/-- The assignment reading the bits of `u` on the elements of `F`, in increasing order, and
`false` elsewhere. -/
def spread (F : Finset ℕ) {k : ℕ} (h : F.card = k) (u : BitString k) : ℕ → Bool :=
  fun i => if hi : i ∈ F then u ((F.orderIsoOfFin h).symm ⟨i, hi⟩) else false

theorem isAffine_spread (F : Finset ℕ) {k : ℕ} (h : F.card = k) : IsAffine (spread F h) := by
  intro u v w
  funext i
  simp only [spread, Pi.add_apply]
  split_ifs <;> rfl

theorem spread_of_notMem {F : Finset ℕ} {k : ℕ} (h : F.card = k) (u : BitString k) {i : ℕ}
    (hi : i ∉ F) : spread F h u i = false := by
  simp [spread, hi]

theorem spread_orderIsoOfFin {F : Finset ℕ} {k : ℕ} (h : F.card = k) (u : BitString k)
    (i : Fin k) : spread F h u (F.orderIsoOfFin h i) = u i := by
  simp only [spread, Finset.coe_mem, ↓reduceDIte, Subtype.coe_eta, OrderIso.symm_apply_apply]

theorem eq_of_spread {F : Finset ℕ} {k : ℕ} (h : F.card = k) {u v : BitString k}
    (huv : ∀ i ∈ F, spread F h u i = spread F h v i) : u = v := by
  funext i
  rw [← spread_orderIsoOfFin h u i, ← spread_orderIsoOfFin h v i]
  exact huv _ (F.orderIsoOfFin h i).2

/-- Updating an affine family at one name by an affine function keeps it affine. -/
theorem isAffine_update {k : ℕ} {σ : BitString k → ℕ → Bool} (hσ : IsAffine σ) (x : ℕ)
    {ψ : BitString k → Bool} (hψ : IsAffine ψ) :
    IsAffine fun u => Function.update (σ u) x (ψ u) := by
  intro u v w
  funext i
  by_cases hi : i = x
  · subst hi
    simp only [Function.update_self, Pi.add_apply, hψ u v w]
  · simp only [Function.update_of_ne hi, Pi.add_apply, congrFun (hσ u v w) i]

/-- A constant plus a sum of coordinates of an affine family is affine. -/
theorem isAffine_const_add_sum {k : ℕ} {σ : BitString k → ℕ → Bool} (hσ : IsAffine σ)
    (c : Bool) (R : Finset ℕ) : IsAffine fun u => c + ∑ j ∈ R, σ u j := by
  intro u v w
  simp only [fun j => congrFun (hσ u v w) j, Pi.add_apply, Finset.sum_add_distrib]
  generalize ∑ j ∈ R, σ u j = a
  generalize ∑ j ∈ R, σ v j = b
  generalize ∑ j ∈ R, σ w j = e
  revert a b e c; decide

variable {S}

/-! ### Proposition 2.2 -/

/-- Choosing one member `rep pr` of every pair leaves exactly `a` other parameters. -/
theorem Valid.card_sdiff_image {f : BooleanFunction n} (hS : S.Valid f) (rep : ℕ × ℕ → ℕ)
    (hrep : ∀ pr, rep pr = pr.1 ∨ rep pr = pr.2) :
    (S.params \ S.pairs.image rep).card = S.a := by
  have hsub : S.pairs.image rep ⊆ S.params := by
    intro i hi
    obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.1 hi
    rcases hrep pr with h | h <;> rw [h]
    · exact (hS.pair_mem pr hpr).1
    · exact (hS.pair_mem pr hpr).2.1
  have hinj : Set.InjOn rep S.pairs := by
    intro pr hpr pr' hpr' heq
    by_contra hne
    have := hS.pairs_disjoint pr hpr pr' hpr' hne
    rcases hrep pr with h | h <;> rcases hrep pr' with h' | h' <;> rw [h, h'] at heq <;> tauto
  rw [Finset.card_sdiff_of_subset hsub, Finset.card_image_of_injOn hinj]
  rfl

/-- Along an injective affine family of parameter assignments on which every pair is tame, the
parameter map is an injective affine map, so the output of a valid state for an affine
disperser for dimension `d` is not constant when the family has dimension at least `d`. -/
theorem Valid.exists_out_ne {f : BooleanFunction n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) {k : ℕ} (σ : BitString k → ℕ → Bool) (hσ : IsAffine σ)
    (htame : ∀ pr ∈ S.pairs, PairTame σ pr)
    (hinj : ∀ u v, (∀ j ∈ S.params, σ u j = σ v j) → u = v) (hk : d ≤ k) :
    ∃ u v val val', S.Consistent val ∧ S.Consistent val' ∧ (∀ j ∈ S.params, val j = σ u j) ∧
      (∀ j ∈ S.params, val' j = σ v j) ∧ S.out.eval val ≠ S.out.eval val' := by
  obtain ⟨u, v, huv⟩ := hf.mono hk (S.phi ∘ σ) (hS.phi_affine k σ hσ htame)
    (fun u v h => hinj u v (hS.phi_injective _ _ h))
  obtain ⟨val, hval, hcons⟩ := hS.wf.exists_consistent (σ u)
  obtain ⟨val', hval', hcons'⟩ := hS.wf.exists_consistent (σ v)
  refine ⟨u, v, val, val', hcons, hcons', hval, hval', ?_⟩
  rw [hS.computes val hcons, hS.computes val' hcons', hS.phi_congr val (σ u) hval,
    hS.phi_congr val' (σ v) hval']
  exact huv

/-- **Proposition 2.2** of [Mishra and Santhanam][MishraSanthanam2026]: the image of the
parameter map of a valid state contains an affine subspace of dimension `a`, the image of an
injective affine map from `BitString a`. -/
theorem Valid.exists_affine_embedding {f : BooleanFunction n} (hS : S.Valid f) :
    ∃ g : BitString S.a → BitString n, IsAffine g ∧ Function.Injective g ∧
      ∀ u, ∃ val, S.Consistent val ∧ g u = S.phi val := by
  set F := S.params \ S.pairs.image Prod.fst
  have hF : F.card = S.a := hS.card_sdiff_image Prod.fst fun _ => Or.inl rfl
  have hFp : F ⊆ S.params := Finset.sdiff_subset
  refine ⟨S.phi ∘ spread F hF, hS.phi_affine _ _ (isAffine_spread F hF) ?_, ?_, fun u => ?_⟩
  · intro pr hpr
    refine Or.inl fun u v => ?_
    have : pr.1 ∉ F := fun h => (Finset.mem_sdiff.1 h).2 (Finset.mem_image_of_mem _ hpr)
    rw [spread_of_notMem hF u this, spread_of_notMem hF v this]
  · intro u v h
    exact eq_of_spread hF fun i hi => hS.phi_injective _ _ h i (hFp hi)
  · obtain ⟨val, hval, hcons⟩ := hS.wf.exists_consistent (spread F hF u)
    exact ⟨val, hcons, (hS.phi_congr val _ hval).symm⟩

/-- The output of a valid state for an affine disperser for dimension `d ≤ a` is not
constant. -/
theorem Valid.exists_out_ne_of_le {f : BooleanFunction n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d ≤ S.a) :
    ∃ val val', S.Consistent val ∧ S.Consistent val' ∧ S.out.eval val ≠ S.out.eval val' := by
  set F := S.params \ S.pairs.image Prod.fst
  have hF : F.card = S.a := hS.card_sdiff_image Prod.fst fun _ => Or.inl rfl
  have hFp : F ⊆ S.params := Finset.sdiff_subset
  obtain ⟨-, -, val, val', h, h', -, -, hne⟩ := hS.exists_out_ne hf (spread F hF)
    (isAffine_spread F hF) (fun pr hpr => Or.inl fun u v => by
      have : pr.1 ∉ F := fun h => (Finset.mem_sdiff.1 h).2 (Finset.mem_image_of_mem _ hpr)
      rw [spread_of_notMem hF u this, spread_of_notMem hF v this])
    (fun u v h => eq_of_spread hF fun i hi => h i (hFp hi)) ha
  exact ⟨val, val', h, h', hne⟩

/-! ### Lemma 2.3 -/

/-- If `d < a`, the output of a valid state for an affine disperser for dimension `d` is not
constant on the consistent assignments satisfying one more affine equation
`x = c + ∑ j ∈ R, u j` between the parameters: imposing it keeps an affine subspace of dimension
`a - 1 ≥ d` in the image of the parameter map. -/
theorem Valid.false_of_fix {f : BooleanFunction n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) {x : ℕ} (hx : x ∈ S.params) (c : Bool)
    (R : Finset ℕ) (hR : R ⊆ S.params) (hxR : x ∉ R) (b : Bool)
    (hout : ∀ val, S.Consistent val → val x = c + ∑ j ∈ R, val j → S.out.eval val = b) :
    False := by
  classical
  let rep : ℕ × ℕ → ℕ := fun pr => if pr.1 = x then pr.2 else pr.1
  have hrep : ∀ pr, rep pr = pr.1 ∨ rep pr = pr.2 := fun pr => by
    by_cases h : pr.1 = x <;> simp [rep, h]
  have hrepx : ∀ pr ∈ S.pairs, rep pr ≠ x := fun pr hpr => by
    by_cases h : pr.1 = x
    · simp only [rep, h, ite_true]
      exact fun h' => (hS.pair_mem pr hpr).2.2 (h.trans h'.symm)
    · simp only [rep, h, ite_false]
      exact h
  set F := S.params \ S.pairs.image rep
  have hF : F.card = S.a := hS.card_sdiff_image rep hrep
  have hxF : x ∈ F := Finset.mem_sdiff.2 ⟨hx, fun h => by
    obtain ⟨pr, hpr, he⟩ := Finset.mem_image.1 h
    exact hrepx pr hpr he⟩
  set F' := F.erase x
  have hF' : F'.card = S.a - 1 := by rw [Finset.card_erase_of_mem hxF, hF]
  have hF'p : F' ⊆ S.params := (Finset.erase_subset _ _).trans Finset.sdiff_subset
  let σ : BitString (S.a - 1) → ℕ → Bool := fun u =>
    Function.update (spread F' hF' u) x (c + ∑ j ∈ R, spread F' hF' u j)
  have hσx : ∀ u, σ u x = c + ∑ j ∈ R, σ u j := fun u => by
    simp only [σ, Function.update_self]
    congr 1
    exact Finset.sum_congr rfl fun j hj =>
      (Function.update_of_ne (by rintro rfl; exact hxR hj) _ _).symm
  have hσ : IsAffine σ :=
    isAffine_update (isAffine_spread F' hF') x (isAffine_const_add_sum (isAffine_spread F' hF') c R)
  obtain ⟨u, v, val, val', hcons, hcons', hval, hval', hne⟩ := hS.exists_out_ne hf σ hσ
    (fun pr hpr => by
      have hnot : rep pr ∉ F' := fun h =>
        (Finset.mem_sdiff.1 (Finset.mem_of_mem_erase h)).2 (Finset.mem_image_of_mem _ hpr)
      have hconst : ∀ u, σ u (rep pr) = false := fun u => by
        simp only [σ, Function.update_of_ne (hrepx pr hpr), spread_of_notMem hF' u hnot]
      rcases hrep pr with h | h
      · exact Or.inl fun u v => by rw [← h, hconst, hconst]
      · exact Or.inr (Or.inl fun u v => by rw [← h, hconst, hconst]))
    (fun u v h => eq_of_spread hF' fun i hi => by
      have := h i (hF'p hi)
      simpa only [σ, Function.update_of_ne (Finset.ne_of_mem_erase hi)] using this)
    (by omega)
  have hfix : ∀ w : ℕ → Bool, ∀ u', (∀ j ∈ S.params, w j = σ u' j) →
      w x = c + ∑ j ∈ R, w j := fun w u' hw => by
    rw [hw x hx, hσx, Finset.sum_congr rfl fun j hj => hw j (hR hj)]
  exact hne ((hout val hcons (hfix val u hval)).trans (hout val' hcons' (hfix val' v hval')).symm)

/-- Part of **Lemma 2.3** of [Mishra and Santhanam][MishraSanthanam2026]: if `d < a`, the output
of a valid state for an affine disperser for dimension `d` is not an affine function of the
parameters. -/
theorem Valid.out_not_affine {f : BooleanFunction n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) (c : Bool) {T : Finset ℕ} (hT : T ⊆ S.params) :
    ¬ ∀ val, S.Consistent val → S.out.eval val = c + ∑ j ∈ T, val j := by
  intro hout
  rcases T.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · obtain ⟨x, hx⟩ : S.params.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro h
      simp [a, m, h] at ha
    exact hS.false_of_fix hf ha hx false ∅ (Finset.empty_subset _) (Finset.notMem_empty _) c
      fun val hval _ => by simpa using hout val hval
  · refine hS.false_of_fix hf ha (hT hx) c (T.erase x) ((Finset.erase_subset _ _).trans hT)
      (Finset.notMem_erase _ _) false fun val hval hfix => ?_
    rw [hout val hval, ← Finset.add_sum_erase T _ hx, hfix]
    generalize ∑ j ∈ T.erase x, val j = e
    cases c <;> cases e <;> rfl

end State

end Cslib.Circuits.Boolean.B2
