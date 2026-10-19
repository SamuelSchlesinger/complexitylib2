/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.B2.Potential

/-!
# Preliminary reductions of gate elimination

Cases 1 and 2 of the preliminary reductions of [Mishra and Santhanam, Section 4.1]
[MishraSanthanam2026], as steps of gate elimination (`State.Step`): a step yields a valid state
with smaller `m + s` and `ΔW ≤ 14 Δa`.

* Case 1: one of the deletions (D1)–(D4) applies (`State.Valid.step_of_deletion`); it keeps `a`
  and lowers `W`.
* Case 2: an AND-type gate reads an unpaired isolated parameter `z` and another parameter `w`
  (`State.Valid.step_case2`); fixing `w` so that the gate becomes constant deletes it and makes
  `z` unused.

## Main definitions

* `Cslib.Circuits.Boolean.B2.State.Step`: a step of gate elimination.
* `Cslib.Circuits.Boolean.B2.State.DeletionAvailable`: one of (D1)–(D4) applies.

## Main results

* `Cslib.Circuits.Boolean.B2.State.Valid.step_of_deletion`: Case 1.
* `Cslib.Circuits.Boolean.B2.State.Valid.step_case2`: Case 2.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.B2

open Finset Cslib.BitString

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-- A step of gate elimination from `S` to `S'`: `S'` is valid, `m + s` decreases and
`ΔW ≤ 14 Δa`, written without subtraction. -/
def Step (f : BooleanFunction n) (S S' : State n) : Prop :=
  S'.Valid f ∧ S'.m + S'.s < S.m + S.s ∧ S'.W + 14 * S.a ≤ S.W + 14 * S'.a

/-! ### Pairs -/

theorem paired_congr {S S' : State n} (h : S'.pairs = S.pairs) {x : ℕ} :
    S'.Paired x ↔ S.Paired x := by
  unfold Paired; rw [h]

theorem unpaired_congr {S S' : State n} (hp : S'.params = S.params) (h : S'.pairs = S.pairs) :
    S'.unpaired = S.unpaired := by
  ext x
  rw [mem_unpaired, mem_unpaired, hp, paired_congr h]

/-- A parameter in no pair other than `pr` is unpaired once `pr` is removed. -/
theorem paired_erase {S : State n} {pr : ℕ × ℕ} (hpr : pr ∈ S.pairs) {x : ℕ}
    (hx : x ≠ pr.1 ∧ x ≠ pr.2) : S.Paired x ↔ ∃ pr' ∈ S.pairs.erase pr, pr'.1 = x ∨ pr'.2 = x := by
  constructor
  · rintro ⟨pr', hpr', h⟩
    refine ⟨pr', Finset.mem_erase.2 ⟨fun he => ?_, hpr'⟩, h⟩
    subst he
    rcases h with h | h
    · exact hx.1 h.symm
    · exact hx.2 h.symm
  · rintro ⟨pr', hpr', h⟩
    exact ⟨pr', Finset.mem_of_mem_erase hpr', h⟩

/-- The partner of a member of a pair is in no other pair. -/
theorem not_mem_other_pair {S : State n} (hS : S.Valid f) {pr pr' : ℕ × ℕ} (hpr : pr ∈ S.pairs)
    (hpr' : pr' ∈ S.pairs) (hne : pr' ≠ pr) : pr'.1 ≠ pr.1 ∧ pr'.1 ≠ pr.2 ∧ pr'.2 ≠ pr.1 ∧
      pr'.2 ≠ pr.2 :=
  hS.pairs_disjoint pr' hpr' pr hpr hne

/-! ### Deletion steps lower the potential -/

theorem sum_ite_target_le (N : Finset ℕ) (t : Option ℕ) :
    ∑ x ∈ N, (if t = some x then 1 else 0) ≤ 1 := by
  cases t with
  | none => simp
  | some t =>
    simp only [Option.some.injEq]
    rw [Finset.sum_ite_eq]
    split_ifs <;> omega

/-- A deletion step keeps `m`, `q` and `a`, lowers `s` by one and lowers `W` by at least one: only
the target can gain weight, by at most one. -/
theorem DelStep.W_add_one_le {S S' : State n} {N : ℕ ⊕ ℕ} {t : Option ℕ}
    (h : DelStep f S S' N t) : S'.W + 1 ≤ S.W := by
  have hunp := unpaired_congr h.params h.pairs
  have hpt : ∀ x ∈ S.params, S'.wt x + 0 ≤ S.wt x + (if t = some x then 1 else 0) := by
    intro x hx
    by_cases ht : t = some x
    · rw [ite_eq_left ht]
      by_cases hu : x ∈ S.unpaired
      · have hdeg : 1 ≤ S.deg x := Finset.card_pos.2 ⟨N, h.target x ht⟩
        have := six_le_weight hdeg
        rw [wt_of_mem hu]
        have := S'.wt_le_seven x
        omega
      · rw [wt_of_notMem (hunp ▸ hu), wt_of_notMem hu]; omega
    · rw [ite_eq_right ht]
      exact (wt_le_of_children_subset h.params.le h.pairs.ge
        ((h.children x hx ht).trans (Finset.erase_subset _ _))).trans le_rfl
  have := W_add_le (S := S) (S' := S') (N := S.params) le_rfl h.params.le _ _ hpt
  have hs : S'.s + 1 = S.s := h.size
  have hq : S'.q = S.q := by simp [q, h.pairs]
  have := sum_ite_target_le S.params t
  simp only [Finset.sum_const_zero] at *
  omega

theorem DelStep.m_eq {S S' : State n} {N : ℕ ⊕ ℕ} {t : Option ℕ} (h : DelStep f S S' N t) :
    S'.m = S.m := by simp [m, h.params]

theorem DelStep.a_eq {S S' : State n} {N : ℕ ⊕ ℕ} {t : Option ℕ} (h : DelStep f S S' N t) :
    S'.a = S.a := by simp [a, m, q, h.params, h.pairs]

/-- A deletion step is a step of gate elimination. -/
theorem DelStep.step {S S' : State n} {N : ℕ ⊕ ℕ} {t : Option ℕ} (h : DelStep f S S' N t) :
    Step f S S' := by
  refine ⟨h.valid, ?_, ?_⟩
  · have : S'.s + 1 = S.s := h.size
    rw [h.m_eq]; omega
  · rw [h.a_eq]; have := h.W_add_one_le; omega

/-! ### Case 1: deletions -/

/-- One of the deletions (D1)–(D4) applies: an equation has at most two terms; a gate computes,
on the solutions of the affine system, a constant or a literal of one of its inputs; a gate other
than the output has no children; or an unpaired parameter has an equation as its only child. -/
def DeletionAvailable (S : State n) : Prop :=
  (∃ e ∈ S.eqns, (S.eqn e).terms.card ≤ 2) ∨
  (∃ J ∈ S.gates, ∃ ℓ : Lit, (∀ t, ℓ.Reads t → (S.gate J).Reads t) ∧
    ∀ val, S.EqnsHold val → (S.gate J).eval val = ℓ.eval val) ∨
  (∃ J ∈ S.gates, (∀ K ∈ S.gates, ¬ (S.gate K).Reads J) ∧ ¬ S.out.Reads J) ∨
  (∃ x ∈ S.unpaired, ∃ e, S.children x = {.inr e})

/-- In a valid state with `d < a`, the output is not a literal of a parameter, by
Lemma 2.3. -/
theorem Valid.not_out_reads_param {S : State n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) {x : ℕ} (hx : x ∈ S.params) :
    ¬ S.out.Reads x := by
  intro hr
  refine hS.out_not_affine hf ha S.out.neg (Finset.singleton_subset_iff.2 hx) fun val _ => ?_
  rw [Finset.sum_singleton]
  unfold Lit.eval
  unfold Lit.Reads at hr
  rw [hr, Arg.eval_node]
  cases S.out.neg <;> cases val x <;> rfl

/-- (D4): an unpaired parameter `x` whose only child is the equation `e` is exchanged with an
auxiliary variable depending on it and then deleted with `e`; this keeps `a` and lowers `W`. -/
theorem Valid.unit_delete {S : State n} {d : ℕ} (hS : S.Valid f) (hf : IsAffineDisperser f d)
    (ha : d < S.a) {x e : ℕ} (hx : x ∈ S.unpaired) (hc : S.children x = {.inr e}) :
    ∃ S' : State n, S'.Valid f ∧ S'.m = S.m ∧ S'.s + 1 = S.s ∧ S'.a = S.a ∧ S'.q = S.q ∧
      S'.W + 1 ≤ S.W := by
  obtain ⟨hxp, hxu⟩ := mem_unpaired.1 hx
  have hex : Sum.inr e ∈ S.children x := by rw [hc]; exact Finset.mem_singleton_self _
  obtain ⟨he, hxe⟩ := (SemiCircuit.inr_mem_children _).1 hex
  obtain ⟨Q, hQ, c, T, hT, hxT⟩ := SemiCircuit.exists_affineIn_of_mem_terms hS.wf hxp he hxe
  have hsw : S.SwapOK x Q c T := ⟨hxp, hxu, hQ, hT, hxT⟩
  have hS₁ := hS.swap hsw
  have hQp : Q ∉ S.params := fun hp => Finset.disjoint_left.1 hS.wf.disjoint_params_aux hp hQ
  have hQx : Q ≠ x := fun he' => hQp (he' ▸ hxp)
  have hdrop : (S.swap x Q c T).DropEqnOK e x := by
    refine ⟨he, Finset.mem_insert_self _ _, hxe, fun e' he' hee hxe' => ?_, fun K hK hr => ?_,
      hS.not_out_reads_param hf ha hxp⟩
    · have : Sum.inr e' ∈ S.children x := (SemiCircuit.inr_mem_children _).2 ⟨he', hxe'⟩
      rw [hc, Finset.mem_singleton] at this
      exact hee (Sum.inr.inj this)
    · have : Sum.inl K ∈ S.children x := (SemiCircuit.inl_mem_children _).2 ⟨hK, hr⟩
      rw [hc] at this
      simp at this
  have hS' := hS₁.dropEqn hdrop
  set S' := (S.swap x Q c T).dropEqn e x
  have hparams : S'.params = insert Q (S.params.erase x) := rfl
  have hpairs : S'.pairs = S.pairs := rfl
  have hsize : S'.size + 1 = S.size := dropEqn_size hdrop
  have hm : S'.m = S.m := by
    simp only [m, hparams]
    rw [Finset.card_insert_of_notMem fun h => hQp (Finset.mem_of_mem_erase h),
      Finset.card_erase_add_one hxp]
  have hq : S'.q = S.q := by simp [q, hpairs]
  have ha' : S'.a = S.a := by simp only [a, hm, hq]
  have hchildren : ∀ z, S'.children z = (S.children z).erase (.inr e) := fun z => by
    rw [dropEqn_children, swap_children]
  -- the potential
  have hN : S.params ⊆ insert Q S.params := Finset.subset_insert _ _
  have hN' : S'.params ⊆ insert Q S.params := by
    rw [hparams]; exact Finset.insert_subset_insert _ (Finset.erase_subset _ _)
  have hpt : ∀ z ∈ insert Q S.params, S'.wt z + (if z = x then 6 else 0) ≤
      S.wt z + (if z = Q then 7 else 0) := by
    intro z _
    by_cases hzx : z = x
    · subst hzx
      have h1 : S'.wt z = 0 := wt_of_notMem_params (by
        rw [hparams, Finset.mem_insert, Finset.mem_erase]; tauto)
      have h2 : S.wt z = 6 := by
        rw [wt_of_mem hx, SemiCircuit.deg, hc, Finset.card_singleton, weight_one]
      rw [h1, h2, ite_eq_left rfl, ite_eq_right hQx.symm]
    · rw [ite_eq_right hzx]
      by_cases hzQ : z = Q
      · subst hzQ
        rw [ite_eq_left rfl, wt_of_notMem_params hQp]
        have := S'.wt_le_seven z
        omega
      · rw [ite_eq_right hzQ]
        by_cases hu : z ∈ S'.unpaired
        · obtain ⟨hzp, hzu⟩ := mem_unpaired.1 hu
          rw [hparams, Finset.mem_insert, Finset.mem_erase] at hzp
          have hzS : z ∈ S.unpaired := mem_unpaired.2 ⟨(hzp.resolve_left hzQ).2,
            (paired_congr hpairs).not.1 hzu⟩
          rw [wt_of_mem hu, wt_of_mem hzS, add_zero]
          refine weight_mono (Finset.card_le_card ?_)
          rw [hchildren]; exact Finset.erase_subset _ _
        · rw [wt_of_notMem hu]; omega
  have hW := W_add_le hN hN' _ _ hpt
  rw [sum_ite_eq_of_mem (Finset.mem_insert_of_mem hxp),
    sum_ite_eq_of_mem (Finset.mem_insert_self _ _)] at hW
  have hs : S'.s + 1 = S.s := hsize
  exact ⟨S', hS', hm, hs, ha', hq, by omega⟩

/-- (D4) as a step of gate elimination. -/
theorem Valid.step_unit {S : State n} {d : ℕ} (hS : S.Valid f) (hf : IsAffineDisperser f d)
    (ha : d < S.a) {x e : ℕ} (hx : x ∈ S.unpaired) (hc : S.children x = {.inr e}) :
    ∃ S', Step f S S' := by
  obtain ⟨S', hS', hm, hs, ha', -, hW⟩ := hS.unit_delete hf ha hx hc
  exact ⟨S', hS', by omega, by omega⟩

/-- **Case 1** of the preliminary reductions: a deletion lowers `s` and `W` and keeps `a`. -/
theorem Valid.step_of_deletion {S : State n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) (h : S.DeletionAvailable) :
    ∃ S', Step f S S' := by
  rcases h with ⟨e, he, hcard⟩ | ⟨J, hJ, ℓ, hreads, hval⟩ | ⟨J, hJ, hun, hout⟩ | ⟨x, hx, e, hc⟩
  · obtain ⟨S', t, hstep, -⟩ := hS.exists_delStep (N := .inr e) ⟨he, hcard⟩
    exact ⟨S', hstep.step⟩
  · exact ⟨_, (hS.delStep_deleteGate ⟨hJ, hreads, Or.inl hval⟩).step⟩
  · exact ⟨_, (hS.delStep_deleteGate (ℓ := Lit.const false)
      ⟨hJ, fun t ht => by simp [Lit.Reads, Lit.const] at ht, Or.inr ⟨hun, hout⟩⟩).step⟩
  · exact hS.step_unit hf ha hx hc

/-! ### Fixing a parameter to a constant -/

/-- The pairs avoiding `w`. -/
def pairsAvoid (S : State n) (w : ℕ) : Finset (ℕ × ℕ) :=
  S.pairs.filter fun pr => pr.1 ≠ w ∧ pr.2 ≠ w

/-- `r` is the partner of `w`: they form a pair. -/
def IsPartner (S : State n) (w r : ℕ) : Prop :=
  ∃ pr ∈ S.pairs, (pr.1 = w ∧ pr.2 = r) ∨ (pr.2 = w ∧ pr.1 = r)

instance (S : State n) (w : ℕ) : DecidablePred (S.IsPartner w) :=
  fun _ => inferInstanceAs (Decidable (∃ pr ∈ S.pairs, _))

/-- Fix the parameter `w` to the constant `b`, dropping the pair containing `w`, if any: the
restriction (UF) for an unpaired parameter and (PF) for a paired one. -/
def fixConst (S : State n) (w : ℕ) (b : Bool) : State n :=
  S.restrict w (Lit.const b) (S.pairsAvoid w)

theorem restrictOK_fixConst {S : State n} {w : ℕ} (hw : w ∈ S.params) (b : Bool) :
    S.RestrictOK w (Lit.const b) (S.pairsAvoid w) where
  mem := hw
  reads y hy := by simp [Lit.Reads, Lit.const] at hy
  subset := Finset.filter_subset _ _
  avoid pr hpr := (Finset.mem_filter.1 hpr).2
  drop pr hpr hP := by
    refine ⟨?_, fun y hy => by simp [Lit.Reads, Lit.const] at hy⟩
    by_contra h
    push Not at h
    exact hP (Finset.mem_filter.2 ⟨hpr, h⟩)

theorem Valid.fixConst {S : State n} (hS : S.Valid f) {w : ℕ} (hw : w ∈ S.params) (b : Bool) :
    (S.fixConst w b).Valid f :=
  hS.restrict (restrictOK_fixConst hw b)

@[simp] theorem fixConst_params (S : State n) (w : ℕ) (b : Bool) :
    (S.fixConst w b).params = S.params.erase w := rfl

@[simp] theorem fixConst_pairs (S : State n) (w : ℕ) (b : Bool) :
    (S.fixConst w b).pairs = S.pairsAvoid w := rfl

theorem fixConst_size (S : State n) (w : ℕ) (b : Bool) : (S.fixConst w b).size = S.size := rfl

theorem fixConst_m {S : State n} {w : ℕ} (hw : w ∈ S.params) (b : Bool) :
    (S.fixConst w b).m + 1 = S.m := by
  simp only [m, fixConst_params]
  exact Finset.card_erase_add_one hw

theorem fixConst_children (S : State n) {w : ℕ} (b : Bool) {z : ℕ} (hz : z ≠ w) : (S.fixConst w b).children z = S.children z :=
  SemiCircuit.children_subst hz (by simp [Lit.const])

/-- A pair containing `w` is unique. -/
theorem Valid.pair_unique {S : State n} (hS : S.Valid f) {w : ℕ} {pr pr' : ℕ × ℕ}
    (hpr : pr ∈ S.pairs) (hpr' : pr' ∈ S.pairs) (h : pr.1 = w ∨ pr.2 = w)
    (h' : pr'.1 = w ∨ pr'.2 = w) : pr = pr' := by
  by_contra hne
  have := hS.pairs_disjoint pr hpr pr' hpr' hne
  rcases h with rfl | rfl <;> rcases h' with h' | h' <;> tauto

theorem Valid.pairsAvoid_card {S : State n} (hS : S.Valid f) (w : ℕ) :
    (S.pairsAvoid w).card + (if S.Paired w then 1 else 0) = S.q := by
  unfold q pairsAvoid
  split_ifs with hw
  · obtain ⟨pr, hpr, hprw⟩ := hw
    have : S.pairs.filter (fun pr => pr.1 ≠ w ∧ pr.2 ≠ w) = S.pairs.erase pr := by
      ext pr'
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hpr', h1, h2⟩
        refine ⟨fun he => ?_, hpr'⟩
        subst he
        rcases hprw with h | h
        · exact h1 h
        · exact h2 h
      · rintro ⟨hne, hpr'⟩
        refine ⟨hpr', ?_⟩
        by_contra h
        push Not at h
        exact hne (hS.pair_unique hpr' hpr (by tauto) hprw)
    rw [this, Finset.card_erase_add_one hpr]
  · rw [add_zero]
    congr 1
    refine Finset.filter_true_of_mem fun pr hpr => ?_
    exact ⟨fun h => hw ⟨pr, hpr, Or.inl h⟩, fun h => hw ⟨pr, hpr, Or.inr h⟩⟩

/-- After fixing `w`, an unpaired parameter was unpaired before or was the partner of `w`. -/
theorem fixConst_unpaired {S : State n} {w : ℕ} {b : Bool} {u : ℕ}
    (hu : u ∈ (S.fixConst w b).unpaired) : u ∈ S.unpaired ∨ S.IsPartner w u := by
  obtain ⟨hup, hun⟩ := mem_unpaired.1 hu
  have huw : u ≠ w := Finset.ne_of_mem_erase hup
  by_cases hpu : S.Paired u
  · obtain ⟨pr, hpr, h⟩ := hpu
    by_cases hprw : pr.1 ≠ w ∧ pr.2 ≠ w
    · exact absurd ⟨pr, Finset.mem_filter.2 ⟨hpr, hprw⟩, h⟩ hun
    · right
      refine ⟨pr, hpr, ?_⟩
      push Not at hprw
      rcases h with h | h
      · exact Or.inr ⟨hprw (by rw [h]; exact huw), h⟩
      · by_cases h1 : pr.1 = w
        · exact Or.inl ⟨h1, h⟩
        · exact absurd (h.symm.trans (hprw h1)) huw
  · exact Or.inl (mem_unpaired.2 ⟨Finset.mem_of_mem_erase hup, hpu⟩)

/-- Fixing `w` keeps every other unpaired parameter unpaired. -/
theorem fixConst_mem_unpaired {S : State n} {w : ℕ} {b : Bool} {u : ℕ} (hu : u ∈ S.unpaired)
    (huw : u ≠ w) : u ∈ (S.fixConst w b).unpaired :=
  mem_unpaired.2 ⟨Finset.mem_erase.2 ⟨huw, (mem_unpaired.1 hu).1⟩,
    fun ⟨pr, hpr, h⟩ => (mem_unpaired.1 hu).2 ⟨pr, Finset.mem_of_mem_filter _ hpr, h⟩⟩

/-- A partner of a paired parameter is unique. -/
theorem Valid.isPartner_unique {S : State n} (hS : S.Valid f) {w r r' : ℕ}
    (h : S.IsPartner w r) (h' : S.IsPartner w r') : r = r' := by
  obtain ⟨pr, hpr, hr⟩ := h
  obtain ⟨pr', hpr', hr'⟩ := h'
  have := hS.pair_unique (w := w) hpr hpr'
    (by rcases hr with h | h; exacts [Or.inl h.1, Or.inr h.1])
    (by rcases hr' with h | h; exacts [Or.inl h.1, Or.inr h.1])
  subst this
  have h12 := (hS.pair_mem pr hpr).2.2
  rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hr' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · exact h2.symm.trans h2'
  · exact absurd (h1.trans h1'.symm) h12
  · exact absurd (h1'.trans h1.symm) h12
  · exact h2.symm.trans h2'

/-- The sum of an indicator of the partner of `w`. -/
theorem Valid.sum_partner_le {S : State n} (hS : S.Valid f) (w : ℕ) (N : Finset ℕ) (c : ℕ) :
    ∑ x ∈ N, (if S.IsPartner w x then c else 0) ≤ c := by
  classical
  by_cases h : ∃ r ∈ N, S.IsPartner w r
  · obtain ⟨r, hr, hpr⟩ := h
    rw [Finset.sum_eq_single_of_mem r hr fun x _ hxr => ite_eq_right fun hx =>
      hxr (hS.isPartner_unique hx hpr)]
    rw [ite_eq_left hpr]
  · push Not at h
    rw [Finset.sum_eq_zero fun x hx => ite_eq_right (h x hx)]
    omega

theorem isPartner_paired {S : State n} {w r : ℕ} (h : S.IsPartner w r) : S.Paired w ∧
    S.Paired r := by
  obtain ⟨pr, hpr, h⟩ := h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨⟨pr, hpr, Or.inl h1⟩, ⟨pr, hpr, Or.inr h2⟩⟩
  · exact ⟨⟨pr, hpr, Or.inr h1⟩, ⟨pr, hpr, Or.inl h2⟩⟩


/-! ### Case 2 -/

/-- An AND-type operation becomes constant when either argument takes a suitable value. -/
theorem exists_eq_of_not_isAffineOp {op : Bool → Bool → Bool} (h : ¬ IsAffineOp op) :
    (∃ b, op b false = op b true) ∧ (∃ b, op false b = op true b) := by
  unfold IsAffineOp at h
  constructor
  · by_cases h0 : op false false = op false true
    · exact ⟨false, h0⟩
    · by_cases h1 : op true false = op true true
      · exact ⟨true, h1⟩
      · exfalso
        apply h
        revert h0 h1
        generalize op false false = a; generalize op true false = b
        generalize op false true = c; generalize op true true = d
        revert a b c d; decide
  · by_cases h0 : op false false = op true false
    · exact ⟨false, h0⟩
    · by_cases h1 : op false true = op true true
      · exact ⟨true, h1⟩
      · exfalso
        apply h
        revert h0 h1
        generalize op false false = a; generalize op true false = b
        generalize op false true = c; generalize op true true = d
        revert a b c d; decide

/-- Fixing one argument of a gate reading two distinct internal values to a value that makes its
operation constant turns it into a degenerate gate computing a constant. -/
theorem lit_subst_const {g : Gate} {z w : ℕ} (hzw : z ≠ w) {b : Bool}
    (h : (g.left = .node z ∧ g.right = .node w ∧ g.op false b = g.op true b) ∨
      (g.left = .node w ∧ g.right = .node z ∧ g.op b false = g.op b true)) :
    (g.subst w (Lit.const b)).Degenerate ∧ (g.subst w (Lit.const b)).lit.target = none := by
  obtain ⟨op, l, r⟩ := g
  rcases h with ⟨hl, hr, hb⟩ | ⟨hl, hr, hb⟩
  · simp only at hl hr hb
    subst hl hr
    have hzw' : Arg.node z ≠ Arg.node w := fun h => hzw (Arg.node.inj h)
    refine ⟨Or.inr (Or.inl ⟨b, ?_⟩), ?_⟩
    · simp [Gate.subst, Arg.substArg, Lit.const]
    · simp [Gate.subst, Arg.substArg, Gate.substNeg, Lit.const, Gate.lit, hzw', hb, Lit.target]
  · simp only at hl hr hb
    subst hl hr
    have hzw' : Arg.node z ≠ Arg.node w := fun h => hzw (Arg.node.inj h)
    refine ⟨Or.inl ⟨b, ?_⟩, ?_⟩
    · simp [Gate.subst, Arg.substArg, Lit.const]
    · simp [Gate.subst, Arg.substArg, Gate.substNeg, Lit.const, Gate.lit, hzw', hb, Lit.target]

/-- Case 2 applies: an AND-type gate reads an unpaired isolated parameter `z` and another
parameter `w`. -/
def Case2 (S : State n) : Prop :=
  ∃ G ∈ S.gates, ∃ z w, ¬ IsAffineOp (S.gate G).op ∧
    (((S.gate G).left = .node z ∧ (S.gate G).right = .node w) ∨
      ((S.gate G).left = .node w ∧ (S.gate G).right = .node z)) ∧
    z ∈ S.unpaired ∧ S.deg z = 1 ∧ w ∈ S.params ∧ z ≠ w

/-- **Case 2** of the preliminary reductions: fix `w` so that the AND-type gate becomes
constant and delete it; `z` becomes unused. If `w` is unpaired, `Δa = -1` and `ΔW ≤ -14`;
otherwise the partner of `w` becomes unpaired, `Δa = 0` and `ΔW ≤ -4`. -/
theorem Valid.step_case2 {S : State n} (hS : S.Valid f) (h : S.Case2) : ∃ S', Step f S S' := by
  obtain ⟨G, hG, z, w, hand, hargs, hz, hz1, hw, hzw⟩ := h
  obtain ⟨⟨bl, hbl⟩, ⟨br, hbr⟩⟩ := exists_eq_of_not_isAffineOp hand
  -- the value of `w` making `G` constant
  obtain ⟨b, hb⟩ : ∃ b, ((S.gate G).left = .node z ∧ (S.gate G).right = .node w ∧
      (S.gate G).op false b = (S.gate G).op true b) ∨ ((S.gate G).left = .node w ∧
      (S.gate G).right = .node z ∧ (S.gate G).op b false = (S.gate G).op b true) := by
    rcases hargs with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact ⟨br, Or.inl ⟨hl, hr, hbr⟩⟩
    · exact ⟨bl, Or.inr ⟨hl, hr, hbl⟩⟩
  have hzp := (mem_unpaired.1 hz).1
  have hGz : (S.gate G).Reads z := by rcases hargs with ⟨hl, -⟩ | ⟨-, hr⟩; exacts [Or.inl hl, Or.inr hr]
  have hGw : (S.gate G).Reads w := by rcases hargs with ⟨-, hr⟩ | ⟨hl, -⟩; exacts [Or.inr hr, Or.inl hl]
  set S₁ := S.fixConst w b
  have hS₁ := hS.fixConst hw b
  obtain ⟨hdeg, htarget⟩ := lit_subst_const hzw hb
  have hok : S₁.DeleteGateOK G (S₁.gate G).lit :=
    ⟨hG, fun t ht => Gate.reads_of_lit_reads ht, Or.inl fun val _ => Gate.eval_lit hdeg val⟩
  have hstep := hS₁.delStep_deleteGate hok
  change DelStep f S₁ _ _ (S.gate G |>.subst w (Lit.const b)).lit.target at hstep
  rw [htarget] at hstep
  set S' := S₁.deleteGate G (S₁.gate G).lit
  have hparams : S'.params = S.params.erase w := rfl
  have hpairs : S'.pairs = S.pairsAvoid w := rfl
  have hsize : S'.size + 1 = S.size := hstep.size
  have hm : S'.m + 1 = S.m := fixConst_m hw b
  have hq := hS.pairsAvoid_card w
  have hchildren : ∀ u ∈ S'.params, S'.children u ⊆ (S.children u).erase (.inl G) := by
    intro u hu
    have := hstep.children u hu (by simp)
    rwa [fixConst_children S b (Finset.ne_of_mem_erase hu)] at this
  have hczG : S.children z = {.inl G} := by
    have hmem : Sum.inl G ∈ S.children z := (SemiCircuit.inl_mem_children _).2 ⟨hG, hGz⟩
    exact (Finset.card_eq_one.1 hz1).elim fun a ha => by
      rw [ha] at hmem ⊢; rw [Finset.mem_singleton.1 hmem]
  have hpt : ∀ u ∈ S.params, S'.wt u + ((if u = z then 6 else 0) +
      (if u = w ∧ w ∈ S.unpaired then 6 else 0)) ≤ S.wt u + (if S.IsPartner w u then 7 else 0) := by
    intro u hu
    by_cases huw : u = w
    · subst huw
      rw [wt_of_notMem_params (by simp [hparams]), ite_eq_right hzw.symm]
      by_cases hwu : u ∈ S.unpaired
      · rw [ite_eq_left ⟨rfl, hwu⟩, wt_of_mem hwu]
        have := six_le_weight (show 1 ≤ S.deg u from Finset.card_pos.2
          ⟨_, (SemiCircuit.inl_mem_children _).2 ⟨hG, hGw⟩⟩)
        omega
      · rw [ite_eq_right fun h => hwu h.2]; omega
    · rw [ite_eq_right (show ¬ (u = w ∧ w ∈ S.unpaired) from fun h => huw h.1)]
      have hu' : u ∈ S'.params := Finset.mem_erase.2 ⟨huw, hu⟩
      by_cases huz : u = z
      · subst huz
        have hdeg0 : S'.deg u = 0 := by
          have := hchildren u hu'
          rw [hczG, Finset.erase_singleton] at this
          exact Finset.card_eq_zero.2 (Finset.subset_empty.1 this)
        have h1 : S'.wt u = 0 := by unfold wt; split_ifs <;> simp [hdeg0]
        rw [h1, wt_of_mem hz, hz1, weight_one, ite_eq_left rfl]
        omega
      · rw [ite_eq_right huz]
        by_cases hu₁ : u ∈ S'.unpaired
        · rcases fixConst_unpaired (S := S) (w := w) (b := b) hu₁ with hus | hpart
          · rw [wt_of_mem hu₁, wt_of_mem hus]
            exact (weight_mono (Finset.card_le_card ((hchildren u hu').trans
              (Finset.erase_subset _ _)))).trans (Nat.le_add_right _ _)
          · rw [ite_eq_left hpart]
            have := S'.wt_le_seven u
            omega
        · rw [wt_of_notMem hu₁]; omega
  have hW := W_add_le (S := S) (S' := S') le_rfl (by rw [hparams]; exact Finset.erase_subset _ _)
    _ _ hpt
  rw [Finset.sum_add_distrib, sum_ite_eq_of_mem hzp] at hW
  have hgain := hS.sum_partner_le w S.params 7
  have hs : S'.s + 1 = S.s := hsize
  refine ⟨S', hstep.valid, by omega, ?_⟩
  by_cases hwp : S.Paired w
  · -- (PF): the pair of `w` is dropped
    have hwu : w ∉ S.unpaired := fun h => (mem_unpaired.1 h).2 hwp
    rw [Finset.sum_eq_zero fun u _ => ite_eq_right fun h => hwu h.2] at hW
    rw [ite_eq_left hwp] at hq
    have hq' : S'.q + 1 = S.q := by simpa [q, hpairs] using hq
    have ha' : S'.a = S.a := by simp only [a]; omega
    rw [ha']; omega
  · -- (UF): `w` is unpaired
    have hwu : w ∈ S.unpaired := mem_unpaired.2 ⟨hw, hwp⟩
    simp only [and_iff_left hwu] at hW
    rw [Finset.sum_ite_eq' S.params w, ite_eq_left hw] at hW
    rw [Finset.sum_eq_zero fun u _ => ite_eq_right fun h => hwp (isPartner_paired h).1] at hW
    rw [ite_eq_right hwp] at hq
    have hq' : S'.q = S.q := by simpa [q, hpairs] using hq
    have ha' : S.a ≤ S'.a + 1 := by simp only [a]; omega
    omega


/-! ### Consequences of the inapplicability of Cases 1 and 2 -/

/-- An affine gate reading no gates, which is moved into the affine system before the
preliminary reductions. -/
def Movable (S : State n) (J : ℕ) : Prop :=
  J ∈ S.gates ∧ IsAffineOp (S.gate J).op ∧ ∀ i, (S.gate J).Reads i → i ∉ S.gates

/-- No constraint has both an unpaired isolated parameter and another parameter as parents. -/
def Exclusive (S : State n) : Prop :=
  ∀ z ∈ S.unpaired, S.deg z = 1 → ∀ N ∈ S.children z, ∀ z' ∈ S.params, z' ≠ z →
    N ∉ S.children z'

/-- A gate reading two distinct internal values reads exactly them. -/
theorem Gate.args_of_reads {g : Gate} {z z' : ℕ} (hzz : z ≠ z') (hz : g.Reads z)
    (hz' : g.Reads z') : (g.left = .node z ∧ g.right = .node z') ∨
      (g.left = .node z' ∧ g.right = .node z) := by
  unfold Gate.Reads at hz hz'
  rcases hz with hz | hz <;> rcases hz' with hz' | hz'
  · exact absurd (Arg.node.inj (hz.symm.trans hz')) hzz
  · exact Or.inl ⟨hz, hz'⟩
  · exact Or.inr ⟨hz', hz⟩
  · exact absurd (Arg.node.inj (hz.symm.trans hz')) hzz

/-- **Consequence of Cases 1 and 2** of [Mishra and Santhanam][MishraSanthanam2026]: when no
affine gate can be moved, no deletion applies and Case 2 does not apply, the unique child of an
unpaired isolated parameter is a gate whose other input is not a parameter. -/
theorem exclusive_of {S : State n} (hS : S.Valid f) (hmov : ∀ J, ¬ S.Movable J)
    (hdel : ¬ S.DeletionAvailable) (h2 : ¬ S.Case2) : S.Exclusive := by
  intro z hz hz1 N hN z' hz' hzz hN'
  have hzp := (mem_unpaired.1 hz).1
  have hcz : S.children z = {N} := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hz1
    rw [ha] at hN ⊢; rw [Finset.mem_singleton.1 hN]
  rcases N with G | e
  · obtain ⟨hG, hGz⟩ := (SemiCircuit.inl_mem_children _).1 hN
    obtain ⟨-, hGz'⟩ := (SemiCircuit.inl_mem_children _).1 hN'
    have hargs := Gate.args_of_reads (Ne.symm hzz) hGz hGz'
    by_cases haff : IsAffineOp (S.gate G).op
    · refine hmov G ⟨hG, haff, fun i hi hig => ?_⟩
      have hip : i ∈ S.params := by
        rcases hargs with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> rcases hi with hi | hi
        · rw [hl] at hi; cases hi; exact hzp
        · rw [hr] at hi; cases hi; exact hz'
        · rw [hl] at hi; cases hi; exact hz'
        · rw [hr] at hi; cases hi; exact hzp
      exact Finset.disjoint_left.1 hS.wf.disjoint_params_gates hip hig
    · exact h2 ⟨G, hG, z, z', haff, hargs, hz, hz1, hz', Ne.symm hzz⟩
  · exact hdel (Or.inr (Or.inr (Or.inr ⟨z, hz, e, hcz⟩)))

/-- After restricting parameters to constants and deleting a chain of constraints, an unpaired
parameter `u` of an exclusive state does not gain weight, provided every deletion targeting `u`
deletes a constraint having another parameter as a parent. -/
theorem weight_le_of_chain {S S₁ S' : State n} {l : List ((ℕ ⊕ ℕ) × Option ℕ)}
    (hexcl : S.Exclusive) (hchain : Chain f S₁ S' l) {u : ℕ} (hu : u ∈ S.unpaired)
    (hu₁ : u ∈ S₁.params) (hc₁ : S₁.children u = S.children u)
    (hparents : ∀ q ∈ l, q.2 = some u → q.1 ∈ S.children u →
      ∃ r ∈ S.params, r ≠ u ∧ q.1 ∈ S.children r) :
    weight (S'.deg u) ≤ weight (S.deg u) := by
  rcases hchain.children_cases hu₁ with hsub | ⟨q, hq, hqu, hq₁⟩
  · refine weight_mono (Finset.card_le_card ?_)
    rw [← hc₁]; exact hsub.trans Finset.sdiff_subset
  · rw [hc₁] at hq₁
    obtain ⟨r, hr, hru, hqr⟩ := hparents q hq hqu hq₁
    have hdeg : 1 ≤ S.deg u := Finset.card_pos.2 ⟨_, hq₁⟩
    rcases Nat.lt_or_ge 1 (S.deg u) with h | h
    · rw [weight_of_two_le h]; exact weight_le_seven _
    · exact absurd hqr (hexcl u hu (by omega) q.1 hq₁ r hr hru)

/-- The children of a parameter `p` fixed to a constant are deletable. -/
theorem deletable_fixConst {S : State n} (hS : S.Valid f) {p : ℕ} (b : Bool) {N : ℕ ⊕ ℕ}
    (hN : N ∈ S.children p) : (S.fixConst p b).Deletable N := by
  rcases N with J | e
  · obtain ⟨hJ, hr⟩ := (SemiCircuit.inl_mem_children _).1 hN
    refine ⟨hJ, ?_⟩
    change ((S.gate J).subst p (Lit.const b)).Degenerate
    unfold Gate.Degenerate
    change (∃ c, (S.gate J).left.substArg p (Arg.const b) = .const c) ∨
      (∃ c, (S.gate J).right.substArg p (Arg.const b) = .const c) ∨ _
    rcases hr with hr | hr
    · exact Or.inl ⟨b, by rw [hr]; simp [Arg.substArg]⟩
    · exact Or.inr (Or.inl ⟨b, by rw [hr]; simp [Arg.substArg]⟩)
  · obtain ⟨he, hpe⟩ := (SemiCircuit.inr_mem_children _).1 hN
    refine ⟨he, ?_⟩
    change ((S.eqn e).subst p (Lit.const b)).terms.card ≤ 2
    have h3 := hS.wf.card_terms_le e he
    have : ((S.eqn e).subst p (Lit.const b)).terms = (S.eqn e).terms.erase p := by
      simp [Equation.subst, hpe, Lit.const]
    rw [this, Finset.card_erase_of_mem hpe]
    omega


/-! ### Case 3 -/

/-- A paired parameter has a partner. -/
theorem exists_partner {S : State n} {p : ℕ} (hp : S.Paired p) : ∃ r, S.IsPartner p r := by
  obtain ⟨pr, hpr, h⟩ := hp
  rcases h with h | h
  · exact ⟨pr.2, pr, hpr, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨pr.1, pr, hpr, Or.inr ⟨h, rfl⟩⟩

theorem Valid.partner_ne {S : State n} (hS : S.Valid f) {p r : ℕ} (h : S.IsPartner p r) :
    r ≠ p := by
  obtain ⟨pr, hpr, h⟩ := h
  have := (hS.pair_mem pr hpr).2.2
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2]; exact this.symm
  · rw [← h1, ← h2]; exact this

theorem Valid.partner_mem {S : State n} (hS : S.Valid f) {p r : ℕ} (h : S.IsPartner p r) :
    r ∈ S.params := by
  obtain ⟨pr, hpr, h⟩ := h
  rcases h with ⟨-, h2⟩ | ⟨-, h2⟩
  · rw [← h2]; exact (hS.pair_mem pr hpr).2.1
  · rw [← h2]; exact (hS.pair_mem pr hpr).1

theorem isPartner_symm {S : State n} {p r : ℕ} (h : S.IsPartner p r) : S.IsPartner r p := by
  obtain ⟨pr, hpr, h⟩ := h
  exact ⟨pr, hpr, by tauto⟩

/-- After fixing a parameter `w`, every unpaired parameter other than the partner of `w` was
unpaired. -/
theorem fixConst_unpaired_of_ne {S : State n} (hS : S.Valid f) {w r u : ℕ} {b : Bool}
    (hr : S.IsPartner w r ∨ ¬ S.Paired w) (hu : u ∈ (S.fixConst w b).unpaired) (hur : u ≠ r) :
    u ∈ S.unpaired := by
  rcases fixConst_unpaired hu with h | h
  · exact h
  · rcases hr with hr | hr
    · exact absurd (hS.isPartner_unique h hr) hur
    · exact absurd (isPartner_paired h).1 hr

/-- Case 3 applies: a paired parameter has degree `0` or at least `2`. -/
def Case3 (S : State n) : Prop :=
  ∃ p ∈ S.params, S.Paired p ∧ (S.deg p = 0 ∨ 2 ≤ S.deg p)

/-- **Case 3** of the preliminary reductions. If a paired parameter `p` is unused, fixing its
partner removes the pair: `Δa = 0`, `ΔW ≤ -3`. If `p` has two children, fixing `p` makes both
deletable; the partner becomes unpaired and no other weight grows: `Δa = 0`, `ΔW ≤ 0`. -/
theorem Valid.step_case3 {S : State n} (hS : S.Valid f) (hexcl : S.Exclusive) (h : S.Case3) :
    ∃ S', Step f S S' := by
  obtain ⟨p, hp, hpp, hdeg⟩ := h
  obtain ⟨r, hpr⟩ := exists_partner hpp
  have hrp := hS.partner_ne hpr
  have hr := hS.partner_mem hpr
  have hq := hS.pairsAvoid_card
  rcases hdeg with hdeg | hdeg
  · -- fix the partner `r`; `p` becomes unpaired and unused
    set S' := S.fixConst r false
    have hS' := hS.fixConst hr false
    have hm : S'.m + 1 = S.m := fixConst_m hr false
    have hqr := hq r
    rw [ite_eq_left (isPartner_paired hpr).2] at hqr
    have hq' : S'.q + 1 = S.q := hqr
    have hs : S'.s = S.s := rfl
    have hnot : r ∉ S'.params := Finset.notMem_erase r S.params
    have hpt : ∀ u ∈ S.params, S'.wt u + 0 ≤ S.wt u + 0 := by
      intro u hu
      by_cases hur : u = r
      · rw [hur, wt_of_notMem_params hnot]; omega
      · by_cases hu' : u ∈ S'.unpaired
        · rw [wt_of_mem hu']
          by_cases hup : u = p
          · subst hup
            have : S'.deg u = 0 := by
              change (S.fixConst r false).deg u = 0
              unfold SemiCircuit.deg
              rw [fixConst_children S false hur]
              exact hdeg
            rw [this]; simp
          · have hus := fixConst_unpaired_of_ne hS (Or.inl (isPartner_symm hpr)) hu' hup
            rw [wt_of_mem hus]
            change weight (SemiCircuit.deg _ u) + 0 ≤ _
            unfold SemiCircuit.deg
            rw [fixConst_children S false hur]
        · rw [wt_of_notMem hu']; omega
    have hW := W_add_le (S := S) (S' := S') le_rfl (Finset.erase_subset _ _) _ _ hpt
    simp only [Finset.sum_const_zero] at hW
    have ha' : S'.a = S.a := by simp only [a]; omega
    exact ⟨S', hS', by omega, by rw [ha']; omega⟩
  · -- fix `p`; two of its children become deletable
    obtain ⟨N₁, hN₁, N₂, hN₂, hne⟩ := Finset.one_lt_card.1 (show 1 < (S.children p).card from hdeg)
    set S₁ := S.fixConst p false
    have hS₁ := hS.fixConst hp false
    obtain ⟨S', tl, hchain, hmap⟩ := hS₁.exists_chain [N₁, N₂] (by simp [hne])
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro N (rfl | rfl)
          exacts [deletable_fixConst hS false hN₁, deletable_fixConst hS false hN₂])
    have hS' := hchain.valid hS₁
    have hparams : S'.params = S.params.erase p := hchain.params
    have hpairs : S'.pairs = S.pairsAvoid p := hchain.pairs
    have hsize : S'.size + 2 = S.size := by
      have := hchain.size
      have hlen : tl.length = 2 := by rw [← List.length_map Prod.fst, hmap]; rfl
      rw [hlen] at this
      exact this
    have hm : S'.m + 1 = S.m := by
      simp only [m, hparams]; exact Finset.card_erase_add_one hp
    have hqp := hq p
    rw [ite_eq_left hpp] at hqp
    have hq' : S'.q + 1 = S.q := by unfold q; rw [hpairs]; exact hqp
    have hnodes : ∀ q ∈ tl, q.1 ∈ S.children p := by
      intro q hq
      have : q.1 ∈ tl.map Prod.fst := List.mem_map_of_mem hq
      rw [hmap] at this
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with h | h <;> rw [h]
      exacts [hN₁, hN₂]
    have hpt : ∀ u ∈ S.params, S'.wt u + 0 ≤ S.wt u + (if S.IsPartner p u then 7 else 0) := by
      intro u hu
      by_cases hup : u = p
      · subst hup; rw [wt_of_notMem_params (by simp [hparams])]; omega
      · by_cases hu' : u ∈ S'.unpaired
        · by_cases hur : S.IsPartner p u
          · rw [ite_eq_left hur]; have := S'.wt_le_seven u; omega
          · rw [ite_eq_right hur]
            have hu₁ : u ∈ S₁.unpaired := by
              rw [unpaired_congr hchain.params hchain.pairs] at hu'; exact hu'
            have hus : u ∈ S.unpaired := by
              rcases fixConst_unpaired hu₁ with h | h
              · exact h
              · exact absurd h hur
            rw [wt_of_mem hu', wt_of_mem hus, add_zero, add_zero]
            refine weight_le_of_chain hexcl hchain hus (Finset.mem_erase.2 ⟨hup, hu⟩)
              (fixConst_children S false hup) fun q hq _ _ => ⟨p, hp, Ne.symm hup, hnodes q hq⟩
        · rw [wt_of_notMem hu']; omega
    have hW := W_add_le (S := S) (S' := S') le_rfl (by rw [hparams]; exact Finset.erase_subset _ _)
      _ _ hpt
    simp only [Finset.sum_const_zero] at hW
    have hgain := hS.sum_partner_le p S.params 7
    have hs : S'.s + 2 = S.s := hsize
    have ha' : S'.a = S.a := by simp only [a]; omega
    exact ⟨S', hS', by omega, by rw [ha']; omega⟩

end State

end Cslib.Circuits.Boolean.B2
