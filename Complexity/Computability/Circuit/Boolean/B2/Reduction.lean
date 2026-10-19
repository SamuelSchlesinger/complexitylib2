/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.B2.Potential

/-!
# Reductions and their accounting

Every reduction of the gate elimination of [Mishra and Santhanam, Section 4][MishraSanthanam2026]
restricts some parameters and then deletes some gates and equations. A *reduction*
(`State.Reduction f S S' F D T`) from `S` to `S'` restricts the parameters of `F`, each to a
constant or to a literal of a remaining parameter with at least its children, drops the pairs
meeting `F`, and then deletes the constraints of the list `D`. Only the deletions of the
constraints of `T` may reroute a constraint to a parameter; the others reroute to constants or to
non-parameters. Reductions compose (`State.Reduction.trans`), and are built from restrictions
(`State.Valid.reduction_restrict`, `State.Valid.reduction_fixConst`) and deletions
(`State.Valid.reduction_deleteGate`, `State.Valid.reduction_deleteEqn`,
`State.Valid.exists_reduction_deleteAll`).

The accounting is done once for all reductions:

* `Δm = -|F|`, `Δs = -|D|` and `Δq = -k`, where `k` is the number of pairs meeting `F`
  (`State.Reduction.m_add`, `State.Reduction.s_add`, `State.Reduction.q_add`);
* the unpaired parameters of `S'` are those of `S` outside `F`, together with the partners of
  members of `F` (`State.Reduction.mem_unpaired_iff`);
* a parameter that no deletion of `T` reroutes to keeps at most its children outside `D`
  (`State.Reduction.wt_le_weight`), and an unpaired parameter rerouted to only by deletions of
  constraints with another parameter as a parent does not gain weight in an *exclusive* state
  (`State.Reduction.wt_le_wt`);
* the potential: `W' + 2 |D| + 3 k + ∑_{x ∈ F} wt(x) ≤ W` plus the pointwise gains
  (`State.Reduction.W_le`), and a reduction with `W' + 14 |F| ≤ W + 14 k` is a step of gate
  elimination (`State.Reduction.step`).

## Main definitions

* `Cslib.Circuits.Boolean.B2.State.Step`: a step of gate elimination.
* `Cslib.Circuits.Boolean.B2.State.Reduction`: reductions.
* `Cslib.Circuits.Boolean.B2.State.Deletable`: constraints deletable by (D1) or (D3).
* `Cslib.Circuits.Boolean.B2.State.Exclusive`: no constraint has an unpaired isolated parameter
  and another parameter as parents.

## Main results

* `Cslib.Circuits.Boolean.B2.State.Reduction.W_le`: the potential of a reduction.
* `Cslib.Circuits.Boolean.B2.State.Reduction.step`: reductions as steps of gate elimination.
* `Cslib.Circuits.Boolean.B2.State.Valid.exists_reduction_deleteAll`: deleting deletable
  constraints.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.B2

open Finset

namespace State

variable {n : ℕ} {f : BooleanFunction n}

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

/-- An AND-type gate reading two internal values becomes constant once the value `w` is fixed
suitably. -/
theorem Gate.exists_const_of_not_isAffineOp {g : Gate} (hg : ¬ IsAffineOp g.op) {a w : ℕ}
    (hargs : (g.left = .node a ∧ g.right = .node w) ∨ (g.left = .node w ∧ g.right = .node a)) :
    ∃ b c, ∀ val : ℕ → Bool, val w = b → g.eval val = c := by
  obtain ⟨⟨bl, hbl⟩, ⟨br, hbr⟩⟩ := exists_eq_of_not_isAffineOp hg
  rcases hargs with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · refine ⟨br, g.op false br, fun val hw => ?_⟩
    rw [Gate.eval_of_args hl hr, hw]
    cases val a
    · rfl
    · exact hbr.symm
  · refine ⟨bl, g.op bl false, fun val hw => ?_⟩
    rw [Gate.eval_of_args hl hr, hw]
    cases val a
    · rfl
    · exact hbl.symm

/-- A step of gate elimination from `S` to `S'`, as in Lemma 4.2 of
[Mishra and Santhanam][MishraSanthanam2026]: `S'` is valid, `m + s` decreases,
`Δa ∈ {0, -1, -2}` and `ΔW ≤ 14 Δa`, written without subtraction. -/
structure Step (f : BooleanFunction n) (S S' : State n) : Prop where
  valid : S'.Valid f
  lt : S'.m + S'.s < S.m + S.s
  a_le : S'.a ≤ S.a
  le_a : S.a ≤ S'.a + 2
  potential : S'.W + 14 * S.a ≤ S.W + 14 * S'.a

/-! ### Pairs and partners -/

/-- `r` is the partner of `w`: they form a pair. -/
def IsPartner (S : State n) (w r : ℕ) : Prop :=
  ∃ pr ∈ S.pairs, (pr.1 = w ∧ pr.2 = r) ∨ (pr.2 = w ∧ pr.1 = r)

instance (S : State n) (w : ℕ) : DecidablePred (S.IsPartner w) :=
  fun _ => inferInstanceAs (Decidable (∃ pr ∈ S.pairs, _))

/-- The pairs avoiding `w`. -/
def pairsAvoid (S : State n) (w : ℕ) : Finset (ℕ × ℕ) :=
  S.pairs.filter fun pr => pr.1 ≠ w ∧ pr.2 ≠ w

/-- The pairs with a member in `F`. -/
def pairsMeeting (S : State n) (F : Finset ℕ) : Finset (ℕ × ℕ) :=
  S.pairs.filter fun pr => pr.1 ∈ F ∨ pr.2 ∈ F

theorem paired_congr {S S' : State n} (h : S'.pairs = S.pairs) {x : ℕ} :
    S'.Paired x ↔ S.Paired x := by
  unfold Paired; rw [h]

theorem unpaired_congr {S S' : State n} (hp : S'.params = S.params) (h : S'.pairs = S.pairs) :
    S'.unpaired = S.unpaired := by
  ext x
  rw [mem_unpaired, mem_unpaired, hp, paired_congr h]

theorem Valid.mem_params_of_paired {S : State n} (hS : S.Valid f) {p : ℕ} (hp : S.Paired p) :
    p ∈ S.params := by
  obtain ⟨pr, hpr, h | h⟩ := hp
  · rw [← h]; exact (hS.pair_mem pr hpr).1
  · rw [← h]; exact (hS.pair_mem pr hpr).2.1

/-- A pair containing `w` is unique. -/
theorem Valid.pair_unique {S : State n} (hS : S.Valid f) {w : ℕ} {pr pr' : ℕ × ℕ}
    (hpr : pr ∈ S.pairs) (hpr' : pr' ∈ S.pairs) (h : pr.1 = w ∨ pr.2 = w)
    (h' : pr'.1 = w ∨ pr'.2 = w) : pr = pr' := by
  by_contra hne
  have := hS.pairs_disjoint pr hpr pr' hpr' hne
  rcases h with rfl | rfl <;> rcases h' with h' | h' <;> tauto

theorem exists_partner {S : State n} {p : ℕ} (hp : S.Paired p) : ∃ r, S.IsPartner p r := by
  obtain ⟨pr, hpr, h | h⟩ := hp
  · exact ⟨pr.2, pr, hpr, Or.inl ⟨h, rfl⟩⟩
  · exact ⟨pr.1, pr, hpr, Or.inr ⟨h, rfl⟩⟩

theorem IsPartner.symm {S : State n} {p r : ℕ} (h : S.IsPartner p r) : S.IsPartner r p := by
  obtain ⟨pr, hpr, h⟩ := h
  exact ⟨pr, hpr, by tauto⟩

theorem IsPartner.paired {S : State n} {w r : ℕ} (h : S.IsPartner w r) : S.Paired w := by
  obtain ⟨pr, hpr, ⟨h1, -⟩ | ⟨h1, -⟩⟩ := h
  · exact ⟨pr, hpr, Or.inl h1⟩
  · exact ⟨pr, hpr, Or.inr h1⟩

theorem Valid.partner_ne {S : State n} (hS : S.Valid f) {p r : ℕ} (h : S.IsPartner p r) :
    r ≠ p := by
  obtain ⟨pr, hpr, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · rw [← h1, ← h2]; exact (hS.pair_mem pr hpr).2.2.symm
  · rw [← h1, ← h2]; exact (hS.pair_mem pr hpr).2.2

theorem Valid.partner_mem {S : State n} (hS : S.Valid f) {p r : ℕ} (h : S.IsPartner p r) :
    r ∈ S.params :=
  hS.mem_params_of_paired h.symm.paired

/-- A partner is unique. -/
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

/-- The partners of `w` contribute at most one summand. -/
theorem Valid.sum_partner_le {S : State n} (hS : S.Valid f) (w : ℕ) (N : Finset ℕ) (c : ℕ) :
    ∑ x ∈ N, (if S.IsPartner w x then c else 0) ≤ c := by
  classical
  by_cases h : ∃ r ∈ N, S.IsPartner w r
  · obtain ⟨r, hr, hpr⟩ := h
    rw [Finset.sum_eq_single_of_mem r hr fun x _ hxr => ite_eq_right fun hx =>
      hxr (hS.isPartner_unique hx hpr), ite_eq_left hpr]
  · push Not at h
    rw [Finset.sum_eq_zero fun x hx => ite_eq_right (h x hx)]
    omega

/-- A paired parameter outside `F` is in a pair meeting `F` exactly when its partner is in
`F`. -/
theorem Valid.paired_filter_iff {S : State n} (hS : S.Valid f) {F : Finset ℕ} {u : ℕ}
    (huF : u ∉ F) : (∃ pr ∈ S.pairs.filter (fun pr => ¬ (pr.1 ∈ F ∨ pr.2 ∈ F)),
      pr.1 = u ∨ pr.2 = u) ↔ S.Paired u ∧ ∀ x ∈ F, ¬ S.IsPartner u x := by
  constructor
  · rintro ⟨pr, hpr, hu⟩
    obtain ⟨hpr, hF⟩ := Finset.mem_filter.1 hpr
    refine ⟨⟨pr, hpr, hu⟩, fun x hx ⟨pr', hpr', hux⟩ => hF ?_⟩
    have := hS.pair_unique hpr hpr' hu (by rcases hux with h | h; exacts [Or.inl h.1, Or.inr h.1])
    subst this
    rcases hux with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr (h ▸ hx)
    · exact Or.inl (h ▸ hx)
  · rintro ⟨⟨pr, hpr, hu⟩, hpart⟩
    refine ⟨pr, Finset.mem_filter.2 ⟨hpr, ?_⟩, hu⟩
    rintro (h | h) <;> rcases hu with hu | hu
    · exact huF (hu ▸ h)
    · exact hpart _ h ⟨pr, hpr, Or.inr ⟨hu, rfl⟩⟩
    · exact hpart _ h ⟨pr, hpr, Or.inl ⟨hu, rfl⟩⟩
    · exact huF (hu ▸ h)

/-- The parameters of a valid state are at least as many as its pairs. -/
theorem Valid.q_le_m {S : State n} (hS : S.Valid f) : S.q ≤ S.m := by
  have hsub : S.pairs.image Prod.fst ⊆ S.params := fun i hi => by
    obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.1 hi
    exact (hS.pair_mem pr hpr).1
  have hinj : Set.InjOn Prod.fst (S.pairs : Set (ℕ × ℕ)) := fun pr hpr pr' hpr' h =>
    hS.pair_unique hpr hpr' (Or.inl rfl) (Or.inl h.symm)
  have := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hinj] at this

/-- At most `|F|` pairs meet a set `F` of parameters. -/
theorem Valid.card_pairsMeeting_le {S : State n} (hS : S.Valid f) (F : Finset ℕ) :
    (S.pairsMeeting F).card ≤ F.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun pr => if pr.1 ∈ F then pr.1 else pr.2)
    (fun pr hpr => ?_) (fun pr hpr pr' hpr' h => ?_)
  · obtain ⟨-, h⟩ := Finset.mem_filter.1 hpr
    by_cases h1 : pr.1 ∈ F
    · simp only [ite_eq_left h1]; exact h1
    · simp only [ite_eq_right h1]; exact h.resolve_left h1
  · obtain ⟨hpr, -⟩ := Finset.mem_filter.1 hpr
    obtain ⟨hpr', -⟩ := Finset.mem_filter.1 hpr'
    simp only at h
    refine hS.pair_unique hpr hpr' (w := if pr.1 ∈ F then pr.1 else pr.2)
      (by split_ifs <;> simp) ?_
    rw [h]; split_ifs <;> simp

theorem Valid.card_pairsMeeting_singleton {S : State n} (hS : S.Valid f) (w : ℕ) :
    (S.pairsMeeting {w}).card = if S.Paired w then 1 else 0 := by
  split_ifs with hw
  · obtain ⟨pr, hpr, hprw⟩ := hw
    rw [Finset.card_eq_one]
    refine ⟨pr, Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2 ⟨hpr, by simpa⟩,
      fun pr' hpr' => ?_⟩⟩
    obtain ⟨hpr', h⟩ := Finset.mem_filter.1 hpr'
    exact hS.pair_unique hpr' hpr (by simpa using h) hprw
  · refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun pr hpr h => hw ?_)
    exact ⟨pr, hpr, by simpa [eq_comm] using h⟩

/-- Adding to `F` a parameter that is not the partner of a member of `F` adds its pair, if
any. -/
theorem Valid.card_pairsMeeting_insert {S : State n} (hS : S.Valid f) {F : Finset ℕ} {x : ℕ}
    (hx : x ∉ F) (hpart : ∀ y ∈ F, ¬ S.IsPartner x y) :
    (S.pairsMeeting (insert x F)).card =
      (S.pairsMeeting F).card + if S.Paired x then 1 else 0 := by
  rw [← hS.card_pairsMeeting_singleton x, ← Finset.card_union_of_disjoint]
  · congr 1
    ext pr
    simp only [pairsMeeting, Finset.mem_union, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    tauto
  · rw [Finset.disjoint_left]
    intro pr h₁ h₂
    obtain ⟨hpr, h₁⟩ := Finset.mem_filter.1 h₁
    obtain ⟨-, h₂⟩ := Finset.mem_filter.1 h₂
    simp only [Finset.mem_singleton] at h₂
    rcases h₂ with h₂ | h₂ <;> rcases h₁ with h₁ | h₁
    · exact hx (h₂ ▸ h₁)
    · exact hpart _ h₁ ⟨pr, hpr, Or.inl ⟨h₂, rfl⟩⟩
    · exact hpart _ h₁ ⟨pr, hpr, Or.inr ⟨h₂, rfl⟩⟩
    · exact hx (h₂ ▸ h₁)

/-! ### Exclusive states -/

/-- No constraint has both an unpaired isolated parameter and another parameter as parents. -/
def Exclusive (S : State n) : Prop :=
  ∀ z ∈ S.unpaired, S.deg z = 1 → ∀ N ∈ S.children z, ∀ z' ∈ S.params, z' ≠ z →
    N ∉ S.children z'

/-- In an exclusive state, an unpaired parameter sharing a child with another parameter has
degree at least two. -/
theorem Exclusive.two_le_deg {S : State n} (h : S.Exclusive) {u x : ℕ} {N : ℕ ⊕ ℕ}
    (hu : u ∈ S.unpaired) (hNu : N ∈ S.children u) (hx : x ∈ S.params) (hxu : x ≠ u)
    (hNx : N ∈ S.children x) : 2 ≤ S.deg u := by
  have : 1 ≤ S.deg u := Finset.card_pos.2 ⟨N, hNu⟩
  by_contra hlt
  exact h u hu (by omega) N hNu x hx hxu hNx

/-! ### Deletable constraints -/

/-- The children of a parameter fixed to a constant are deletable. -/
theorem deletable_fixConst_child {S : State n} (hS : S.Valid f) {p : ℕ} (P : Finset (ℕ × ℕ))
    (b : Bool) {N : ℕ ⊕ ℕ} (hN : N ∈ S.children p) :
    (S.restrict p (Lit.const b) P).Deletable N := by
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

/-- After deleting the gate `J` rerouted to a constant, the gates reading `J` are deletable. -/
theorem deletable_deleteGate_child {S : State n} {J K : ℕ} (c : Bool) (hK : K ∈ S.gates)
    (hKJ : K ≠ J) (hr : (S.gate K).Reads J) :
    (S.deleteGate J (Lit.const c)).Deletable (.inl K) := by
  refine ⟨Finset.mem_erase.2 ⟨hKJ, hK⟩, ?_⟩
  change ((S.gate K).subst J (Lit.const c)).Degenerate
  unfold Gate.Degenerate
  change (∃ b, (S.gate K).left.substArg J (Arg.const c) = .const b) ∨
    (∃ b, (S.gate K).right.substArg J (Arg.const c) = .const b) ∨ _
  rcases hr with hr | hr
  · exact Or.inl ⟨c, by rw [hr]; simp [Arg.substArg]⟩
  · exact Or.inr (Or.inl ⟨c, by rw [hr]; simp [Arg.substArg]⟩)

/-! ### Reductions -/

/-- A reduction from `S` to `S'`: the parameters of `F` are restricted, each to a constant or to
a literal of a remaining parameter having at least its children, the pairs meeting `F` are
dropped, and the constraints of `D` are deleted. The children of a remaining parameter lose the
deleted constraints and gain none, unless a deletion of a constraint of `T` that was one of its
children reroutes to it; and the other constraints stay deletable. -/
structure Reduction (f : BooleanFunction n) (S S' : State n) (F : Finset ℕ)
    (D T : List (ℕ ⊕ ℕ)) : Prop where
  valid : S'.Valid f
  subset : F ⊆ S.params
  params : S'.params = S.params \ F
  pairs : S'.pairs = S.pairs.filter fun pr => ¬ (pr.1 ∈ F ∨ pr.2 ∈ F)
  size : S'.size + D.length = S.size
  children : ∀ u ∈ S'.params,
    S'.children u ⊆ S.children u \ D.toFinset ∨ ∃ N ∈ T, N ∈ S.children u
  deletable : ∀ N, N ∉ D → S.Deletable N → S'.Deletable N

namespace Reduction

variable {S S' : State n} {F : Finset ℕ} {D T : List (ℕ ⊕ ℕ)}

theorem refl (hS : S.Valid f) : Reduction f S S ∅ [] [] where
  valid := hS
  subset := Finset.empty_subset _
  params := (Finset.sdiff_empty).symm
  pairs := (Finset.filter_true_of_mem fun _ _ => by simp).symm
  size := rfl
  children _ _ := Or.inl (by simp)
  deletable _ _ h := h

/-- Reductions compose. -/
theorem trans {S₁ S₂ : State n} {F₁ F₂ : Finset ℕ} {D₁ D₂ T₁ T₂ : List (ℕ ⊕ ℕ)}
    (h₁ : Reduction f S S₁ F₁ D₁ T₁) (h₂ : Reduction f S₁ S₂ F₂ D₂ T₂) :
    Reduction f S S₂ (F₁ ∪ F₂) (D₁ ++ D₂) (T₁ ++ T₂) where
  valid := h₂.valid
  subset := Finset.union_subset h₁.subset ((h₂.subset.trans h₁.params.le).trans sdiff_subset)
  params := by
    rw [h₂.params, h₁.params]
    ext u
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  pairs := by
    rw [h₂.pairs, h₁.pairs, Finset.filter_filter]
    exact Finset.filter_congr fun pr _ => by simp only [Finset.mem_union]; tauto
  size := by rw [List.length_append, ← h₁.size, ← h₂.size]; omega
  children u hu := by
    have hu₁ : u ∈ S₁.params := (h₂.params.le hu |> Finset.mem_sdiff.1).1
    rcases h₂.children u hu with h₂' | ⟨N, hN, hNu⟩ <;> rcases h₁.children u hu₁ with h₁' | h₁'
    · refine Or.inl fun N hN => ?_
      have h₂N := Finset.mem_sdiff.1 (h₂' hN)
      have h₁N := Finset.mem_sdiff.1 (h₁' h₂N.1)
      simp only [Finset.mem_sdiff, List.toFinset_append, Finset.mem_union, not_or]
      exact ⟨h₁N.1, h₁N.2, h₂N.2⟩
    · obtain ⟨N, hN, hNu⟩ := h₁'
      exact Or.inr ⟨N, List.mem_append_left _ hN, hNu⟩
    · exact Or.inr ⟨N, List.mem_append_right _ hN, (Finset.mem_sdiff.1 (h₁' hNu)).1⟩
    · obtain ⟨N, hN, hNu⟩ := h₁'
      exact Or.inr ⟨N, List.mem_append_left _ hN, hNu⟩
  deletable N hN h := by
    rw [List.mem_append, not_or] at hN
    exact h₂.deletable N hN.2 (h₁.deletable N hN.1 h)

/-- A reduction may record more deletions as possibly rerouting to parameters. -/
theorem mono (h : Reduction f S S' F D T) {T' : List (ℕ ⊕ ℕ)} (hT : ∀ N ∈ T, N ∈ T') :
    Reduction f S S' F D T' :=
  { h with
    children := fun u hu => (h.children u hu).imp_right fun ⟨N, hN, hNu⟩ => ⟨N, hT N hN, hNu⟩ }

/-! ### Accounting -/

theorem m_add (h : Reduction f S S' F D T) : S'.m + F.card = S.m := by
  unfold m
  rw [h.params, Finset.card_sdiff_of_subset h.subset]
  have := Finset.card_le_card h.subset
  omega

theorem s_add (h : Reduction f S S' F D T) : S'.s + D.length = S.s :=
  h.size

theorem q_add (h : Reduction f S S' F D T) : S'.q + (S.pairsMeeting F).card = S.q := by
  unfold q pairsMeeting
  rw [h.pairs, add_comm]
  exact Finset.card_filter_add_card_filter_not _

theorem a_add (h : Reduction f S S' F D T) (hS : S.Valid f) :
    S'.a + F.card = S.a + (S.pairsMeeting F).card := by
  have hm := h.m_add
  have hq := h.q_add
  have hk := hS.card_pairsMeeting_le F
  have hqm := h.valid.q_le_m
  unfold a
  omega

/-- The unpaired parameters after a reduction: the unpaired parameters outside `F` and the
partners of members of `F`. -/
theorem mem_unpaired_iff (h : Reduction f S S' F D T) (hS : S.Valid f) {u : ℕ} :
    u ∈ S'.unpaired ↔ u ∈ S.params ∧ u ∉ F ∧ (¬ S.Paired u ∨ ∃ x ∈ F, S.IsPartner x u) := by
  rw [mem_unpaired, h.params, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hu, huF⟩, hun⟩
    refine ⟨hu, huF, ?_⟩
    by_contra hc
    push Not at hc
    exact hun (by
      unfold Paired; rw [h.pairs]
      exact (hS.paired_filter_iff huF).2 ⟨hc.1, fun x hx hux => hc.2 x hx hux.symm⟩)
  · rintro ⟨hu, huF, hc⟩
    refine ⟨⟨hu, huF⟩, fun hp => ?_⟩
    unfold Paired at hp
    rw [h.pairs] at hp
    obtain ⟨hpu, hpart⟩ := (hS.paired_filter_iff huF).1 hp
    rcases hc with hc | ⟨x, hx, hux⟩
    · exact hc hpu
    · exact hpart x hx hux.symm

/-- A paired parameter that is not the partner of a member of `F` stays paired. -/
theorem wt_eq_zero (h : Reduction f S S' F D T) (hS : S.Valid f) {u : ℕ} (hu : u ∉ S.unpaired)
    (hpart : ∀ x ∈ F, ¬ S.IsPartner x u) : S'.wt u = 0 := by
  refine wt_of_notMem fun hu' => ?_
  obtain ⟨hup, -, hc⟩ := (h.mem_unpaired_iff hS).1 hu'
  rcases hc with hc | ⟨x, hx, hxu⟩
  · exact hu (mem_unpaired.2 ⟨hup, hc⟩)
  · exact hpart x hx hxu

/-- A parameter that no deletion of `T` reroutes to keeps at most its children outside `D`. -/
theorem wt_le_weight (h : Reduction f S S' F D T) {u : ℕ} (hT : ∀ N ∈ T, N ∉ S.children u) :
    S'.wt u ≤ weight (S.children u \ D.toFinset).card := by
  by_cases hu : u ∈ S'.unpaired
  · rw [wt_of_mem hu]
    refine weight_mono (Finset.card_le_card ?_)
    rcases h.children u (mem_unpaired.1 hu).1 with h' | ⟨N, hN, hNu⟩
    · exact h'
    · exact absurd hNu (hT N hN)
  · rw [wt_of_notMem hu]; exact Nat.zero_le _

/-- A parameter that no deletion of `T` reroutes to keeps at most its children outside `D`. -/
theorem children_subset (h : Reduction f S S' F D T) {u : ℕ} (hu : u ∈ S'.params)
    (hT : ∀ N ∈ T, N ∉ S.children u) : S'.children u ⊆ S.children u \ D.toFinset :=
  (h.children u hu).resolve_right fun ⟨N, hN, hNu⟩ => hT N hN hNu

/-- A parameter that is not the partner of a member of `F`, and that no deletion reroutes to,
does not gain weight. -/
theorem wt_le (h : Reduction f S S' F D T) (hS : S.Valid f) {u : ℕ}
    (hpart : ∀ x ∈ F, ¬ S.IsPartner x u) (hT : ∀ N ∈ T, N ∉ S.children u) :
    S'.wt u ≤ S.wt u := by
  by_cases hu : u ∈ S.unpaired
  · rw [wt_of_mem hu]
    exact (h.wt_le_weight hT).trans (weight_mono (Finset.card_le_card Finset.sdiff_subset))
  · rw [h.wt_eq_zero hS hu hpart]; exact Nat.zero_le _

/-- A used parameter that is not the partner of a member of `F` gains at most one in weight. -/
theorem wt_le_add_one (h : Reduction f S S' F D T) (hS : S.Valid f) {u : ℕ}
    (hpart : ∀ x ∈ F, ¬ S.IsPartner x u) (hdeg : 1 ≤ S.deg u) : S'.wt u ≤ S.wt u + 1 := by
  by_cases hu : u ∈ S.unpaired
  · rw [wt_of_mem hu]
    have := six_le_weight hdeg
    have := S'.wt_le_seven u
    omega
  · rw [h.wt_eq_zero hS hu hpart]; exact Nat.zero_le _

/-- A parameter all of whose children are deleted, and that no deletion reroutes to, becomes
unused. -/
theorem wt_eq_zero_of_subset (h : Reduction f S S' F D T) {u : ℕ}
    (hsub : S.children u ⊆ D.toFinset) (hT : ∀ N ∈ T, N ∉ S.children u) : S'.wt u = 0 := by
  have := h.wt_le_weight hT
  rwa [Finset.sdiff_eq_empty_iff_subset.2 hsub, Finset.card_empty, weight_zero,
    Nat.le_zero] at this

/-- In an exclusive state, an unpaired parameter does not gain weight when every deletion that
may reroute to it deletes a constraint with another parameter as a parent. -/
theorem wt_le_wt (h : Reduction f S S' F D T) (hexcl : S.Exclusive) {u : ℕ}
    (hu : u ∈ S.unpaired)
    (hT : ∀ N ∈ T, N ∈ S.children u → ∃ x ∈ S.params, x ≠ u ∧ N ∈ S.children x) :
    S'.wt u ≤ S.wt u := by
  by_cases hu' : u ∈ S'.unpaired
  · rw [wt_of_mem hu]
    by_cases hN : ∃ N ∈ T, N ∈ S.children u
    · obtain ⟨N, hN, hNu⟩ := hN
      obtain ⟨x, hx, hxu, hNx⟩ := hT N hN hNu
      rw [weight_of_two_le (hexcl.two_le_deg hu hNu hx hxu hNx)]
      exact S'.wt_le_seven u
    · push Not at hN
      exact (h.wt_le_weight hN).trans
        (weight_mono (Finset.card_le_card Finset.sdiff_subset))
  · rw [wt_of_notMem hu']; exact Nat.zero_le _

/-- In an exclusive state, a parameter that is not the partner of a member of `F` does not gain
weight when every deletion that may reroute to it deletes a constraint with another parameter as a
parent. -/
theorem wt_le_of_exclusive (h : Reduction f S S' F D T) (hS : S.Valid f) (hexcl : S.Exclusive)
    {u : ℕ} (hpart : ∀ x ∈ F, ¬ S.IsPartner x u)
    (hT : ∀ N ∈ T, N ∈ S.children u → ∃ x ∈ S.params, x ≠ u ∧ N ∈ S.children x) :
    S'.wt u ≤ S.wt u := by
  by_cases hu : u ∈ S.unpaired
  · exact h.wt_le_wt hexcl hu hT
  · rw [h.wt_eq_zero hS hu hpart]; exact Nat.zero_le _

/-- **The potential of a reduction.** If every parameter outside `F` gains at most `gain` and
loses at least `loss` in weight, then
`W' + 2 |D| + 3 k + ∑_{x ∈ F} wt(x) + ∑ loss ≤ W + ∑ gain`, where `k` is the number of pairs
meeting `F`. -/
theorem W_le (h : Reduction f S S' F D T) (loss gain : ℕ → ℕ)
    (hpt : ∀ u ∈ S.params \ F, S'.wt u + loss u ≤ S.wt u + gain u) :
    S'.W + 2 * D.length + 3 * (S.pairsMeeting F).card + ∑ u ∈ F, S.wt u +
        ∑ u ∈ S.params \ F, loss u ≤ S.W + ∑ u ∈ S.params \ F, gain u := by
  have hW := W_add_le (S := S) (S' := S') (N := S.params) le_rfl
    (by rw [h.params]; exact Finset.sdiff_subset)
    (fun u => if u ∈ F then S.wt u else loss u) (fun u => if u ∈ F then 0 else gain u)
    fun u hu => by
      by_cases huF : u ∈ F
      · simp only [ite_eq_left huF, wt_of_notMem_params (show u ∉ S'.params by
          rw [h.params]; exact fun h' => (Finset.mem_sdiff.1 h').2 huF)]
        omega
      · simp only [ite_eq_right huF]
        exact hpt u (Finset.mem_sdiff.2 ⟨hu, huF⟩)
  have hsplit : ∀ g : ℕ → ℕ, ∑ u ∈ S.params, g u =
      ∑ u ∈ S.params \ F, g u + ∑ u ∈ F, g u := fun g => (Finset.sum_sdiff h.subset).symm
  rw [hsplit, hsplit (fun u => if u ∈ F then 0 else gain u),
    Finset.sum_congr rfl (g := fun u => loss u) fun u hu => ite_eq_right (Finset.mem_sdiff.1 hu).2,
    Finset.sum_congr rfl (g := fun u => S.wt u) fun u hu => ite_eq_left hu,
    Finset.sum_congr rfl (g := fun u => gain u) fun u hu => ite_eq_right (Finset.mem_sdiff.1 hu).2,
    Finset.sum_congr rfl (g := fun _ => 0) fun u hu => ite_eq_left hu, Finset.sum_const_zero] at hW
  have hs := h.s_add
  have hq := h.q_add
  omega

/-- A reduction restricting at most two parameters, and at least one parameter or constraint,
with `W' + 14 |F| ≤ W + 14 k`, is a step of gate elimination. -/
theorem step (h : Reduction f S S' F D T) (hS : S.Valid f) (hF : F.card ≤ 2)
    (hne : 0 < F.card + D.length)
    (hW : S'.W + 14 * F.card ≤ S.W + 14 * (S.pairsMeeting F).card) : Step f S S' := by
  have ha := h.a_add hS
  have hm := h.m_add
  have hs := h.s_add
  have hk := hS.card_pairsMeeting_le F
  exact ⟨h.valid, by omega, by omega, by omega, by omega⟩

/-- Deleting one constraint with at most two parameters as parents is a step of gate
elimination: only those parents may gain weight, each at most one. -/
theorem step_of_delete {N : ℕ ⊕ ℕ} (h : Reduction f S S' ∅ [N] [N]) (hS : S.Valid f)
    (hN : (S.params.filter fun u => N ∈ S.children u).card ≤ 2) : Step f S S' := by
  refine h.step hS (by simp) (by simp) ?_
  have hW := h.W_le (fun _ => 0) (fun u => if N ∈ S.children u then 1 else 0) fun u hu => by
    by_cases hNu : N ∈ S.children u
    · rw [ite_eq_left hNu]
      exact Nat.add_le_add_right (h.wt_le_add_one hS (fun _ hx => absurd hx (Finset.notMem_empty _))
        (Finset.card_pos.2 ⟨N, hNu⟩)) 0
    · rw [ite_eq_right hNu]
      exact Nat.add_le_add_right (h.wt_le hS (fun _ hx => absurd hx (Finset.notMem_empty _))
        fun N' hN' => by rw [List.mem_singleton] at hN'; exact hN' ▸ hNu) 0
  rw [Finset.sdiff_empty, ← Finset.card_filter] at hW
  simp only [Finset.card_empty, Finset.sum_empty, Finset.sum_const_zero, List.length_singleton,
    mul_zero, add_zero] at hW ⊢
  omega

end Reduction

/-! ### Restrictions -/

/-- Restricting a parameter `x` to a constant, or to a literal of a remaining parameter `y` with
at least the children of `x` and, if `x` is paired, its partner, is a reduction. -/
theorem Valid.reduction_restrict {S : State n} (hS : S.Valid f) {x : ℕ} (hx : x ∈ S.params)
    {ℓ : Lit} (hℓ : ∀ y, ℓ.Reads y → y ∈ S.params ∧ y ≠ x ∧ S.children x ⊆ S.children y ∧
      (S.Paired x → S.IsPartner x y)) :
    Reduction f S (S.restrict x ℓ (S.pairsAvoid x)) {x} [] [] where
  valid := hS.restrict
    { mem := hx
      reads := fun y hy => ⟨(hℓ y hy).1, (hℓ y hy).2.1⟩
      subset := Finset.filter_subset _ _
      avoid := fun pr hpr => (Finset.mem_filter.1 hpr).2
      drop := fun pr hpr hP => by
        have hprx : pr.1 = x ∨ pr.2 = x := by
          by_contra hc
          push Not at hc
          exact hP (Finset.mem_filter.2 ⟨hpr, hc⟩)
        refine ⟨hprx, fun y hy => ?_⟩
        obtain ⟨pr', hpr', hxy⟩ := (hℓ y hy).2.2.2 ⟨pr, hpr, hprx⟩
        have := hS.pair_unique hpr hpr' hprx
          (by rcases hxy with h | h; exacts [Or.inl h.1, Or.inr h.1])
        subst this
        rcases hxy with ⟨-, h⟩ | ⟨-, h⟩
        · exact Or.inr h.symm
        · exact Or.inl h.symm }
  subset := Finset.singleton_subset_iff.2 hx
  params := by
    ext u
    simp only [restrict_params, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton]
    tauto
  pairs := Finset.filter_congr fun pr _ => by simp only [Finset.mem_singleton, not_or]
  size := by rw [List.length_nil, add_zero]; rfl
  children u hu := by
    refine Or.inl ?_
    rw [List.toFinset_nil, Finset.sdiff_empty, restrict_children]
    have hux : u ≠ x := Finset.ne_of_mem_erase hu
    by_cases hℓu : ℓ.Reads u
    · exact (SemiCircuit.children_subst_subset x ℓ u).trans
        (Finset.union_subset le_rfl (hℓ u hℓu).2.2.1)
    · rw [SemiCircuit.children_subst hux hℓu]
  deletable N _ hN := by
    rcases N with J | e
    · exact ⟨hN.1, Gate.degenerate_subst hN.2 _ _⟩
    · exact ⟨hN.1, Equation.card_subst_le.trans hN.2⟩

/-! ### Fixing a parameter to a constant -/

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

@[simp] theorem fixConst_gate (S : State n) (w : ℕ) (b : Bool) (J : ℕ) :
    (S.fixConst w b).gate J = (S.gate J).subst w (Lit.const b) := rfl

theorem fixConst_m {S : State n} {w : ℕ} (hw : w ∈ S.params) (b : Bool) :
    (S.fixConst w b).m + 1 = S.m := by
  simp only [m, fixConst_params]
  exact Finset.card_erase_add_one hw

theorem fixConst_children (S : State n) {w : ℕ} (b : Bool) {z : ℕ} (hz : z ≠ w) :
    (S.fixConst w b).children z = S.children z :=
  SemiCircuit.children_subst hz (by simp [Lit.const])

/-- Fixing a parameter to a constant is a reduction. -/
theorem Valid.reduction_fixConst {S : State n} (hS : S.Valid f) {w : ℕ} (hw : w ∈ S.params)
    (b : Bool) : Reduction f S (S.fixConst w b) {w} [] [] :=
  hS.reduction_restrict hw fun y hy => by simp [Lit.Reads, Lit.const] at hy

/-! ### Deletions -/

/-- Deleting a gate is a reduction; it may reroute only to the parameter read by the literal. -/
theorem Valid.reduction_deleteGate {S : State n} (hS : S.Valid f) {J : ℕ} {ℓ : Lit}
    (h : S.DeleteGateOK J ℓ) {T : List (ℕ ⊕ ℕ)} (hT : ∀ t, ℓ.Reads t → .inl J ∈ T) :
    Reduction f S (S.deleteGate J ℓ) ∅ [.inl J] T where
  valid := hS.deleteGate h
  subset := Finset.empty_subset _
  params := (Finset.sdiff_empty).symm
  pairs := (Finset.filter_true_of_mem fun _ _ => by simp).symm
  size := deleteGate_size h
  children u hu := by
    by_cases hℓu : ℓ.Reads u
    · exact Or.inr ⟨_, hT u hℓu, (SemiCircuit.inl_mem_children _).2 ⟨h.mem, h.reads u hℓu⟩⟩
    · refine Or.inl ?_
      rw [List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
        Finset.sdiff_singleton_eq_erase]
      exact deleteGate_children_of_ne hS h hu hℓu
  deletable N hN hdel := by
    rcases N with K | e
    · have hKJ : K ≠ J := fun he => hN (by rw [he]; exact List.mem_singleton_self _)
      exact ⟨Finset.mem_erase.2 ⟨hKJ, hdel.1⟩, Gate.degenerate_subst hdel.2 _ _⟩
    · exact ⟨hdel.1, Equation.card_subst_le.trans hdel.2⟩

/-- Deleting a gate that is constant on the solutions of the affine system is a reduction
rerouting nothing. -/
theorem Valid.reduction_deleteConst {S : State n} (hS : S.Valid f) {J : ℕ} {c : Bool}
    (hJ : J ∈ S.gates) (hc : ∀ val, S.EqnsHold val → (S.gate J).eval val = c) :
    Reduction f S (S.deleteGate J (Lit.const c)) ∅ [.inl J] [] :=
  hS.reduction_deleteGate ⟨hJ, fun t ht => by simp [Lit.Reads, Lit.const] at ht,
    Or.inl fun val hval => by rw [hc val hval, Lit.eval_const]⟩
    fun t ht => by simp [Lit.Reads, Lit.const] at ht

/-- Deleting an equation `v = ℓ` is a reduction; it may reroute only to the parameter read by
the literal. -/
theorem Valid.reduction_deleteEqn {S : State n} (hS : S.Valid f) {e v : ℕ} {ℓ : Lit}
    (h : S.DeleteEqnOK e v ℓ) {T : List (ℕ ⊕ ℕ)} (hT : ∀ t, ℓ.Reads t → .inr e ∈ T) :
    Reduction f S (S.deleteEqn e v ℓ) ∅ [.inr e] T where
  valid := hS.deleteEqn h
  subset := Finset.empty_subset _
  params := (Finset.sdiff_empty).symm
  pairs := (Finset.filter_true_of_mem fun _ _ => by simp).symm
  size := deleteEqn_size h
  children u hu := by
    by_cases hℓu : ℓ.Reads u
    · exact Or.inr ⟨_, hT u hℓu, (SemiCircuit.inr_mem_children _).2
        ⟨h.mem, (h.reads u hℓu).1⟩⟩
    · refine Or.inl ?_
      rw [List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
        Finset.sdiff_singleton_eq_erase]
      exact deleteEqn_children_of_ne hS h hu hℓu
  deletable N hN hdel := by
    rcases N with K | e'
    · exact ⟨hdel.1, Gate.degenerate_subst hdel.2 _ _⟩
    · have hee : e' ≠ e := fun he => hN (by rw [he]; exact List.mem_singleton_self _)
      exact ⟨Finset.mem_erase.2 ⟨hee, hdel.1⟩, Equation.card_subst_le.trans hdel.2⟩

/-- Deleting an equation without terms is a reduction rerouting nothing. -/
theorem Valid.reduction_dropTrivialEqn {S : State n} (hS : S.Valid f) {e : ℕ} (he : e ∈ S.eqns)
    (hterms : (S.eqn e).terms = ∅) : Reduction f S (S.dropTrivialEqn e) ∅ [.inr e] [] where
  valid := hS.dropTrivialEqn he hterms
  subset := Finset.empty_subset _
  params := (Finset.sdiff_empty).symm
  pairs := (Finset.filter_true_of_mem fun _ _ => by simp).symm
  size := dropTrivialEqn_size he
  children u _ := Or.inl (by
    rw [dropTrivialEqn_children, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.sdiff_singleton_eq_erase])
  deletable N hN hdel := by
    rcases N with K | e'
    · exact hdel
    · have hee : e' ≠ e := fun h => hN (by rw [h]; exact List.mem_singleton_self _)
      exact ⟨Finset.mem_erase.2 ⟨hee, hdel.1⟩, hdel.2⟩

/-- A deletable constraint of a valid state is deleted by a reduction. -/
theorem Valid.exists_reduction_delete {S : State n} (hS : S.Valid f) {N : ℕ ⊕ ℕ}
    (hN : S.Deletable N) : ∃ S', Reduction f S S' ∅ [N] [N] := by
  rcases N with J | e
  · obtain ⟨hJ, hdeg⟩ := hN
    exact ⟨_, hS.reduction_deleteGate (ℓ := (S.gate J).lit)
      ⟨hJ, fun t ht => Gate.reads_of_lit_reads ht, Or.inl fun val _ => Gate.eval_lit hdeg val⟩
      fun _ _ => List.mem_singleton_self _⟩
  · obtain ⟨he, hcard⟩ := hN
    by_cases haux : ∃ v ∈ (S.eqn e).terms, v ∈ S.aux
    · obtain ⟨v, hv, hva⟩ := haux
      have hrest : ((S.eqn e).terms.erase v).card ≤ 1 := by
        rw [Finset.card_erase_of_mem hv]; omega
      rcases Finset.card_le_one_iff_subset_singleton.1 hrest with ⟨U, hU⟩
      by_cases hUmem : U ∈ (S.eqn e).terms.erase v
      · -- the equation reads `v + U = rhs`
        have hterms : (S.eqn e).terms = {v, U} := by
          ext i
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro hi
            by_cases hiv : i = v
            · exact Or.inl hiv
            · exact Or.inr (Finset.mem_singleton.1 (hU (Finset.mem_erase.2 ⟨hiv, hi⟩)))
          · rintro (rfl | rfl)
            · exact hv
            · exact Finset.mem_of_mem_erase hUmem
        have hUv : U ≠ v := Finset.ne_of_mem_erase hUmem
        refine ⟨_, hS.reduction_deleteEqn (v := v) (ℓ := ⟨.node U, (S.eqn e).rhs⟩)
          ⟨he, hva, fun val => ?_, fun t ht => ?_⟩ fun _ _ => List.mem_singleton_self _⟩
        · unfold Equation.Holds
          rw [hterms, Finset.sum_pair hUv.symm]
          simp only [Lit.eval, Arg.eval_node]
          generalize val v = a; generalize val U = b; generalize (S.eqn e).rhs = r
          revert a b r; decide
        · cases ht
          exact ⟨Finset.mem_of_mem_erase hUmem, hUv⟩
      · -- the equation reads `v = rhs`
        have hterms : (S.eqn e).terms = {v} := by
          ext i
          simp only [Finset.mem_singleton]
          constructor
          · intro hi
            by_contra hiv
            have := hU (Finset.mem_erase.2 ⟨hiv, hi⟩)
            rw [Finset.mem_singleton] at this
            exact hUmem (this ▸ Finset.mem_erase.2 ⟨hiv, hi⟩)
          · rintro rfl; exact hv
        refine ⟨_, hS.reduction_deleteEqn (v := v) (ℓ := Lit.const (S.eqn e).rhs)
          ⟨he, hva, fun val => ?_, fun t ht => by cases ht⟩ fun _ ht => by cases ht⟩
        unfold Equation.Holds
        rw [hterms, Finset.sum_singleton, Lit.eval_const]
    · push Not at haux
      have hsub : (S.eqn e).terms ⊆ S.params := fun i hi => by
        rcases Finset.mem_union.1 (hS.wf.terms_subset e he hi) with hp | ha
        · exact hp
        · exact absurd ha (haux i hi)
      exact ⟨_, (hS.reduction_dropTrivialEqn he (hS.terms_eq_empty_of_subset he hsub)).mono
        fun _ hN => absurd hN List.not_mem_nil⟩

/-- Distinct deletable constraints of a valid state are deleted by a reduction. -/
theorem Valid.exists_reduction_deleteAll {S : State n} (hS : S.Valid f) (l : List (ℕ ⊕ ℕ))
    (hl : l.Nodup) (hdel : ∀ N ∈ l, S.Deletable N) : ∃ S', Reduction f S S' ∅ l l := by
  induction l generalizing S with
  | nil => exact ⟨S, Reduction.refl hS⟩
  | cons N l ih =>
    obtain ⟨S₁, h₁⟩ := hS.exists_reduction_delete (hdel N List.mem_cons_self)
    have hl' := List.nodup_cons.1 hl
    obtain ⟨S', h₂⟩ := ih h₁.valid hl'.2 fun N' hN' => h₁.deletable N'
      (by rw [List.mem_singleton]; rintro rfl; exact hl'.1 hN')
      (hdel N' (List.mem_cons_of_mem _ hN'))
    have h := h₁.trans h₂
    rw [Finset.empty_union] at h
    exact ⟨S', h⟩

end State

end Cslib.Circuits.Boolean.B2
