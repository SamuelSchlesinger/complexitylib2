/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.B2.Case7
public import Complexity.Computability.Circuit.Boolean.B2.Case8
public import Complexity.Computability.Circuit.Boolean.B2.Bottleneck

/-!
# Lemma 4.2: one step of gate elimination

**Lemma 4.2** of [Mishra and Santhanam][MishraSanthanam2026]: if `a > d`, a valid state for an
affine disperser for dimension `d` has a step of gate elimination (`State.Valid.exists_step`):
a valid state with smaller `m + s` and `ΔW ≤ 14 Δa`.

The proof follows Section 4 of the source. Movable affine gates are moved into the affine system
first; then the first applicable preliminary reduction (Cases 1 to 6) is a step. Otherwise the
minimal gate is an AND-type gate on two distinct inputs among the parameters and auxiliary
variables (`State.Valid.clean_minGate`); an auxiliary input is exchanged with a parameter, and a
child of the minimal AND reading one of its inputs is rerouted, and the analysis restarts; once
neither applies, Cases 7 to 10 eliminate the minimal AND. The preparatory operations keep `m`,
`s` and `a` and do not increase `W`, and terminate since each lowers, lexicographically, the
number of gates (`State.auxIn`, `State.childIn`). The existence proof is not an algorithm and no
running time is claimed.

## Main definitions

* `Cslib.Circuits.Boolean.B2.State.auxIn`, `Cslib.Circuits.Boolean.B2.State.childIn`: the
  measures of the restructuring.

## Main results

* `Cslib.Circuits.Boolean.B2.State.Valid.exists_step`: Lemma 4.2.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.B2

open Finset Cslib.BitString

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Composing preparatory operations with steps -/

theorem Step.of_prep {S S₁ S' : State n} (h : Step f S₁ S') (hms : S₁.m + S₁.s = S.m + S.s)
    (ha : S₁.a = S.a) (hW : S₁.W ≤ S.W) : Step f S S' := by
  obtain ⟨hS', hlt, ha₁, ha₂, hW'⟩ := h
  exact ⟨hS', by omega, by omega, by omega, by rw [← ha]; omega⟩

/-! ### Degenerate minimal gates allow deletions -/

theorem deletionAvailable_of_degenerate {S : State n} {J : ℕ} (hJ : J ∈ S.gates)
    (h : (S.gate J).Degenerate) : S.DeletionAvailable :=
  Or.inr (Or.inl ⟨J, hJ, (S.gate J).lit, fun _ ht => Gate.reads_of_lit_reads ht,
    fun val _ => Gate.eval_lit h val⟩)

/-- A gate one of whose inputs is constant on the solutions of the affine system allows (D1). -/
theorem deletionAvailable_of_const_input {S : State n} {J t : ℕ} (hJ : J ∈ S.gates) {c : Bool}
    (ht : (S.gate J).Reads t) (hc : ∀ val, S.EqnsHold val → val t = c) : S.DeletionAvailable := by
  refine Or.inr (Or.inl ⟨J, hJ, ?_⟩)
  rcases ht with ht | ht
  · refine ⟨unaryLit ((S.gate J).op c) (S.gate J).right,
      fun s hs => Or.inr (reads_of_unaryLit_reads hs), fun val hval => ?_⟩
    rw [← eval_unaryLit]
    unfold Gate.eval
    rw [ht, Arg.eval_node, hc val hval]
  · refine ⟨unaryLit (fun a => (S.gate J).op a c) (S.gate J).left,
      fun s hs => Or.inl (reads_of_unaryLit_reads hs), fun val hval => ?_⟩
    rw [← eval_unaryLit]
    unfold Gate.eval
    rw [ht, Arg.eval_node, hc val hval]

/-- A gate whose inputs differ by a constant on the solutions of the affine system allows
(D1). -/
theorem deletionAvailable_of_dependent {S : State n} {J t t' : ℕ} (hJ : J ∈ S.gates) {c : Bool}
    (hargs : ((S.gate J).left = .node t ∧ (S.gate J).right = .node t') ∨
      ((S.gate J).left = .node t' ∧ (S.gate J).right = .node t))
    (hc : ∀ val, S.EqnsHold val → val t' = (val t ^^ c)) : S.DeletionAvailable := by
  refine Or.inr (Or.inl ⟨J, hJ, ?_⟩)
  rcases hargs with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · refine ⟨unaryLit (fun a => (S.gate J).op a (a ^^ c)) (S.gate J).left,
      fun s hs => Or.inl (reads_of_unaryLit_reads hs), fun val hval => ?_⟩
    rw [← eval_unaryLit]
    unfold Gate.eval
    rw [hl, hr, Arg.eval_node, Arg.eval_node, hc val hval]
  · refine ⟨unaryLit (fun a => (S.gate J).op (a ^^ c) a) (S.gate J).right,
      fun s hs => Or.inr (reads_of_unaryLit_reads hs), fun val hval => ?_⟩
    rw [← eval_unaryLit]
    unfold Gate.eval
    rw [hl, hr, Arg.eval_node, Arg.eval_node, hc val hval]

/-! ### The minimal gate of a clean state -/

/-- The output of a valid state with `d < a` is not a literal of an auxiliary variable. -/
theorem Valid.not_out_reads_aux {S : State n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) {v : ℕ} (hv : v ∈ S.aux) : ¬ S.out.Reads v := by
  intro hr
  obtain ⟨c, T, hT⟩ := hS.wf.exists_affineIn hv
  refine hS.out_not_affine hf ha (c ^^ S.out.neg) hT.1 fun val hval => ?_
  unfold Lit.eval
  unfold Lit.Reads at hr
  rw [hr, Arg.eval_node, hT.2 val hval.1]
  generalize ∑ j ∈ T, val j = s
  cases c <;> cases s <;> cases S.out.neg <;> rfl

/-- In a valid state with `d < a` where no affine gate can be moved and no deletion applies,
there are gates, and the minimal one is an AND-type gate reading two distinct inputs among the
parameters and auxiliary variables. -/
theorem Valid.clean_minGate {S : State n} {d : ℕ} (hS : S.Valid f) (hf : IsAffineDisperser f d)
    (ha : d < S.a) (hmov : ∀ J, ¬ S.Movable J) (hdel : ¬ S.DeletionAvailable) :
    ∃ h : S.gates.Nonempty, ¬ IsAffineOp (S.gate (S.gates.min' h)).op ∧
      ∃ t₁ t₂, (S.gate (S.gates.min' h)).left = .node t₁ ∧
        (S.gate (S.gates.min' h)).right = .node t₂ ∧ t₁ ≠ t₂ ∧
        t₁ ∈ S.params ∪ S.aux ∧ t₂ ∈ S.params ∪ S.aux := by
  have hne : S.gates.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rcases hout : S.out.arg with b | t
    · refine hS.out_not_affine hf ha (b ^^ S.out.neg) (Finset.empty_subset _) fun val _ => ?_
      simp [Lit.eval, hout]
    · have hlive := hS.wf.out_live t hout
      simp only [SemiCircuit.live, Finset.mem_union, hempty, Finset.notMem_empty, or_false]
        at hlive
      rcases hlive with hp | hv
      · exact hS.not_out_reads_param hf ha hp hout
      · exact hS.not_out_reads_aux hf ha hv hout
  set G := S.gates.min' hne
  have hG : G ∈ S.gates := Finset.min'_mem _ _
  have hmin : ∀ i, (S.gate G).Reads i → i ∉ S.gates := fun i hi hig =>
    absurd (hS.wf.reads_lt G hG i hig hi) (not_lt.2 (Finset.min'_le _ _ hig))
  have hand : ¬ IsAffineOp (S.gate G).op := fun haff => hmov G ⟨hG, haff, hmin⟩
  have hpa : ∀ i, (S.gate G).Reads i → i ∈ S.params ∪ S.aux := fun i hi => by
    have := hS.wf.reads_live G hG i hi
    simp only [SemiCircuit.live, Finset.mem_union] at this ⊢
    rcases this with h | h
    · exact h
    · exact absurd h (hmin i hi)
  refine ⟨hne, hand, ?_⟩
  rcases hl : (S.gate G).left with b₁ | t₁
  · exact absurd (deletionAvailable_of_degenerate hG (Or.inl ⟨b₁, hl⟩)) hdel
  rcases hr : (S.gate G).right with b₂ | t₂
  · exact absurd (deletionAvailable_of_degenerate hG (Or.inr (Or.inl ⟨b₂, hr⟩))) hdel
  refine ⟨t₁, t₂, rfl, rfl, fun he => ?_, hpa t₁ (Or.inl hl), hpa t₂ (Or.inr hr)⟩
  subst he
  exact hdel (deletionAvailable_of_degenerate hG (Or.inr (Or.inr (hl.trans hr.symm))))

/-! ### The measures of the restructuring -/

/-- The number of auxiliary inputs of a gate. -/
def auxArgs (S : State n) (g : Gate) : ℕ :=
  (match g.left with | .node t => if t ∈ S.aux then 1 else 0 | .const _ => 0) +
    (match g.right with | .node t => if t ∈ S.aux then 1 else 0 | .const _ => 0)

/-- The number of auxiliary inputs of the minimal gate. -/
def auxIn (S : State n) : ℕ :=
  if h : S.gates.Nonempty then S.auxArgs (S.gate (S.gates.min' h)) else 0

/-- The number of children of the minimal gate reading one of its parameter inputs. -/
def childIn (S : State n) : ℕ :=
  if h : S.gates.Nonempty then
    (S.gates.filter fun K => (S.gate K).Reads (S.gates.min' h) ∧
      ∃ t ∈ S.params, (S.gate (S.gates.min' h)).Reads t ∧ (S.gate K).Reads t).card
  else 0

theorem auxIn_eq {S : State n} (hne : S.gates.Nonempty) :
    S.auxIn = S.auxArgs (S.gate (S.gates.min' hne)) := by
  simp only [auxIn, dite_eq_left hne]

theorem auxArgs_nodes (S : State n) {g : Gate} {t₁ t₂ : ℕ} (hl : g.left = .node t₁)
    (hr : g.right = .node t₂) :
    S.auxArgs g = (if t₁ ∈ S.aux then 1 else 0) + (if t₂ ∈ S.aux then 1 else 0) := by
  simp only [auxArgs, hl, hr]

theorem childIn_eq {S : State n} (hne : S.gates.Nonempty) :
    S.childIn = (S.gates.filter fun K => (S.gate K).Reads (S.gates.min' hne) ∧
      ∃ t ∈ S.params, (S.gate (S.gates.min' hne)).Reads t ∧ (S.gate K).Reads t).card := by
  simp only [childIn, dite_eq_left hne]

/-- An auxiliary input `Q` of the minimal gate depends on a parameter `x` other than the other
input; when no preliminary reduction applies, `x` is unpaired of degree at least two, and `Q` has
degree at least two. -/
theorem Valid.prep_aux_input {S : State n} (hS : S.Valid f) (hdel : ¬ S.DeletionAvailable)
    (h5 : ¬ S.PairInSystem) {G Q o : ℕ} (hG : G ∈ S.gates)
    (hargs : ((S.gate G).left = .node Q ∧ (S.gate G).right = .node o) ∨
      ((S.gate G).left = .node o ∧ (S.gate G).right = .node Q))
    (hQ : Q ∈ S.aux) (hQo : Q ≠ o) :
    ∃ x c T, S.AffineIn Q c T ∧ x ∈ T ∧ x ≠ o ∧ x ∈ S.unpaired ∧ 2 ≤ S.deg x ∧
      2 ≤ S.deg Q := by
  obtain ⟨c, T, hT⟩ := hS.wf.exists_affineIn hQ
  have hQp : Q ∉ S.params := fun hp => Finset.disjoint_left.1 hS.wf.disjoint_params_aux hp hQ
  have hGQ : (S.gate G).Reads Q := by
    rcases hargs with ⟨hl, -⟩ | ⟨-, hr⟩; exacts [Or.inl hl, Or.inr hr]
  by_cases hTo : ∃ x ∈ T, x ≠ o
  · obtain ⟨x, hxT, hxo⟩ := hTo
    have hxp := hT.1 hxT
    obtain ⟨e, he, hxe⟩ := hT.mem_terms hS.wf hQp hxT
    have hxu : x ∈ S.unpaired := mem_unpaired.2 ⟨hxp, fun hp => h5 ⟨x, hp, e, he, hxe⟩⟩
    have hex : Sum.inr e ∈ S.children x := (SemiCircuit.inr_mem_children _).2 ⟨he, hxe⟩
    have hxdeg : 2 ≤ S.deg x := by
      by_contra hlt
      have h1 : S.deg x = 1 := by have := Finset.card_pos.2 ⟨_, hex⟩; unfold SemiCircuit.deg at *; omega
      exact hdel (Or.inr (Or.inr (Or.inr ⟨x, hxu, e, children_eq_singleton h1 hex⟩)))
    obtain ⟨e', he', hQe'⟩ := hS.exists_eqn_of_aux hQ
    have hQdeg : 2 ≤ S.deg Q := by
      have hsub : ({Sum.inr e', Sum.inl G} : Finset (ℕ ⊕ ℕ)) ⊆ S.children Q := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact (SemiCircuit.inr_mem_children _).2 ⟨he', hQe'⟩
        · exact (SemiCircuit.inl_mem_children _).2 ⟨hG, hGQ⟩
      have := Finset.card_le_card hsub
      rwa [Finset.card_pair (by simp)] at this
    exact ⟨x, c, T, hT, hxT, hxo, hxu, hxdeg, hQdeg⟩
  · push Not at hTo
    exfalso
    rcases T.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact hdel (deletionAvailable_of_const_input hG hGQ (c := c) fun val hval => by
        rw [hT.2 val hval, Finset.sum_empty, add_zero])
    · have hxo := hTo x hx
      subst hxo
      have hTo' : T = {x} := Finset.eq_singleton_iff_unique_mem.2 ⟨hx, hTo⟩
      refine hdel (deletionAvailable_of_dependent hG (t := x) (t' := Q) (c := c) ?_ fun val hval => ?_)
      · rcases hargs with ⟨hl, hr⟩ | ⟨hl, hr⟩
        · exact Or.inr ⟨hl, hr⟩
        · exact Or.inl ⟨hl, hr⟩
      · rw [hT.2 val hval, hTo', Finset.sum_singleton]
        cases c <;> cases val x <;> rfl

/-! ### Lemma 4.2 -/

/-- Lemma 4.2, by induction on the number of gates, the number of auxiliary inputs of the minimal
gate and the number of its children reading one of its parameter inputs. -/
theorem Valid.exists_step_aux {d : ℕ} (hf : IsAffineDisperser f d) :
    ∀ k₁ k₂ k₃ (S : State n), S.gates.card = k₁ → S.auxIn = k₂ → S.childIn = k₃ →
      S.Valid f → d < S.a → ∃ S', Step f S S' := by
  intro k₁
  induction k₁ using Nat.strong_induction_on with | _ k₁ ih₁ => ?_
  intro k₂
  induction k₂ using Nat.strong_induction_on with | _ k₂ ih₂ => ?_
  intro k₃
  induction k₃ using Nat.strong_induction_on with | _ k₃ ih₃ => ?_
  intro S hk₁ hk₂ hk₃ hS ha
  -- move affine gates first
  by_cases hmov : ∃ J, S.Movable J
  · obtain ⟨J, hJ⟩ := hmov
    obtain ⟨S₁, hS₁, hcard, hm, hs, hq, hW⟩ := hS.prep_move hJ
    have ha₁ : S₁.a = S.a := by simp only [a, hm, hq]
    obtain ⟨S', hstep⟩ := ih₁ _ (hk₁ ▸ hcard) _ _ S₁ rfl rfl rfl hS₁ (ha₁ ▸ ha)
    exact ⟨S', hstep.of_prep (by omega) ha₁ hW⟩
  push Not at hmov
  -- the preliminary reductions
  by_cases hdel : S.DeletionAvailable
  · exact hS.step_of_deletion hf ha hdel
  by_cases h2 : S.AndOnIsolated
  · exact hS.step_of_andOnIsolated h2
  have hexcl := hS.exclusive hmov hdel h2
  by_cases h3 : S.DegeneratePair
  · exact hS.step_of_degeneratePair hexcl h3
  by_cases h4 : S.PartnersShareChild
  · exact hS.step_of_partnersShareChild hdel h3 h4
  by_cases h5 : S.PairInSystem
  · exact hS.step_of_pairInSystem hf ha hexcl h3 h4 h5
  by_cases h6 : S.AndOnPair
  · exact hS.step_of_andOnPair hexcl h2 h3 h4 h5 h6
  -- the minimal AND
  obtain ⟨hne, hand, t₁, t₂, hl, hr, ht12, ht₁, ht₂⟩ := hS.clean_minGate hf ha hmov hdel
  set G := S.gates.min' hne with hGdef
  have hG : G ∈ S.gates := Finset.min'_mem _ _
  -- an auxiliary input is exchanged with a parameter
  by_cases haux : t₁ ∈ S.aux ∨ t₂ ∈ S.aux
  · obtain ⟨Q, o, hargs, hQ, hQo⟩ : ∃ Q o, (((S.gate G).left = .node Q ∧
        (S.gate G).right = .node o) ∨ ((S.gate G).left = .node o ∧
        (S.gate G).right = .node Q)) ∧ Q ∈ S.aux ∧ Q ≠ o := by
      rcases haux with h | h
      · exact ⟨t₁, t₂, Or.inl ⟨hl, hr⟩, h, ht12⟩
      · exact ⟨t₂, t₁, Or.inr ⟨hl, hr⟩, h, ht12.symm⟩
    obtain ⟨x, c, T, hT, hxT, hxo, hxu, hxdeg, hQdeg⟩ :=
      hS.prep_aux_input hdel h5 hG hargs hQ hQo
    obtain ⟨hS₁, hm, hs, hq, hW⟩ := hS.prep_swap hxu hxdeg hQ hQdeg hT hxT
    set S₁ := S.swap x Q c T
    have ha₁ : S₁.a = S.a := by simp only [a, hm, hq]
    have hxp := (mem_unpaired.1 hxu).1
    have hQx : Q ≠ x := fun h => Finset.disjoint_left.1 hS.wf.disjoint_params_aux (h ▸ hxp) hQ
    have hQ₁ : Q ∉ S₁.aux := fun h => by
      change Q ∈ insert x (S.aux.erase Q) at h
      rcases Finset.mem_insert.1 h with h | h
      · exact hQx h
      · exact Finset.notMem_erase _ _ h
    have ho₁ : o ∈ S₁.aux ↔ o ∈ S.aux := by
      change o ∈ insert x (S.aux.erase Q) ↔ _
      rw [Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact absurd h.symm hxo
        · exact h
      · exact fun h => Or.inr ⟨hQo.symm, h⟩
    have hlt : S₁.auxIn < S.auxIn := by
      rw [auxIn_eq (S := S₁) hne, auxIn_eq hne]
      change S₁.auxArgs (S.gate G) < S.auxArgs (S.gate G)
      rcases hargs with ⟨hlQ, hro⟩ | ⟨hlo, hrQ⟩
      · rw [auxArgs_nodes S₁ hlQ hro, auxArgs_nodes S hlQ hro, ite_eq_right hQ₁, ite_eq_left hQ]
        by_cases hoa : o ∈ S.aux
        · rw [ite_eq_left (ho₁.2 hoa), ite_eq_left hoa]; omega
        · rw [ite_eq_right (fun h => hoa (ho₁.1 h)), ite_eq_right hoa]; omega
      · rw [auxArgs_nodes S₁ hlo hrQ, auxArgs_nodes S hlo hrQ, ite_eq_right hQ₁, ite_eq_left hQ]
        by_cases hoa : o ∈ S.aux
        · rw [ite_eq_left (ho₁.2 hoa), ite_eq_left hoa]; omega
        · rw [ite_eq_right (fun h => hoa (ho₁.1 h)), ite_eq_right hoa]; omega
    obtain ⟨S', hstep⟩ := ih₂ _ (hk₂ ▸ hlt) _ S₁ hk₁ rfl rfl hS₁ (ha₁ ▸ ha)
    exact ⟨S', hstep.of_prep (by omega) ha₁ hW⟩
  push Not at haux
  have hx : t₁ ∈ S.params := (Finset.mem_union.1 ht₁).resolve_right haux.1
  have hy : t₂ ∈ S.params := (Finset.mem_union.1 ht₂).resolve_right haux.2
  have hxu : t₁ ∈ S.unpaired :=
    mem_unpaired.2 ⟨hx, fun hp => h6 ⟨G, hG, t₁, t₂, hand, Or.inl ⟨hl, hr⟩, hp, hy, ht12⟩⟩
  have hyu : t₂ ∈ S.unpaired :=
    mem_unpaired.2 ⟨hy, fun hp => h6 ⟨G, hG, t₂, t₁, hand, Or.inr ⟨hl, hr⟩, hp, hx, ht12.symm⟩⟩
  have hGx : Sum.inl G ∈ S.children t₁ := (SemiCircuit.inl_mem_children _).2 ⟨hG, Or.inl hl⟩
  have hGy : Sum.inl G ∈ S.children t₂ := (SemiCircuit.inl_mem_children _).2 ⟨hG, Or.inr hr⟩
  have hxdeg : 2 ≤ S.deg t₁ := by
    have h1 : 1 ≤ S.deg t₁ := Finset.card_pos.2 ⟨_, hGx⟩
    by_contra hlt
    exact h2 ⟨G, hG, t₁, t₂, hand, Or.inl ⟨hl, hr⟩, hxu, by omega, hy, ht12⟩
  have hydeg : 2 ≤ S.deg t₂ := by
    have h1 : 1 ≤ S.deg t₂ := Finset.card_pos.2 ⟨_, hGy⟩
    by_contra hlt
    exact h2 ⟨G, hG, t₂, t₁, hand, Or.inr ⟨hl, hr⟩, hyu, by omega, hx, ht12.symm⟩
  have hGp : ∀ {i}, i ∈ S.params → i ≠ G := fun hi he =>
    Finset.disjoint_left.1 hS.wf.disjoint_params_gates (he ▸ hi) hG
  -- a child of the minimal AND reading one of its inputs is rerouted
  by_cases hch : ∃ K ∈ S.gates, (S.gate K).Reads G ∧ ((S.gate K).Reads t₁ ∨ (S.gate K).Reads t₂)
  · obtain ⟨K, hK, hKG, hKt⟩ := hch
    have hKne : K ≠ G := fun h => hS.not_reads_self hG (h ▸ hKG)
    let env : Bool → Bool → ℕ → Bool := fun u v i =>
      if i = G then (S.gate G).op u v else if i = t₁ then u else if i = t₂ then v else false
    let g' : Gate := ⟨fun u v => (S.gate K).eval (env u v), .node t₁, .node t₂⟩
    have hg'reads : ∀ i, g'.Reads i → i = t₁ ∨ i = t₂ := by
      rintro i (h | h)
      · exact Or.inl (Arg.node.inj h).symm
      · exact Or.inr (Arg.node.inj h).symm
    have hok : S.RewireOK K g' := by
      refine ⟨hK, fun i hi => (hg'reads i hi).elim (fun h => h ▸ hx) (fun h => h ▸ hy),
        fun val hothers => ?_⟩
      change (S.gate K).eval (env (val t₁) (val t₂)) = (S.gate K).eval val
      obtain ⟨t, ht, hKt'⟩ : ∃ t, (t = t₁ ∨ t = t₂) ∧ (S.gate K).Reads t := by
        rcases hKt with h | h
        · exact ⟨t₁, Or.inl rfl, h⟩
        · exact ⟨t₂, Or.inr rfl, h⟩
      have htG : t ≠ G := by rcases ht with rfl | rfl; exacts [hGp hx, hGp hy]
      refine Gate.eval_congr fun i hi => ?_
      rcases Gate.eq_or_eq_of_reads htG.symm hKG hKt' hi with rfl | rfl
      · simp only [env, ite_true]
        rw [hothers G hG hKne.symm]
        unfold Gate.eval
        rw [hl, hr, Arg.eval_node, Arg.eval_node]
      · rcases ht with rfl | rfl
        · simp only [env, ite_eq_right htG, ite_true]
        · simp only [env, ite_eq_right htG, ite_eq_right ht12.symm, ite_true]
    obtain ⟨hS₁, hm, hs, hq, hW⟩ := hS.prep_rewire hok fun t ht htu => by
      rcases hg'reads t ht with rfl | rfl; exacts [hxdeg, hydeg]
    set S₁ := S.rewire K g'
    have ha₁ : S₁.a = S.a := by simp only [a, hm, hq]
    have hgate : ∀ K', K' ≠ K → S₁.gate K' = S.gate K' := fun K' h => Function.update_of_ne h _ _
    have hauxeq : S₁.auxIn = S.auxIn := by
      rw [auxIn_eq (S := S₁) hne, auxIn_eq hne]
      change S₁.auxArgs (S₁.gate G) = S.auxArgs (S.gate G)
      rw [hgate G hKne.symm]
      rfl
    have hlt : S₁.childIn < S.childIn := by
      rw [childIn_eq (S := S₁) hne, childIn_eq hne]
      change (S.gates.filter fun K' => (S₁.gate K').Reads G ∧
        ∃ t ∈ S.params, (S₁.gate G).Reads t ∧ (S₁.gate K').Reads t).card <
          (S.gates.filter fun K' => (S.gate K').Reads G ∧
            ∃ t ∈ S.params, (S.gate G).Reads t ∧ (S.gate K').Reads t).card
      refine Finset.card_lt_card ⟨fun K' hK' => ?_, fun hsub => ?_⟩
      · obtain ⟨hK'g, hK'G, t, htp, hGt, hK't⟩ := Finset.mem_filter.1 hK'
        have hK'K : K' ≠ K := by
          rintro rfl
          rw [show S₁.gate K' = g' from Function.update_self _ _ _] at hK'G
          rcases hg'reads G hK'G with h | h
          · exact hGp hx h.symm
          · exact hGp hy h.symm
        rw [hgate K' hK'K] at hK'G hK't
        rw [hgate G hKne.symm] at hGt
        exact Finset.mem_filter.2 ⟨hK'g, hK'G, t, htp, hGt, hK't⟩
      · have hKmem : K ∈ S.gates.filter fun K' => (S.gate K').Reads G ∧
            ∃ t ∈ S.params, (S.gate G).Reads t ∧ (S.gate K').Reads t := by
          refine Finset.mem_filter.2 ⟨hK, hKG, ?_⟩
          rcases hKt with h | h
          · exact ⟨t₁, hx, Or.inl hl, h⟩
          · exact ⟨t₂, hy, Or.inr hr, h⟩
        obtain ⟨-, hKG', -⟩ := Finset.mem_filter.1 (hsub hKmem)
        rw [show S₁.gate K = g' from Function.update_self _ _ _] at hKG'
        rcases hg'reads G hKG' with h | h
        · exact hGp hx h.symm
        · exact hGp hy h.symm
    obtain ⟨S', hstep⟩ := ih₃ _ (hk₃ ▸ hlt) S₁ hk₁ (hauxeq.trans hk₂) rfl hS₁ (ha₁ ▸ ha)
    exact ⟨S', hstep.of_prep (by omega) ha₁ hW⟩
  push Not at hch
  -- Cases 7 to 10
  have hGout : ¬ S.out.Reads G := by
    intro hout
    obtain ⟨α, β, γ, hform⟩ := exists_and_form hand
    refine hS.false_of_fix hf ha hy β ∅ (Finset.empty_subset _) (Finset.notMem_empty _)
      (γ ^^ S.out.neg) fun val hval hfix => ?_
    rw [Finset.sum_empty, add_zero] at hfix
    unfold Lit.eval
    unfold Lit.Reads at hout
    rw [hout, Arg.eval_node, hval.2 G hG]
    unfold Gate.eval
    rw [hl, hr, Arg.eval_node, Arg.eval_node, hform, hfix]
    cases val t₁ <;> cases α <;> cases β <;> cases γ <;> cases S.out.neg <;> rfl
  have hhas : ∃ K ∈ S.gates, (S.gate K).Reads G := by
    by_contra hno
    push Not at hno
    exact hdel (Or.inr (Or.inr (Or.inl ⟨G, hG, hno, hGout⟩)))
  have hdispatch : ∀ x y, S.MinAnd G x y → ∃ S', Step f S S' := fun x y hmin => by
    by_cases h7 : S.Case7 G x y
    · exact hS.step_case7 hdel hmin h7
    · by_cases hbot : S.Bottleneck G x
      · exact hS.step_bottleneck hf ha hexcl hdel hmin h7 hbot
      · exact hS.step_case8 hexcl hdel hmin h7 hbot
  by_cases hle : S.deg t₂ ≤ S.deg t₁
  · exact hdispatch _ _ ⟨hG, hand, Or.inl ⟨hl, hr⟩, hxu, hyu, ht12, hydeg, hle,
      fun K hK hKG => ⟨(hch K hK hKG).1, (hch K hK hKG).2⟩, hGout, hhas⟩
  · exact hdispatch _ _ ⟨hG, hand, Or.inr ⟨hl, hr⟩, hyu, hxu, ht12.symm, hxdeg, by omega,
      fun K hK hKG => ⟨(hch K hK hKG).2, (hch K hK hKG).1⟩, hGout, hhas⟩

/-- **Lemma 4.2** of [Mishra and Santhanam][MishraSanthanam2026]: if `d < a`, a valid state for
an affine disperser for dimension `d` has a step of gate elimination: a valid state with smaller
`m + s` and `ΔW ≤ 14 Δa`. -/
theorem Valid.exists_step {d : ℕ} {S : State n} (hS : S.Valid f) (hf : IsAffineDisperser f d)
    (ha : d < S.a) : ∃ S' : State n, Step f S S' :=
  Valid.exists_step_aux hf _ _ _ S rfl rfl rfl hS ha

end State

end Cslib.Circuits.Boolean.B2
