/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.B2.Eliminate

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
  obtain ⟨hS', hlt, hW'⟩ := h
  exact ⟨hS', by omega, by rw [← ha]; omega⟩

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
  by_cases h2 : S.Case2
  · exact hS.step_case2 h2
  have hexcl := exclusive_of hS hmov hdel h2
  by_cases h3 : S.Case3
  · exact hS.step_case3 hexcl h3
  by_cases h4 : S.Case4
  · exact hS.step_case4 hdel h3 h4
  by_cases h5 : S.Case5
  · exact hS.step_case5 hf ha hexcl h3 h4 h5
  by_cases h6 : S.Case6
  · exact hS.step_case6 hexcl h2 h3 h4 h5 h6
  -- the minimal AND
  sorry

/-- **Lemma 4.2** of [Mishra and Santhanam][MishraSanthanam2026]: if `d < a`, a valid state for
an affine disperser for dimension `d` has a step of gate elimination: a valid state with smaller
`m + s` and `ΔW ≤ 14 Δa`. -/
theorem Valid.exists_step {d : ℕ} {S : State n} (hS : S.Valid f) (hf : IsAffineDisperser f d)
    (ha : d < S.a) : ∃ S' : State n, S'.Valid f ∧ S'.m + S'.s < S.m + S.s ∧
      S'.W + 14 * S.a ≤ S.W + 14 * S'.a :=
  Valid.exists_step_aux hf _ _ _ S rfl rfl rfl hS ha

end State

end Cslib.Circuits.Boolean.B2
