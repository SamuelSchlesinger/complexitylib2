/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AffineDisperser.Normal

/-!
# Restructuring and eliminating the minimal AND

Sections 4.2 and 4.3 of [Mishra and Santhanam][MishraSanthanam2026]. In a normal state with
`d < a` (`State.Normal`), the minimal gate is an AND-type gate `G` on two distinct inputs among
the parameters and auxiliary variables (`State.Valid.exists_minGate`).

*Restructuring* (Section 4.2) uses preparatory operations (`State.Preparation`), which keep `m`,
`s` and `q` and do not increase `W`. An auxiliary input of `G` is exchanged with a parameter it
depends on by the affine reparameterisation (`State.Valid.exists_preparation_auxIn_lt`), and a
child of `G` reading an input of `G` is relabelled to read both inputs instead
(`State.Valid.exists_preparation_childIn_lt`). Afterwards `G` is a *minimal AND*
(`State.MinimalAnd`, `State.Valid.exists_minimalAnd`): it reads two unpaired parameters `x` and
`y` with `2 ≤ deg y ≤ deg x`, no child of `G` reads them, and `G` is not the output and has a
child.

*Elimination* (Section 4.3) is a step of gate elimination (`State.Valid.step_of_minimalAnd`):

* Case 7, `State.SharedSecondChild`: `deg x = deg y = 2` and `x`, `y` share their second child
  `B`; restricting to a line of `𝔽₂²` on which `G` and `B` are constant (`exists_line_const`)
  deletes both (`State.Valid.step_of_sharedSecondChild`), `ΔW ≤ -18`, `Δa = -1`;
* the bottleneck configuration, `State.Bottleneck`: `deg x = 2` and the unique child `D` of `G`
  reads an unpaired isolated parameter `z`. If `D` is AND-type, fixing `x` and `y` makes `G` and
  `D` constant (Case 9, `ΔW ≤ -28`, `Δa = -2`); otherwise `D` is XOR-type and the quadratic
  reparameterisation deletes `G` and `D` (Case 10, `State.Valid.step_quad`, `ΔW ≤ -14`,
  `Δa = -1`); both in `State.Valid.step_of_bottleneck`;
* Case 8, otherwise: fixing `x` so that `G` becomes constant deletes all children of `x` and of
  `G` (`State.Valid.step_fixInput`), `Δa = -1`; only the unpaired isolated parameters below `G`
  can gain weight, at most `deg G` of them (`State.Valid.card_isolated_le`).

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser.State.MinimalAnd`: the minimal AND.
* `Cslib.Circuits.Boolean.AffineDisperser.State.SharedSecondChild`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.Bottleneck`: the configurations of Section 4.3.
* `Cslib.Circuits.Boolean.AffineDisperser.State.auxIn`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.childIn`: the measures of the restructuring.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.exists_preparation_auxIn_lt`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.exists_preparation_childIn_lt`: the
  restructuring.
* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.step_of_minimalAnd`: eliminating the
  minimal AND.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset Cslib.BitString SemiCircuit

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Exchanging a parameter and an auxiliary variable -/

/-- An auxiliary variable of a valid state occurs in some equation: otherwise the affine system
would not determine it. -/
theorem Valid.exists_eqn_of_aux {S : State n} (hS : S.Valid f) {v : ℕ} (hv : v ∈ S.aux) :
    ∃ e ∈ S.eqns, v ∈ (S.eqn e).terms := by
  by_contra hne
  push Not at hne
  obtain ⟨val, -, heq⟩ := hS.wf.solvable 0
  have hvp : v ∉ S.params := fun hp => Finset.disjoint_left.1 hS.wf.disjoint_params_aux hp hv
  have heq' : S.EqnsHold (Function.update val v (!val v)) := fun e he =>
    (Equation.holds_congr fun i hi =>
      Function.update_of_ne (show i ≠ v from fun h => hne e he (h ▸ hi)) _ _).2 (heq e he)
  have := hS.wf.unique val _ (fun j hj => (Function.update_of_ne
    (show j ≠ v from fun h => hvp (h ▸ hj)) _ _).symm) heq heq' v hv
  rw [Function.update_self] at this
  cases h : val v <;> simp [h] at this

/-- The affine reparameterisation of an unpaired parameter `x` of degree at least two and an
auxiliary variable `Q` of degree at least two depending on it is a preparatory operation: it keeps
every child, and both weights are `7`. -/
theorem Valid.preparation_swap {S : State n} (hS : S.Valid f) {x Q : ℕ} {c : Bool}
    {T : Finset ℕ} (hx : x ∈ S.unpaired) (hxdeg : 2 ≤ S.deg x) (hQ : Q ∈ S.aux)
    (hQdeg : 2 ≤ S.deg Q) (haff : S.AffineIn Q c T) (hxT : x ∈ T) :
    Preparation f S (S.swap x Q c T) := by
  obtain ⟨hxp, hxu⟩ := mem_unpaired.1 hx
  have hok : S.SwapOK x Q c T := ⟨hxp, hxu, hQ, haff, hxT⟩
  have hQp : Q ∉ S.params := fun hp => Finset.disjoint_left.1 hS.wf.disjoint_params_aux hp hQ
  have hQx : Q ≠ x := fun h => hQp (h ▸ hxp)
  set S₁ := S.swap x Q c T
  have hm : S₁.m = S.m := by
    change (insert Q (S.params.erase x)).card = S.params.card
    rw [Finset.card_insert_of_notMem fun h => hQp (Finset.mem_of_mem_erase h),
      Finset.card_erase_add_one hxp]
  refine ⟨hS.swap hok, hm, rfl, rfl, ?_⟩
  have hN : S.params ⊆ insert Q S.params := Finset.subset_insert _ _
  have hN' : S₁.params ⊆ insert Q S.params :=
    Finset.insert_subset_insert _ (Finset.erase_subset _ _)
  have hpt : ∀ u ∈ insert Q S.params, S₁.wt u + (if u = x then 7 else 0) ≤
      S.wt u + (if u = Q then 7 else 0) := by
    intro u _
    by_cases hux : u = x
    · subst hux
      rw [wt_of_notMem_params (by simp [S₁, hQx.symm]), wt_of_mem hx, weight_of_two_le hxdeg,
        ite_eq_left rfl, ite_eq_right hQx.symm]
    · rw [ite_eq_right hux]
      by_cases huQ : u = Q
      · subst huQ
        rw [ite_eq_left rfl, wt_of_notMem_params hQp]
        have := S₁.wt_le_seven u
        omega
      · rw [ite_eq_right huQ]
        by_cases hu₁ : u ∈ S₁.unpaired
        · have hus : u ∈ S.unpaired := by
            obtain ⟨hup, hun⟩ := mem_unpaired.1 hu₁
            simp only [S₁, swap_params, Finset.mem_insert, Finset.mem_erase] at hup
            exact mem_unpaired.2 ⟨(hup.resolve_left huQ).2, hun⟩
          rw [wt_of_mem hu₁, wt_of_mem hus]
          rfl
        · rw [wt_of_notMem hu₁]; omega
  have hW := W_add_le hN hN' _ _ hpt
  rw [sum_ite_eq_of_mem (Finset.mem_insert_of_mem hxp),
    sum_ite_eq_of_mem (Finset.mem_insert_self _ _)] at hW
  have hs : S₁.s = S.s := rfl
  have hq : S₁.q = S.q := rfl
  omega

/-! ### Rewiring a gate -/

/-- Rewiring a gate to a gate reading only parameters of degree at least two is a preparatory
operation: only those parameters may gain a child, and their weight is already `7`. -/
theorem Valid.preparation_rewire {S : State n} (hS : S.Valid f) {J : ℕ} {g : Gate}
    (h : S.RewireOK J g) (hdeg : ∀ t, g.Reads t → t ∈ S.unpaired → 2 ≤ S.deg t) :
    Preparation f S (S.rewire J g) := by
  refine ⟨hS.rewire h, rfl, rfl, rfl, ?_⟩
  have hpt : ∀ u ∈ S.params, (S.rewire J g).wt u + 0 ≤ S.wt u + 0 := by
    intro u hu
    by_cases hu' : u ∈ S.unpaired
    · have hu₁ : u ∈ (S.rewire J g).unpaired := by rwa [unpaired_congr rfl rfl]
      rw [wt_of_mem hu₁, wt_of_mem hu']
      by_cases hgu : g.Reads u
      · rw [weight_of_two_le (hdeg u hgu hu')]
        have := weight_le_seven ((S.rewire J g).deg u)
        omega
      · refine Nat.add_le_add_right (weight_mono (Finset.card_le_card fun w hw => ?_)) _
        rcases w with K | e
        · rw [inl_mem_children_rewire] at hw
          obtain ⟨hK, hr⟩ := hw
          by_cases hKJ : K = J
          · rw [ite_eq_left hKJ] at hr; exact absurd hr hgu
          · rw [ite_eq_right hKJ] at hr
            exact (SemiCircuit.inl_mem_children _).2 ⟨hK, hr⟩
        · rwa [inr_mem_children_rewire] at hw
    · rw [wt_of_notMem (by rwa [unpaired_congr rfl rfl]), wt_of_notMem hu']
  have hW := W_add_le (S := S) (S' := S.rewire J g) le_rfl le_rfl _ _ hpt
  have hs : (S.rewire J g).s = S.s := rfl
  have hq : (S.rewire J g).q = S.q := rfl
  simp only [Finset.sum_const_zero] at hW
  omega

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

/-! ### The minimal gate of a normal state -/

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
theorem Valid.exists_minGate {S : State n} {d : ℕ} (hS : S.Valid f) (hf : IsAffineDisperser f d)
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

/-- An auxiliary input `Q` of the minimal gate depends on a parameter `x` other than the other
input; when no preliminary reduction applies, `x` is unpaired of degree at least two, and `Q` has
degree at least two. -/
theorem Valid.exists_param_of_aux_input {S : State n} (hS : S.Valid f) (hN : S.Normal) {G Q o : ℕ}
    (hG : G ∈ S.gates) (hargs : ((S.gate G).left = .node Q ∧ (S.gate G).right = .node o) ∨
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
    obtain ⟨e, he, hxe⟩ := hT.mem_terms hS.wf hQp hxT
    obtain ⟨hxu, hxdeg⟩ := hN.system_param x (hT.1 hxT) e he hxe
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
    · exact hN.no_deletion (deletionAvailable_of_const_input hG hGQ (c := c) fun val hval => by
        rw [hT.2 val hval, Finset.sum_empty, add_zero])
    · have hxo := hTo x hx
      subst hxo
      have hTo' : T = {x} := Finset.eq_singleton_iff_unique_mem.2 ⟨hx, hTo⟩
      refine hN.no_deletion (deletionAvailable_of_dependent hG (t := x) (t' := Q) (c := c) ?_
        fun val hval => ?_)
      · rcases hargs with ⟨hl, hr⟩ | ⟨hl, hr⟩
        · exact Or.inr ⟨hl, hr⟩
        · exact Or.inl ⟨hl, hr⟩
      · rw [hT.2 val hval, hTo', Finset.sum_singleton]
        cases c <;> cases val x <;> rfl

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

/-! ### Restructuring the minimal AND -/

/-- Exchanging an auxiliary input of the minimal gate of a normal state with a parameter it
depends on is a preparatory operation lowering the number of auxiliary inputs of the minimal
gate. -/
theorem Valid.exists_preparation_auxIn_lt {S : State n} (hS : S.Valid f) (hN : S.Normal)
    (hne : S.gates.Nonempty) {Q o : ℕ}
    (hargs : ((S.gate (S.gates.min' hne)).left = .node Q ∧
        (S.gate (S.gates.min' hne)).right = .node o) ∨
      ((S.gate (S.gates.min' hne)).left = .node o ∧ (S.gate (S.gates.min' hne)).right = .node Q))
    (hQ : Q ∈ S.aux) (hQo : Q ≠ o) :
    ∃ S₁ : State n, Preparation f S S₁ ∧ S₁.gates = S.gates ∧ S₁.auxIn < S.auxIn := by
  set G := S.gates.min' hne
  obtain ⟨x, c, T, hT, hxT, hxo, hxu, hxdeg, hQdeg⟩ :=
    hS.exists_param_of_aux_input hN (Finset.min'_mem _ _) hargs hQ hQo
  refine ⟨S.swap x Q c T, hS.preparation_swap hxu hxdeg hQ hQdeg hT hxT, rfl, ?_⟩
  set S₁ := S.swap x Q c T
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

/-- Rerouting a child `K` of the minimal gate that reads one of its parameter inputs, by
relabelling `K` with the operation it computes on the two inputs, is a preparatory operation
lowering the number of such children. -/
theorem Valid.exists_preparation_childIn_lt {S : State n} (hS : S.Valid f)
    (hne : S.gates.Nonempty) {t₁ t₂ : ℕ} (hl : (S.gate (S.gates.min' hne)).left = .node t₁)
    (hr : (S.gate (S.gates.min' hne)).right = .node t₂) (ht12 : t₁ ≠ t₂) (hx : t₁ ∈ S.params)
    (hy : t₂ ∈ S.params) (hxdeg : 2 ≤ S.deg t₁) (hydeg : 2 ≤ S.deg t₂) {K : ℕ}
    (hK : K ∈ S.gates) (hKG : (S.gate K).Reads (S.gates.min' hne))
    (hKt : (S.gate K).Reads t₁ ∨ (S.gate K).Reads t₂) :
    ∃ S₁ : State n, Preparation f S S₁ ∧ S₁.gates = S.gates ∧ S₁.auxIn = S.auxIn ∧
      S₁.childIn < S.childIn := by
  set G := S.gates.min' hne
  have hG : G ∈ S.gates := Finset.min'_mem _ _
  have hGp : ∀ {i}, i ∈ S.params → i ≠ G := fun hi he =>
    Finset.disjoint_left.1 hS.wf.disjoint_params_gates (he ▸ hi) hG
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
      rw [hothers G hG hKne.symm, Gate.eval_of_args hl hr]
    · rcases ht with rfl | rfl
      · simp only [env, ite_eq_right htG, ite_true]
      · simp only [env, ite_eq_right htG, ite_eq_right ht12.symm, ite_true]
  refine ⟨S.rewire K g', hS.preparation_rewire hok fun t ht _ => by
    rcases hg'reads t ht with rfl | rfl; exacts [hxdeg, hydeg], rfl, ?_, ?_⟩
  · rw [auxIn_eq (S := S.rewire K g') hne, auxIn_eq hne]
    change (S.rewire K g').auxArgs ((S.rewire K g').gate G) = S.auxArgs (S.gate G)
    rw [show (S.rewire K g').gate G = S.gate G from Function.update_of_ne hKne.symm _ _]
    rfl
  · have hgate : ∀ K', K' ≠ K → (S.rewire K g').gate K' = S.gate K' := fun K' h =>
      Function.update_of_ne h _ _
    have hgateK : (S.rewire K g').gate K = g' := Function.update_self _ _ _
    have hnot : ¬ g'.Reads G := fun hG' => by
      rcases hg'reads G hG' with h | h
      · exact hGp hx h.symm
      · exact hGp hy h.symm
    rw [childIn_eq (S := S.rewire K g') hne, childIn_eq hne]
    change (S.gates.filter fun K' => ((S.rewire K g').gate K').Reads G ∧
      ∃ t ∈ S.params, ((S.rewire K g').gate G).Reads t ∧ ((S.rewire K g').gate K').Reads t).card <
        (S.gates.filter fun K' => (S.gate K').Reads G ∧
          ∃ t ∈ S.params, (S.gate G).Reads t ∧ (S.gate K').Reads t).card
    refine Finset.card_lt_card ⟨fun K' hK' => ?_, fun hsub => ?_⟩
    · obtain ⟨hK'g, hK'G, t, htp, hGt, hK't⟩ := Finset.mem_filter.1 hK'
      have hK'K : K' ≠ K := by
        rintro rfl
        rw [hgateK] at hK'G
        exact hnot hK'G
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
      rw [hgateK] at hKG'
      exact hnot hKG'

/-! ### Eliminating the minimal AND -/

/-- The configuration of Section 4.3: `G` is an AND-type gate reading the distinct unpaired
parameters `x` and `y` with `2 ≤ deg y ≤ deg x`, no child of `G` reads `x` or `y`, and `G` is not
the output and has a child. -/
structure MinimalAnd (S : State n) (G x y : ℕ) : Prop where
  /-- `G` is a gate. -/
  mem : G ∈ S.gates
  /-- `G` is AND-type. -/
  and_op : ¬ IsAffineOp (S.gate G).op
  /-- `G` reads `x` and `y`. -/
  args : ((S.gate G).left = .node x ∧ (S.gate G).right = .node y) ∨
    ((S.gate G).left = .node y ∧ (S.gate G).right = .node x)
  /-- `x` is unpaired. -/
  unpaired_x : x ∈ S.unpaired
  /-- `y` is unpaired. -/
  unpaired_y : y ∈ S.unpaired
  /-- `x` and `y` are distinct. -/
  ne : x ≠ y
  /-- `y` has degree at least two. -/
  deg_y : 2 ≤ S.deg y
  /-- `x` has degree at least that of `y`. -/
  deg_le : S.deg y ≤ S.deg x
  /-- No child of `G` reads `x` or `y`. -/
  children : ∀ K ∈ S.gates, (S.gate K).Reads G → ¬ (S.gate K).Reads x ∧ ¬ (S.gate K).Reads y
  /-- `G` is not the output. -/
  not_out : ¬ S.out.Reads G
  /-- `G` has a child. -/
  has_child : ∃ K ∈ S.gates, (S.gate K).Reads G

namespace MinimalAnd

variable {S : State n} {G x y : ℕ}

theorem mem_params_x (h : S.MinimalAnd G x y) : x ∈ S.params := (mem_unpaired.1 h.unpaired_x).1

theorem mem_params_y (h : S.MinimalAnd G x y) : y ∈ S.params := (mem_unpaired.1 h.unpaired_y).1

theorem mem_children_x (h : S.MinimalAnd G x y) : Sum.inl G ∈ S.children x := by
  refine (SemiCircuit.inl_mem_children _).2 ⟨h.mem, ?_⟩
  rcases h.args with ⟨hl, -⟩ | ⟨-, hr⟩; exacts [Or.inl hl, Or.inr hr]

theorem mem_children_y (h : S.MinimalAnd G x y) : Sum.inl G ∈ S.children y := by
  refine (SemiCircuit.inl_mem_children _).2 ⟨h.mem, ?_⟩
  rcases h.args with ⟨-, hr⟩ | ⟨hl, -⟩; exacts [Or.inr hr, Or.inl hl]

/-- The minimal AND computes an AND-type operation of its inputs. -/
theorem exists_op (h : S.MinimalAnd G x y) : ∃ φ : Bool → Bool → Bool, ¬ IsAffineOp φ ∧
    ∀ val : ℕ → Bool, (S.gate G).eval val = φ (val x) (val y) := by
  obtain ⟨φ, hφ, hG⟩ := Gate.exists_op_of_args h.args
  exact ⟨φ, fun h' => h.and_op (hφ.1 h'), hG⟩

theorem ne_gate (hS : S.Valid f) (h : S.MinimalAnd G x y) {u : ℕ} (hu : u ∈ S.params) : u ≠ G :=
  fun he => Finset.disjoint_left.1 hS.wf.disjoint_params_gates hu (he ▸ h.mem)

/-- The children of `G` are gates. -/
theorem eq_inl_of_mem_children (hS : S.Valid f) (h : S.MinimalAnd G x y) {N : ℕ ⊕ ℕ}
    (hN : N ∈ S.children G) : ∃ K ∈ S.gates, N = .inl K ∧ (S.gate K).Reads G := by
  rcases N with K | e
  · obtain ⟨hK, hKG⟩ := (SemiCircuit.inl_mem_children _).1 hN
    exact ⟨K, hK, rfl, hKG⟩
  · obtain ⟨he, hGe⟩ := (SemiCircuit.inr_mem_children _).1 hN
    exact absurd hGe (notMem_terms_of_mem_gates hS h.mem he)

end MinimalAnd

/-- In a normal state with `d < a`, an AND-type gate `G` reading two parameters, no child of which
reads them, is a minimal AND in the sense of Section 4.3, its inputs ordered by degree: by
Lemma 2.3, `G` is not the output, and it has a child since no deletion applies. -/
theorem Valid.exists_minimalAnd {S : State n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) (hN : S.Normal) {G t₁ t₂ : ℕ} (hG : G ∈ S.gates)
    (hand : ¬ IsAffineOp (S.gate G).op) (hl : (S.gate G).left = .node t₁)
    (hr : (S.gate G).right = .node t₂) (ht12 : t₁ ≠ t₂) (hx : t₁ ∈ S.params) (hy : t₂ ∈ S.params)
    (hch : ∀ K ∈ S.gates, (S.gate K).Reads G → ¬ (S.gate K).Reads t₁ ∧ ¬ (S.gate K).Reads t₂) :
    ∃ x y, S.MinimalAnd G x y := by
  obtain ⟨hxu, hxdeg⟩ := hN.and_param G hG hand t₁ t₂ (Or.inl ⟨hl, hr⟩) hx hy ht12
  obtain ⟨hyu, hydeg⟩ := hN.and_param G hG hand t₂ t₁ (Or.inr ⟨hl, hr⟩) hy hx ht12.symm
  have hGout : ¬ S.out.Reads G := by
    intro hout
    obtain ⟨α, β, γ, hform⟩ := exists_and_form hand
    refine hS.false_of_fix hf ha hy β ∅ (Finset.empty_subset _) (Finset.notMem_empty _)
      (γ ^^ S.out.neg) fun val hval hfix => ?_
    rw [Finset.sum_empty, add_zero] at hfix
    unfold Lit.eval
    unfold Lit.Reads at hout
    rw [hout, Arg.eval_node, hval.2 G hG, Gate.eval_of_args hl hr, hform, hfix]
    cases val t₁ <;> cases α <;> cases β <;> cases γ <;> cases S.out.neg <;> rfl
  have hhas : ∃ K ∈ S.gates, (S.gate K).Reads G := by
    by_contra hno
    push Not at hno
    exact hN.no_deletion (Or.inr (Or.inr (Or.inl ⟨G, hG, hno, hGout⟩)))
  by_cases hle : S.deg t₂ ≤ S.deg t₁
  · exact ⟨t₁, t₂, hG, hand, Or.inl ⟨hl, hr⟩, hxu, hyu, ht12, hydeg, hle, hch, hGout, hhas⟩
  · exact ⟨t₂, t₁, hG, hand, Or.inr ⟨hl, hr⟩, hyu, hxu, ht12.symm, hxdeg, by omega,
      fun K hK hKG => (hch K hK hKG).symm, hGout, hhas⟩

/-! ### Case 7: a shared second child -/

/-- The configuration of Case 7 of [Mishra and Santhanam][MishraSanthanam2026]: `deg x = 2` and
the inputs of the minimal AND share their second child `B`. -/
def SharedSecondChild (S : State n) (G x y : ℕ) : Prop :=
  S.deg x = 2 ∧ ∃ B, B ≠ .inl G ∧ B ∈ S.children x ∧ B ∈ S.children y

/-- Restricting one input `x'` of the minimal AND and deleting its two children `G` and `B`,
which are also the children of the other input `y'`, is a step: `Δa = -1`, `ΔW ≤ -18`. -/
theorem Reduction.step_of_shared {S S' : State n} (hS : S.Valid f) {G x' y' : ℕ}
    {B : ℕ ⊕ ℕ} (hx' : x' ∈ S.unpaired) (hy' : y' ∈ S.unpaired) (hxy : x' ≠ y')
    (hx'2 : S.deg x' = 2) (hy'2 : S.deg y' = 2) (hcy : S.children y' = {.inl G, B})
    (h : Reduction f S S' {x'} [.inl G, B] []) : Step f S S' := by
  have hx'p : ¬ S.Paired x' := (mem_unpaired.1 hx').2
  refine h.step hS (by simp) (by simp) ?_
  have hW := h.W_le (fun u => if u = y' then 7 else 0) (fun _ => 0) fun u hu => by
    by_cases huy : u = y'
    · subst huy
      rw [h.wt_eq_zero_of_subset (by simp [hcy]) (by simp), wt_of_mem hy', ite_eq_left rfl,
        weight_of_two_le hy'2.ge]
    · rw [ite_eq_right huy]
      refine Nat.add_le_add_right (h.wt_le hS (fun z hz hzu => ?_) (by simp)) 0
      rw [Finset.mem_singleton] at hz
      exact hx'p (hz ▸ hzu.paired)
  have hy'm : y' ∈ S.params \ {x'} :=
    Finset.mem_sdiff.2 ⟨(mem_unpaired.1 hy').1, by simpa using hxy.symm⟩
  rw [Finset.sum_ite_eq' _ y', ite_eq_left hy'm, Finset.sum_singleton, wt_of_mem hx',
    weight_of_two_le hx'2.ge, hS.card_pairsMeeting_singleton, ite_eq_right hx'p] at hW
  simp only [Finset.sum_const_zero, List.length_cons, List.length_nil] at hW
  rw [Finset.card_singleton, hS.card_pairsMeeting_singleton, ite_eq_right hx'p]
  omega

/-- **Case 7** of [Mishra and Santhanam, Section 4.3][MishraSanthanam2026]: if both inputs `x`,
`y` of the minimal AND have degree two and share their second child `B`, restrict to a line of
`𝔽₂²` on which both `G` and `B` are constant (`exists_line_const`) and delete both; the other
input becomes unused: `Δa = -1`, `ΔW ≤ -18`. -/
theorem Valid.step_of_sharedSecondChild {S : State n} (hS : S.Valid f) (hN : S.Normal)
    {G x y : ℕ} (h : S.MinimalAnd G x y) (h7 : S.SharedSecondChild G x y) :
    ∃ S', Step f S S' := by
  obtain ⟨hx2, B, hBG, hBx, hBy⟩ := h7
  have hy2 : S.deg y = 2 := le_antisymm (hx2 ▸ h.deg_le) h.deg_y
  have hpair : ({.inl G, B} : Finset (ℕ ⊕ ℕ)).card = 2 := Finset.card_pair hBG.symm
  have hcx : S.children x = {.inl G, B} := (Finset.eq_of_subset_of_card_le
    (by simp [Finset.insert_subset_iff, h.mem_children_x, hBx])
    (by rw [hpair]; exact hx2.le)).symm
  have hcy : S.children y = {.inl G, B} := (Finset.eq_of_subset_of_card_le
    (by simp [Finset.insert_subset_iff, h.mem_children_y, hBy])
    (by rw [hpair]; exact hy2.le)).symm
  obtain ⟨φ, hφ, hG⟩ := h.exists_op
  have hxG := h.ne_gate hS h.mem_params_x
  have hyG := h.ne_gate hS h.mem_params_y
  have hyx := h.ne.symm
  have hxy' : Arg.node y ≠ Arg.node x := fun he => hyx (Arg.node.inj he)
  -- restricting `x = y + c` deletes the children of `x` once they are constant
  have hline : ∀ c : Bool, Reduction f S (S.restrict x ⟨.node y, c⟩ (S.pairsAvoid x)) {x} [] [] :=
    fun c => hS.reduction_restrict h.mem_params_x fun t ht => by
      cases ht
      exact ⟨h.mem_params_y, hyx, by rw [hcx, hcy],
        fun hp => absurd hp (mem_unpaired.1 h.unpaired_x).2⟩
  suffices key : ∃ S' x' y', ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x)) ∧
      Reduction f S S' {x'} [.inl G, B] [] by
    obtain ⟨S', x', y', hxy', hred⟩ := key
    rcases hxy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨S', hred.step_of_shared hS h.unpaired_x h.unpaired_y h.ne hx2 hy2 hcy⟩
    · exact ⟨S', hred.step_of_shared hS h.unpaired_y h.unpaired_x hyx hy2 hx2 hcx⟩
  rcases B with Bg | e
  · -- `B` is a gate reading `x` and `y`
    obtain ⟨hBg, hBgx⟩ := (SemiCircuit.inl_mem_children _).1 hBx
    obtain ⟨-, hBgy⟩ := (SemiCircuit.inl_mem_children _).1 hBy
    obtain ⟨ψ, -, hB⟩ := Gate.exists_op_of_args (Gate.args_of_reads h.ne hBgx hBgy)
    have hBgG : Bg ≠ G := fun he => hBG (by rw [he])
    rcases exists_line_const (h := ψ) hφ with ⟨c, hφc, hψc⟩ | ⟨c, hφc, hψc⟩ | ⟨c, hφc, hψc⟩
    · -- the line `x = c`
      have h₁ := hS.reduction_fixConst h.mem_params_x c
      have h₂ := h₁.valid.reduction_deleteConst (J := G) (c := φ c false) h.mem fun val _ => by
        rw [fixConst_gate, Gate.eval_subst_const, hG, Function.update_self,
          Function.update_of_ne hyx]
        exact hφc _
      have h₃ := h₂.valid.reduction_deleteConst (J := Bg) (c := ψ c false)
        (Finset.mem_erase.2 ⟨hBgG, hBg⟩) fun val _ => by
          rw [deleteGate_gate, Gate.eval_subst_const, fixConst_gate, Gate.eval_subst_const, hB,
            Function.update_self, Function.update_of_ne hyx, Function.update_of_ne hyG]
          exact hψc _
      have h := (h₁.trans h₂).trans h₃
      simp only [Finset.union_empty, List.nil_append, List.singleton_append] at h
      exact ⟨_, x, y, Or.inl ⟨rfl, rfl⟩, h⟩
    · -- the line `y = c`
      have h₁ := hS.reduction_fixConst h.mem_params_y c
      have h₂ := h₁.valid.reduction_deleteConst (J := G) (c := φ false c) h.mem fun val _ => by
        rw [fixConst_gate, Gate.eval_subst_const, hG, Function.update_self,
          Function.update_of_ne h.ne]
        exact hφc _
      have h₃ := h₂.valid.reduction_deleteConst (J := Bg) (c := ψ false c)
        (Finset.mem_erase.2 ⟨hBgG, hBg⟩) fun val _ => by
          rw [deleteGate_gate, Gate.eval_subst_const, fixConst_gate, Gate.eval_subst_const, hB,
            Function.update_self, Function.update_of_ne h.ne, Function.update_of_ne hxG]
          exact hψc _
      have h := (h₁.trans h₂).trans h₃
      simp only [Finset.union_empty, List.nil_append, List.singleton_append] at h
      exact ⟨_, y, x, Or.inr ⟨rfl, rfl⟩, h⟩
    · -- the line `x = y + c`
      have h₁ := hline c
      have h₂ := h₁.valid.reduction_deleteConst (J := G) (c := φ c false) h.mem fun val _ => by
        rw [restrict_gate, Gate.eval_subst_update hxy', hG, Function.update_self,
          Function.update_of_ne hyx]
        exact hφc _
      have h₃ := h₂.valid.reduction_deleteConst (J := Bg) (c := ψ c false)
        (Finset.mem_erase.2 ⟨hBgG, hBg⟩) fun val _ => by
          rw [deleteGate_gate, Gate.eval_subst_const, restrict_gate,
            Gate.eval_subst_update hxy', hB, Function.update_self, Function.update_of_ne hyx]
          simp only [Lit.eval, Arg.eval_node, Function.update_of_ne hyG]
          exact hψc _
      have h := (h₁.trans h₂).trans h₃
      simp only [Finset.union_empty, List.nil_append, List.singleton_append] at h
      exact ⟨_, x, y, Or.inl ⟨rfl, rfl⟩, h⟩
  · -- `B` is an equation `v + x + y = rhs`, constant on the lines `x = y + c` only
    obtain ⟨he, hxe⟩ := (SemiCircuit.inr_mem_children _).1 hBx
    obtain ⟨-, hye⟩ := (SemiCircuit.inr_mem_children _).1 hBy
    obtain ⟨v, hva, hvx, hvy, hterms⟩ := hS.eq_insert_of_mem_terms hN.no_deletion he
      h.mem_params_x h.mem_params_y h.ne hxe hye
    have hvG : v ≠ G := fun he' =>
      Finset.disjoint_left.1 hS.wf.disjoint_aux_gates hva (he' ▸ h.mem)
    obtain ⟨c, hφc⟩ : ∃ c, ∀ b, φ (b ^^ c) b = φ c false := by
      rcases exists_line_const (h := fun a b => a ^^ b) hφ with ⟨c, -, hc⟩ | ⟨c, -, hc⟩ | ⟨c, hc, -⟩
      · simpa using hc true
      · simpa using hc true
      · exact ⟨c, hc⟩
    have h₁ := hline c
    have h₂ := h₁.valid.reduction_deleteConst (J := G) (c := φ c false) h.mem fun val _ => by
      rw [restrict_gate, Gate.eval_subst_update hxy', hG, Function.update_self,
        Function.update_of_ne hyx]
      exact hφc _
    have h₃ := h₂.valid.reduction_deleteEqn (e := e) (v := v) (ℓ := Lit.const ((S.eqn e).rhs ^^ c))
      (T := []) ⟨he, hva, fun val => by
        rw [deleteGate_eqn, Equation.holds_subst_update (by simp [Lit.const]), restrict_eqn,
          Equation.holds_subst_update hxy', Lit.eval_const]
        simp only [Lit.eval, Arg.eval_node]
        rw [Equation.holds_update_iff hterms hvx hvy h.ne, Function.update_of_ne hvG]
        simp [Lit.const],
        fun t ht => by simp [Lit.Reads, Lit.const] at ht⟩
      fun t ht => by simp [Lit.Reads, Lit.const] at ht
    have h := (h₁.trans h₂).trans h₃
    simp only [Finset.union_empty, List.nil_append, List.singleton_append] at h
    exact ⟨_, x, y, Or.inl ⟨rfl, rfl⟩, h⟩

/-! ### Case 8: fixing an input -/

/-- The bottleneck configuration of [Mishra and Santhanam, Section 4.3][MishraSanthanam2026]:
`deg x = 2` and the minimal AND `G` has a unique child `D`, which reads an unpaired isolated
parameter `z`. -/
def Bottleneck (S : State n) (G x : ℕ) : Prop :=
  S.deg x = 2 ∧ ∃ D z, (∀ K ∈ S.gates, (S.gate K).Reads G ↔ K = D) ∧ D ∈ S.gates ∧
    z ∈ S.unpaired ∧ S.deg z = 1 ∧ (S.gate D).Reads z

/-- At most `deg G` unpaired isolated parameters have their child among the children of the gate
`G`: a child of `G` has at most one parent other than `G`. -/
theorem Valid.card_isolated_le {S : State n} (hS : S.Valid f) {G : ℕ} (hG : G ∈ S.gates)
    (s : Finset ℕ) (hs : s ⊆ S.params) :
    (s.filter fun u => u ∈ S.unpaired ∧ S.deg u = 1 ∧ ∃ N ∈ S.children G, N ∈ S.children u).card
      ≤ S.deg G := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun u => if hu : ∃ N ∈ S.children G, N ∈ S.children u then hu.choose else .inl G)
    (fun u hu => ?_) (fun u hu u' hu' heq => ?_)
  · obtain ⟨-, -, -, hex⟩ := Finset.mem_filter.1 hu
    simp only [dite_eq_left hex]
    exact hex.choose_spec.1
  · obtain ⟨hus, -, -, hex⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hu)
    obtain ⟨hus', -, -, hex'⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hu')
    simp only [dite_eq_left hex, dite_eq_left hex'] at heq
    have h₁ := hex.choose_spec
    have h₂ := hex'.choose_spec
    rw [heq] at h₁
    generalize hex'.choose = N at h₁ h₂
    have hG' : ∀ {w}, w ∈ S.params → w ≠ G := fun hw he =>
      Finset.disjoint_left.1 hS.wf.disjoint_params_gates hw (he ▸ hG)
    rcases N with K | e
    · obtain ⟨-, hKG⟩ := (SemiCircuit.inl_mem_children _).1 h₁.1
      obtain ⟨-, hKu⟩ := (SemiCircuit.inl_mem_children _).1 h₁.2
      obtain ⟨-, hKu'⟩ := (SemiCircuit.inl_mem_children _).1 h₂.2
      rcases Gate.eq_or_eq_of_reads (hG' (hs hus)).symm hKG hKu hKu' with h' | h'
      · exact absurd h' (hG' (hs hus'))
      · exact h'.symm
    · obtain ⟨he, hGe⟩ := (SemiCircuit.inr_mem_children _).1 h₁.1
      exact absurd hGe (notMem_terms_of_mem_gates hS hG he)

/-- **Case 8** of [Mishra and Santhanam, Section 4.3][MishraSanthanam2026]: outside Case 7 and
the bottleneck configuration, fix the input `x` of the minimal AND `G` so that `G` becomes
constant and delete all children of `x` and of `G`. Only the `k₁ ≤ k = deg G` unpaired isolated
parameters below `G` may gain weight, and `y` drops to weight six when `deg x = 2`:
`Δa = -1`, `ΔW ≤ -7 - 2 (deg x + k) + k₁ - [deg x = 2] ≤ -14`. -/
theorem Valid.step_fixInput {S : State n} (hS : S.Valid f) (hN : S.Normal) {G x y : ℕ}
    (h : S.MinimalAnd G x y) (h7 : ¬ S.SharedSecondChild G x y) (hbot : ¬ S.Bottleneck G x) :
    ∃ S', Step f S S' := by
  have hxp := h.mem_params_x
  have hxu : ¬ S.Paired x := (mem_unpaired.1 h.unpaired_x).2
  have hxG := h.ne_gate hS hxp
  have hx2 : 2 ≤ S.deg x := h.deg_y.trans h.deg_le
  obtain ⟨b, c, hc⟩ := Gate.exists_const_of_not_isAffineOp h.and_op (a := y) (w := x) h.args.symm
  -- delete `G`, the other children of `x` and the children of `G`
  set Lx := (S.children x).erase (.inl G)
  set L := (Lx ∪ S.children G).toList
  have hdisj : Disjoint Lx (S.children G) := by
    rw [Finset.disjoint_left]
    intro N hNx hNG
    obtain ⟨K, hK, rfl, hKG⟩ := h.eq_inl_of_mem_children hS hNG
    exact (h.children K hK hKG).1
      ((SemiCircuit.inl_mem_children _).1 (Finset.mem_of_mem_erase hNx)).2
  have h₁ := hS.reduction_fixConst hxp b
  have h₂ := h₁.valid.reduction_deleteConst (J := G) (c := c) h.mem fun val _ => by
    rw [fixConst_gate, Gate.eval_subst_const]; exact hc _ (Function.update_self _ _ _)
  obtain ⟨S', h₃⟩ := h₂.valid.exists_reduction_deleteAll L (Finset.nodup_toList _) fun N hNL => by
    rw [Finset.mem_toList, Finset.mem_union] at hNL
    rcases hNL with hNx | hNG
    · exact h₂.deletable N (by simpa using Finset.ne_of_mem_erase hNx)
        (deletable_fixConst_child hS _ b (Finset.mem_of_mem_erase hNx))
    · obtain ⟨K, hK, rfl, hKG⟩ := h.eq_inl_of_mem_children hS hNG
      exact deletable_deleteGate_child c hK (fun he => hS.not_reads_self h.mem (he ▸ hKG))
        (by rw [fixConst_gate, Gate.reads_subst_of_ne hxG.symm (by simp [Lit.const])]; exact hKG)
  have hred := (h₁.trans h₂).trans h₃
  simp only [Finset.union_empty, List.nil_append, List.singleton_append] at hred
  have hlen : (Sum.inl G :: L).length = S.deg x + S.deg G := by
    have hdx : S.deg x = (S.children x).card := rfl
    have hdG : S.deg G = (S.children G).card := rfl
    rw [List.length_cons, Finset.length_toList, Finset.card_union_of_disjoint hdisj,
      Finset.card_erase_of_mem h.mem_children_x]
    omega
  refine ⟨S', hred.step hS (by simp) (by simp) ?_⟩
  have hW := hred.W_le (fun u => if u = y then (if S.deg x = 2 then 1 else 0) else 0)
    (fun u => if u ∈ S.unpaired ∧ S.deg u = 1 ∧ ∃ N ∈ S.children G, N ∈ S.children u then 1
      else 0) fun u hu => by
    obtain ⟨-, hux⟩ := Finset.mem_sdiff.1 hu
    rw [Finset.mem_singleton] at hux
    by_cases huy : u = y ∧ S.deg x = 2
    · -- `y` keeps only its second child
      obtain ⟨rfl, hx2'⟩ := huy
      have hy2 : S.deg u = 2 := le_antisymm (hx2' ▸ h.deg_le) h.deg_y
      rw [ite_eq_left rfl, ite_eq_left hx2', ite_eq_right fun hg => by omega]
      have hT : ∀ N ∈ L, N ∉ S.children u := by
        intro N hNL hNy
        rw [Finset.mem_toList, Finset.mem_union] at hNL
        rcases hNL with hNx | hNG
        · exact h7 ⟨hx2', N, Finset.ne_of_mem_erase hNx, Finset.mem_of_mem_erase hNx, hNy⟩
        · obtain ⟨K, hK, rfl, hKG⟩ := h.eq_inl_of_mem_children hS hNG
          exact (h.children K hK hKG).2 ((SemiCircuit.inl_mem_children _).1 hNy).2
      have hcard : (S.children u \ (Sum.inl G :: L).toFinset).card ≤ 1 := by
        have hsub : S.children u \ (Sum.inl G :: L).toFinset ⊆ (S.children u).erase (.inl G) :=
          fun N hN' => Finset.mem_erase.2 ⟨fun he => (Finset.mem_sdiff.1 hN').2 (by simp [he]),
            (Finset.mem_sdiff.1 hN').1⟩
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem h.mem_children_y] at this
        change _ ≤ S.deg u - 1 at this
        omega
      have hwt := (hred.wt_le_weight (fun N hN' => hT N (by simpa using hN'))).trans
        (weight_mono hcard)
      rw [weight_one] at hwt
      rw [wt_of_mem h.unpaired_y, weight_of_two_le hy2.ge]
      omega
    · rw [show (if u = y then (if S.deg x = 2 then 1 else 0) else 0) = 0 by
        by_cases huy' : u = y
        · rw [ite_eq_left huy', ite_eq_right fun hx2' => huy ⟨huy', hx2'⟩]
        · exact ite_eq_right huy']
      by_cases hg : u ∈ S.unpaired ∧ S.deg u = 1 ∧ ∃ N ∈ S.children G, N ∈ S.children u
      · -- an isolated parameter below `G` gains at most one
        rw [ite_eq_left hg, wt_of_mem hg.1, hg.2.1, weight_one]
        have := S'.wt_le_seven u
        omega
      · rw [ite_eq_right hg]
        by_cases hu' : u ∈ S.unpaired
        · refine Nat.add_le_add_right (hred.wt_le_wt hu' fun N hNL hNu => ?_) 0
          rw [Finset.mem_toList, Finset.mem_union] at hNL
          rcases hNL with hNx | hNG
          · exact hN.exclusive.two_le_deg hu' hNu hxp (Ne.symm hux) (Finset.mem_of_mem_erase hNx)
          · have h1 : 1 ≤ S.deg u := Finset.card_pos.2 ⟨N, hNu⟩
            by_contra hlt
            exact hg ⟨hu', by omega, N, hNG, hNu⟩
        · rw [hred.wt_eq_zero hS hu' fun w hw hwu => by
            rw [Finset.mem_singleton] at hw; subst hw; exact hxu hwu.paired]
          omega
  -- the gainers, and the bottleneck
  have hgain := hS.card_isolated_le h.mem (S.params \ {x}) Finset.sdiff_subset
  rw [Finset.card_filter] at hgain
  have hbot' : S.deg x = 2 → S.deg G = 1 → ∑ u ∈ S.params \ {x},
      (if u ∈ S.unpaired ∧ S.deg u = 1 ∧ ∃ N ∈ S.children G, N ∈ S.children u then 1 else 0)
        = 0 := by
    intro hx2' hG1
    refine Finset.sum_eq_zero fun u _ => ite_eq_right fun ⟨hu1, hu2, N, hNG, hNu⟩ =>
      hbot ⟨hx2', ?_⟩
    obtain ⟨K, hK, rfl, hKG⟩ := h.eq_inl_of_mem_children hS hNG
    have hcG : S.children G = {.inl K} := children_eq_singleton hG1 hNG
    refine ⟨K, u, fun K' hK' => ⟨fun hr => ?_, fun he => he ▸ hKG⟩, hK, hu1, hu2,
      ((SemiCircuit.inl_mem_children _).1 hNu).2⟩
    have : Sum.inl K' ∈ S.children G := (SemiCircuit.inl_mem_children _).2 ⟨hK', hr⟩
    rw [hcG, Finset.mem_singleton] at this
    exact Sum.inl.inj this
  have hk : 1 ≤ S.deg G := by
    obtain ⟨K, hK, hKG⟩ := h.has_child
    exact Finset.card_pos.2 ⟨_, (SemiCircuit.inl_mem_children _).2 ⟨hK, hKG⟩⟩
  have hym : y ∈ S.params \ {x} := Finset.mem_sdiff.2 ⟨h.mem_params_y, by simpa using h.ne.symm⟩
  rw [Finset.sum_ite_eq' _ y, ite_eq_left hym, Finset.sum_singleton, wt_of_mem h.unpaired_x,
    weight_of_two_le hx2, hS.card_pairsMeeting_singleton, ite_eq_right hxu, hlen] at hW
  rw [Finset.card_singleton, hS.card_pairsMeeting_singleton, ite_eq_right hxu]
  by_cases hx2' : S.deg x = 2
  · rw [ite_eq_left hx2'] at hW
    rcases Nat.lt_or_ge 1 (S.deg G) with hG2 | hG1
    · omega
    · have := hbot' hx2' (by omega)
      omega
  · rw [ite_eq_right hx2'] at hW
    omega

/-! ### Cases 9 and 10: the bottleneck -/

/-- The quadratic reparameterisation of the bottleneck configuration, when `x` and `y` have
degree at least two, is a step of gate elimination: `Δa = -1`, `ΔW ≤ -14`. -/
theorem Valid.step_quad {S : State n} (hS : S.Valid f) {x y z G D : ℕ} {α β γ c : Bool}
    (h : S.QuadOK x y z G D α β γ c) (hx : 2 ≤ S.deg x) (hy : 2 ≤ S.deg y) :
    Step f S (S.quad x y z G D α β γ c) := by
  set S' := S.quad x y z G D α β γ c
  have hS' := hS.quad h
  have hgp : ∀ {i}, i ∈ S.gates → i ∉ S.params := fun hg hp =>
    Finset.disjoint_left.1 hS.wf.disjoint_params_gates hp hg
  have hDp := hgp h.mem_D
  have hDz : D ≠ z := fun he => hDp (he ▸ h.mem_z)
  have hDx : D ≠ x := fun he => hDp (he ▸ h.mem_x)
  have hDy : D ≠ y := fun he => hDp (he ▸ h.mem_y)
  have hxy := h.x_ne_y
  have hxz := h.x_ne_z
  have hyz := h.y_ne_z
  have hm : S'.m = S.m := by
    change (insert D (S.params.erase z)).card = S.params.card
    rw [Finset.card_insert_of_notMem fun h' => hDp (Finset.mem_of_mem_erase h'),
      Finset.card_erase_add_one h.mem_z]
  have hq : S'.q = S.q + 1 := by
    change (insert (x, y) S.pairs).card = S.pairs.card + 1
    exact Finset.card_insert_of_notMem fun h' => h.unpaired_x ⟨_, h', Or.inl rfl⟩
  have hs : S'.s + 2 = S.s := quad_size h
  have hqm := hS'.q_le_m
  have hxu : x ∈ S.unpaired := mem_unpaired.2 ⟨h.mem_x, h.unpaired_x⟩
  have hyu : y ∈ S.unpaired := mem_unpaired.2 ⟨h.mem_y, h.unpaired_y⟩
  have hzu : z ∈ S.unpaired := mem_unpaired.2 ⟨h.mem_z, h.unpaired_z⟩
  have hpaired : ∀ {u}, u = x ∨ u = y → S'.Paired u := fun hu =>
    ⟨(x, y), Finset.mem_insert_self _ _, hu.imp Eq.symm Eq.symm⟩
  have hpt : ∀ u ∈ insert D S.params, S'.wt u + ((if u = x then 7 else 0) +
      (if u = y then 7 else 0) + (if u = z then 6 else 0)) ≤ S.wt u + (if u = D then 7 else 0) := by
    intro u _
    by_cases hux : u = x
    · subst hux
      rw [wt_of_paired (hpaired (Or.inl rfl)), wt_of_mem hxu, weight_of_two_le hx]
      simp [hxy, hxz, hDx.symm]
    by_cases huy : u = y
    · subst huy
      rw [wt_of_paired (hpaired (Or.inr rfl)), wt_of_mem hyu, weight_of_two_le hy]
      simp [hxy.symm, hyz, hDy.symm]
    by_cases huz : u = z
    · subst huz
      have hdz : S.deg u = 1 := by rw [SemiCircuit.deg, h.children_z, Finset.card_singleton]
      rw [wt_of_notMem_params (show u ∉ S'.params by simp [S', quad_params, hDz.symm]),
        wt_of_mem hzu, hdz, weight_one]
      simp [hux, huy, hDz.symm]
    rw [ite_eq_right hux, ite_eq_right huy, ite_eq_right huz]
    by_cases huD : u = D
    · subst huD
      rw [wt_of_notMem_params hDp, ite_eq_left rfl]
      have := S'.wt_le_seven u
      omega
    · rw [ite_eq_right huD]
      by_cases hu' : u ∈ S'.unpaired
      · obtain ⟨hup, hun⟩ := mem_unpaired.1 hu'
        have hup' : u ∈ S.params := by
          simp only [S', quad_params, Finset.mem_insert, Finset.mem_erase] at hup
          exact (hup.resolve_left huD).2
        have hus : u ∈ S.unpaired := mem_unpaired.2 ⟨hup', fun ⟨pr, hpr, hu⟩ =>
          hun ⟨pr, Finset.mem_insert_of_mem hpr, hu⟩⟩
        rw [wt_of_mem hu', wt_of_mem hus]
        exact Nat.add_le_add_right (weight_mono (Finset.card_le_card
          ((quad_children_subset S x y z G D α β γ c u).trans
            ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))))) _
      · rw [wt_of_notMem hu']
        omega
  have hW := W_add_le (S := S) (S' := S') (N := insert D S.params) (Finset.subset_insert _ _)
    (Finset.insert_subset_insert _ (Finset.erase_subset _ _)) _ _ hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' _ x, Finset.sum_ite_eq' _ y, Finset.sum_ite_eq' _ z, Finset.sum_ite_eq' _ D,
    ite_eq_left (Finset.mem_insert_of_mem h.mem_x), ite_eq_left (Finset.mem_insert_of_mem h.mem_y),
    ite_eq_left (Finset.mem_insert_of_mem h.mem_z), ite_eq_left (Finset.mem_insert_self _ _)] at hW
  exact ⟨hS', by omega, by simp only [State.a]; omega, by simp only [State.a]; omega,
    by simp only [State.a]; omega⟩

/-- **Cases 9 and 10** of [Mishra and Santhanam, Section 4.3][MishraSanthanam2026], the
bottleneck configuration: the unique child `D` of the minimal AND `G` reads an unpaired isolated
parameter `z`. If `D` is AND-type, fix `x` and `y` so that `D` becomes constant and delete `G`,
`D` and the second children of `x` and `y`: `Δa = -2`, `ΔW ≤ -28`. Otherwise `D` is XOR-type and
the quadratic reparameterisation deletes `G` and `D`: `Δa = -1`, `ΔW ≤ -14`. -/
theorem Valid.step_of_bottleneck {S : State n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) (hN : S.Normal) {G x y : ℕ}
    (h : S.MinimalAnd G x y) (h7 : ¬ S.SharedSecondChild G x y) (hbot : S.Bottleneck G x) :
    ∃ S', Step f S S' := by
  obtain ⟨hx2, D, z, hDiff, hD, hz, hz1, hDz⟩ := hbot
  have hy2 : S.deg y = 2 := le_antisymm (hx2 ▸ h.deg_le) h.deg_y
  have hDG : (S.gate D).Reads G := (hDiff D hD).2 rfl
  have hcG : S.children G = {.inl D} := by
    ext N
    constructor
    · intro hNG
      obtain ⟨K, hK, rfl, hKG⟩ := h.eq_inl_of_mem_children hS hNG
      rw [(hDiff K hK).1 hKG]
      exact Finset.mem_singleton_self _
    · intro hNm
      rw [Finset.mem_singleton] at hNm
      subst hNm
      exact (SemiCircuit.inl_mem_children _).2 ⟨hD, hDG⟩
  have hzp := (mem_unpaired.1 hz).1
  have hcz : S.children z = {.inl D} :=
    children_eq_singleton hz1 ((SemiCircuit.inl_mem_children _).2 ⟨hD, hDz⟩)
  have hzG := h.ne_gate hS hzp
  have hDx : ¬ (S.gate D).Reads x := (h.children D hD hDG).1
  have hDy : ¬ (S.gate D).Reads y := (h.children D hD hDG).2
  have hzx : z ≠ x := fun he => hDx (he ▸ hDz)
  have hzy : z ≠ y := fun he => hDy (he ▸ hDz)
  have hDG' : D ≠ G := fun he => hS.not_reads_self h.mem (he ▸ hDG)
  have hDargs := Gate.args_of_reads hzG hDz hDG
  obtain ⟨φ, hφ, hGφ⟩ := h.exists_op
  have hxG := h.ne_gate hS h.mem_params_x
  have hyG := h.ne_gate hS h.mem_params_y
  by_cases hDand : ¬ IsAffineOp (S.gate D).op
  · -- Case 9: fix `x` and `y` so that `G` takes the value making `D` constant
    obtain ⟨δ, c, hc⟩ := Gate.exists_const_of_not_isAffineOp hDand hDargs
    obtain ⟨x₀, y₀, hδ⟩ := exists_eq_of_not_isAffineOp' hφ δ
    obtain ⟨Bx, hBx, hBxG⟩ := Finset.exists_mem_ne (show 1 < (S.children x).card by
      change 1 < S.deg x; omega) (.inl G)
    obtain ⟨By, hBy, hByG⟩ := Finset.exists_mem_ne (show 1 < (S.children y).card by
      change 1 < S.deg y; omega) (.inl G)
    have hBxy : Bx ≠ By := fun he => h7 ⟨hx2, Bx, hBxG, hBx, he ▸ hBy⟩
    have hBxD : Bx ≠ .inl D := fun he => hDx ((SemiCircuit.inl_mem_children _).1 (he ▸ hBx)).2
    have hByD : By ≠ .inl D := fun he => hDy ((SemiCircuit.inl_mem_children _).1 (he ▸ hBy)).2
    have h₁ := hS.reduction_fixConst h.mem_params_x x₀
    have h₂ := h₁.valid.reduction_fixConst (Finset.mem_erase.2 ⟨h.ne.symm, h.mem_params_y⟩) y₀
    have h₃ := h₂.valid.reduction_deleteConst (J := G) (c := δ) h.mem fun val _ => by
      rw [fixConst_gate, Gate.eval_subst_const, fixConst_gate, Gate.eval_subst_const, hGφ,
        Function.update_self, Function.update_of_ne h.ne.symm, Function.update_self]
      exact hδ
    have h₄ := h₃.valid.reduction_deleteConst (J := D) (c := c)
      (Finset.mem_erase.2 ⟨hDG', hD⟩) fun val _ => by
        rw [deleteGate_gate, Gate.eval_subst_const, fixConst_gate, Gate.eval_subst_const,
          fixConst_gate, Gate.eval_subst_const]
        exact hc _ (by rw [Function.update_of_ne hxG.symm, Function.update_of_ne hyG.symm,
          Function.update_self])
    obtain ⟨S', h₅⟩ := h₄.valid.exists_reduction_deleteAll [Bx, By] (by simp [hBxy]) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro N (rfl | rfl)
      · exact h₄.deletable _ (by simpa using hBxD) (h₃.deletable _ (by simpa using hBxG)
          (h₂.deletable _ (by simp) (deletable_fixConst_child hS _ x₀ hBx)))
      · exact h₄.deletable _ (by simpa using hByD) (h₃.deletable _ (by simpa using hByG)
          (deletable_fixConst_child h₁.valid _ y₀
            (by rw [fixConst_children _ _ h.ne.symm]; exact hBy))))
    have hred := (((h₁.trans h₂).trans h₃).trans h₄).trans h₅
    simp only [Finset.union_empty, List.nil_append, List.cons_append, ← Finset.insert_eq] at hred
    refine ⟨S', hred.step hS Finset.card_le_two (by simp) ?_⟩
    have hW := hred.W_le (fun u => if u = z then 6 else 0) (fun _ => 0) fun u hu => by
      obtain ⟨-, huF⟩ := Finset.mem_sdiff.1 hu
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at huF
      by_cases huz : u = z
      · subst huz
        rw [hred.wt_eq_zero_of_subset (by simp [hcz]) (by simp [hcz, hBxD, hByD]), wt_of_mem hz,
          hz1, weight_one, ite_eq_left rfl]
      · rw [ite_eq_right huz]
        refine Nat.add_le_add_right (hred.wt_le_of_exclusive hS hN.exclusive
          (fun w hw hwu => ?_) fun N hNL _ => ?_) 0
        · rcases Finset.mem_insert.1 hw with rfl | hw
          · exact (mem_unpaired.1 h.unpaired_x).2 hwu.paired
          · rw [Finset.mem_singleton] at hw
            subst hw
            exact (mem_unpaired.1 h.unpaired_y).2 hwu.paired
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hNL
          rcases hNL with rfl | rfl
          · exact ⟨x, h.mem_params_x, Ne.symm huF.1, hBx⟩
          · exact ⟨y, h.mem_params_y, Ne.symm huF.2, hBy⟩
    have hk : (S.pairsMeeting {x, y}).card = 0 := by
      rw [hS.card_pairsMeeting_insert (by simpa using h.ne)
        (by simpa using fun hxy => (mem_unpaired.1 h.unpaired_x).2 hxy.paired),
        hS.card_pairsMeeting_singleton, ite_eq_right (mem_unpaired.1 h.unpaired_y).2,
        ite_eq_right (mem_unpaired.1 h.unpaired_x).2]
    have hzm : z ∈ S.params \ {x, y} := Finset.mem_sdiff.2 ⟨hzp, by simp [hzx, hzy]⟩
    rw [Finset.sum_ite_eq' _ z, ite_eq_left hzm, Finset.sum_pair h.ne, wt_of_mem h.unpaired_x,
      wt_of_mem h.unpaired_y, hx2, hy2, weight_of_two_le le_rfl, hk] at hW
    simp only [Finset.sum_const_zero, List.length_cons, List.length_nil] at hW
    rw [Finset.card_pair h.ne, hk]
    omega
  · -- Case 10: `D` is XOR-type and the quadratic reparameterisation applies
    push Not at hDand
    obtain ⟨c, hDc⟩ := exists_xor_form hDand
      (fun hun => hN.no_deletion (deletionAvailable_of_unary hD hun))
      (by
        by_contra hconst
        push Not at hconst
        exact hN.no_deletion (deletionAvailable_of_const_op hD hconst))
    obtain ⟨α, β, γ, hform⟩ := exists_and_form hφ
    refine ⟨_, hS.step_quad (x := x) (y := y) (z := z) (G := G) (D := D) (α := α) (β := β)
      (γ := γ) (c := c)
      { mem_x := h.mem_params_x
        mem_y := h.mem_params_y
        mem_z := hzp
        unpaired_x := (mem_unpaired.1 h.unpaired_x).2
        unpaired_y := (mem_unpaired.1 h.unpaired_y).2
        unpaired_z := (mem_unpaired.1 hz).2
        x_ne_y := h.ne
        x_ne_z := hzx.symm
        y_ne_z := hzy.symm
        mem_G := h.mem
        mem_D := hD
        G_ne_D := hDG'.symm
        eval_G := fun val => by
          rw [hGφ, hform]
          cases val x <;> cases val y <;> cases α <;> cases β <;> cases γ <;> rfl
        eval_D := fun val => by
          rcases hDargs with ⟨hl, hr⟩ | ⟨hl, hr⟩
          · rw [Gate.eval_of_args hl hr, hDc]
            cases val G <;> cases val z <;> cases c <;> rfl
          · rw [Gate.eval_of_args hl hr, hDc]
            cases val G <;> cases val z <;> cases c <;> rfl
        children_G := hcG
        children_z := hcz
        out_G := h.not_out
        out_z := hS.not_out_reads_param hf ha hzp }
      (h.deg_y.trans h.deg_le) h.deg_y⟩

/-- **Section 4.3** of [Mishra and Santhanam][MishraSanthanam2026]: in a normal state with
`d < a`, eliminating the minimal AND is a step of gate elimination. -/
theorem Valid.step_of_minimalAnd {S : State n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) (hN : S.Normal) {G x y : ℕ}
    (h : S.MinimalAnd G x y) : ∃ S', Step f S S' := by
  by_cases h7 : S.SharedSecondChild G x y
  · exact hS.step_of_sharedSecondChild hN h h7
  by_cases hbot : S.Bottleneck G x
  · exact hS.step_of_bottleneck hf ha hN h h7 hbot
  · exact hS.step_fixInput hN h h7 hbot

end State

end Cslib.Circuits.Boolean.AffineDisperser
