/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AffineDisperser.Normal

/-!
# The minimal AND

Sections 4.2 and 4.3 of [Mishra and Santhanam][MishraSanthanam2026].

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
auxiliary variable `Q` of degree at least two depending on it keeps `m`, `s`, `q`, `a` and every
child, and does not increase `W`: both weights are `7`. -/
theorem Valid.prep_swap {S : State n} (hS : S.Valid f) {x Q : ℕ} {c : Bool} {T : Finset ℕ}
    (hx : x ∈ S.unpaired) (hxdeg : 2 ≤ S.deg x) (hQ : Q ∈ S.aux) (hQdeg : 2 ≤ S.deg Q)
    (haff : S.AffineIn Q c T) (hxT : x ∈ T) :
    (S.swap x Q c T).Valid f ∧ (S.swap x Q c T).m = S.m ∧ (S.swap x Q c T).s = S.s ∧
      (S.swap x Q c T).q = S.q ∧ (S.swap x Q c T).W ≤ S.W := by
  obtain ⟨hxp, hxu⟩ := mem_unpaired.1 hx
  have hok : S.SwapOK x Q c T := ⟨hxp, hxu, hQ, haff, hxT⟩
  have hQp : Q ∉ S.params := fun hp => Finset.disjoint_left.1 hS.wf.disjoint_params_aux hp hQ
  have hQx : Q ≠ x := fun h => hQp (h ▸ hxp)
  set S₁ := S.swap x Q c T
  have hm : S₁.m = S.m := by
    show (insert Q (S.params.erase x)).card = S.params.card
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

/-- Rewiring a gate to a gate reading only parameters of degree at least two keeps `m`, `s`, `q`
and `a` and does not increase `W`: only those parameters may gain a child, and their weight is
already `7`. -/
theorem Valid.prep_rewire {S : State n} (hS : S.Valid f) {J : ℕ} {g : Gate}
    (h : S.RewireOK J g) (hdeg : ∀ t, g.Reads t → t ∈ S.unpaired → 2 ≤ S.deg t) :
    (S.rewire J g).Valid f ∧ (S.rewire J g).m = S.m ∧ (S.rewire J g).s = S.s ∧
      (S.rewire J g).q = S.q ∧ (S.rewire J g).W ≤ S.W := by
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

/-! ### Eliminating the minimal AND -/

/-- The configuration of Section 4.3: `G` is an AND-type gate reading the distinct unpaired
parameters `x` and `y` with `2 ≤ deg y ≤ deg x`, no child of `G` reads `x` or `y`, and `G` is not
the output and has a child. -/
structure MinAnd (S : State n) (G x y : ℕ) : Prop where
  mem : G ∈ S.gates
  and_op : ¬ IsAffineOp (S.gate G).op
  args : ((S.gate G).left = .node x ∧ (S.gate G).right = .node y) ∨
    ((S.gate G).left = .node y ∧ (S.gate G).right = .node x)
  unpaired_x : x ∈ S.unpaired
  unpaired_y : y ∈ S.unpaired
  ne : x ≠ y
  deg_y : 2 ≤ S.deg y
  deg_le : S.deg y ≤ S.deg x
  children : ∀ K ∈ S.gates, (S.gate K).Reads G → ¬ (S.gate K).Reads x ∧ ¬ (S.gate K).Reads y
  not_out : ¬ S.out.Reads G
  has_child : ∃ K ∈ S.gates, (S.gate K).Reads G

/-- The configuration of Case 7: `deg x = deg y = 2` and the second children coincide. -/
def Case7 (S : State n) (G x y : ℕ) : Prop :=
  S.deg x = 2 ∧ ∃ B, B ≠ .inl G ∧ B ∈ S.children x ∧ B ∈ S.children y

/-- The bottleneck configuration: `deg x = 2`, `G` has a unique child `D`, and `D` reads an
unpaired isolated parameter `z`. -/
def Bottleneck (S : State n) (G x : ℕ) : Prop :=
  S.deg x = 2 ∧ ∃ D z, (∀ K ∈ S.gates, (S.gate K).Reads G ↔ K = D) ∧ D ∈ S.gates ∧
    z ∈ S.unpaired ∧ S.deg z = 1 ∧ (S.gate D).Reads z

/-- **Case 7** of [Mishra and Santhanam][MishraSanthanam2026]. -/
theorem Valid.step_case7 {S : State n} (hS : S.Valid f) (hdel : ¬ S.DeletionAvailable)
    {G x y : ℕ} (h : S.MinAnd G x y) (h7 : S.Case7 G x y) : ∃ S', Step f S S' := by
  sorry


/-- **Case 8** of [Mishra and Santhanam][MishraSanthanam2026]. -/
theorem Valid.step_case8 {S : State n} (hS : S.Valid f) (hexcl : S.Exclusive)
    (hdel : ¬ S.DeletionAvailable) {G x y : ℕ} (h : S.MinAnd G x y) (h7 : ¬ S.Case7 G x y)
    (hbot : ¬ S.Bottleneck G x) : ∃ S', Step f S S' := by
  sorry


/-- **Cases 9 and 10** of [Mishra and Santhanam][MishraSanthanam2026]. -/
theorem Valid.step_bottleneck {S : State n} {d : ℕ} (hS : S.Valid f)
    (hf : IsAffineDisperser f d) (ha : d < S.a) (hexcl : S.Exclusive)
    (hdel : ¬ S.DeletionAvailable) {G x y : ℕ} (h : S.MinAnd G x y) (h7 : ¬ S.Case7 G x y)
    (hbot : S.Bottleneck G x) : ∃ S', Step f S S' := by
  sorry


end State

end Cslib.Circuits.Boolean.AffineDisperser
