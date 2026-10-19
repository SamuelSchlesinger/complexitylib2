/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.B2.Operations

/-!
# Chains of deletions

The reductions of [Mishra and Santhanam, Section 4][MishraSanthanam2026] restrict parameters and
then delete several gates and equations in a row, each by (D1) or (D3). A *deletion step*
(`State.DelStep`) deletes one constraint `N` and keeps the parameters and pairs; it reroutes `N`
to a literal reading at most one internal value `t`, the *target*, which is a parent of `N`, and
changes the children of no other parameter except by removing `N`. A *chain*
(`State.Chain`) is a sequence of deletion steps.

Along a chain, a parameter gains children only through a deletion targeting it, and the first
such deletion removes one of its original children (`State.Chain.children_cases`). This is the
observation behind every weight estimate of the source: an unpaired parameter can increase its
weight only when it is isolated and its unique child is deleted and rerouted to it.

A gate with a constant argument or two equal arguments, and an equation with at most two terms,
are *deletable* (`State.Deletable`), and deleting one deletable constraint keeps the others
deletable, so any list of distinct deletable constraints is deleted by a chain
(`State.Valid.exists_chain`).

## Main definitions

* `Cslib.Circuits.Boolean.B2.State.DelStep`, `Cslib.Circuits.Boolean.B2.State.Chain`:
  deletion steps and chains.
* `Cslib.Circuits.Boolean.B2.State.Deletable`: deletable constraints.

## Main results

* `Cslib.Circuits.Boolean.B2.State.Chain.children_cases`: how children change along a chain.
* `Cslib.Circuits.Boolean.B2.State.Valid.exists_chain`: deletable constraints are deleted by
  chains.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.B2

open Finset

/-- The internal value read by a literal, if any. -/
def Lit.target (ℓ : Lit) : Option ℕ :=
  match ℓ.arg with
  | .node t => some t
  | .const _ => none

theorem Lit.target_eq_some {ℓ : Lit} {t : ℕ} : ℓ.target = some t ↔ ℓ.Reads t := by
  unfold target Reads
  cases ℓ.arg <;> simp

/-- The literal computed by a gate with a constant argument or two equal arguments. -/
def Gate.lit (g : Gate) : Lit :=
  match g.left with
  | .const b =>
    if g.op b false = g.op b true then Lit.const (g.op b false) else ⟨g.right, g.op b false⟩
  | .node t =>
    match g.right with
    | .const b =>
      if g.op false b = g.op true b then Lit.const (g.op false b) else ⟨.node t, g.op false b⟩
    | .node _ =>
      if g.op false false = g.op true true then Lit.const (g.op false false)
      else ⟨.node t, g.op false false⟩

/-- The gate has a constant argument or two equal arguments. -/
def Gate.Degenerate (g : Gate) : Prop :=
  (∃ b, g.left = .const b) ∨ (∃ b, g.right = .const b) ∨ g.left = g.right

/-- A Boolean function of one bit is a constant or a literal. -/
theorem unary_cases (h : Bool → Bool) (x : Bool) :
    h x = if h false = h true then h false else (x ^^ h false) := by
  cases x <;> cases h0 : h false <;> cases h1 : h true <;> simp_all

/-- The literal computing the Boolean function `h` of one bit applied to the argument `a`. -/
def unaryLit (h : Bool → Bool) (a : Arg) : Lit :=
  if h false = h true then Lit.const (h false) else ⟨a, h false⟩

theorem eval_unaryLit (h : Bool → Bool) (a : Arg) (val : ℕ → Bool) :
    h (a.eval val) = (unaryLit h a).eval val := by
  rw [unary_cases h (a.eval val)]
  unfold unaryLit
  split_ifs <;> simp [Lit.eval, Lit.const]

theorem reads_of_unaryLit_reads {h : Bool → Bool} {a : Arg} {t : ℕ}
    (hr : (unaryLit h a).Reads t) : a = .node t := by
  unfold unaryLit at hr
  split_ifs at hr
  · simp [Lit.Reads, Lit.const] at hr
  · exact hr

theorem Gate.eval_lit {g : Gate} (hg : g.Degenerate) (val : ℕ → Bool) :
    g.eval val = g.lit.eval val := by
  obtain ⟨op, l, r⟩ := g
  unfold Degenerate at hg
  unfold eval
  cases l with
  | const b =>
    simp only [lit, Arg.eval_const]
    rw [unary_cases (op b) (r.eval val)]
    split_ifs <;> simp [Lit.eval, Lit.const]
  | node t =>
    cases r with
    | const b =>
      simp only [lit, Arg.eval_const, Arg.eval_node]
      rw [unary_cases (fun x => op x b) (val t)]
      split_ifs <;> simp [Lit.eval, Lit.const]
    | node t' =>
      simp only at hg
      rcases hg with ⟨b, hb⟩ | ⟨b, hb⟩ | hb
      · cases hb
      · cases hb
      · cases hb
        simp only [lit, Arg.eval_node]
        rw [unary_cases (fun x => op x x) (val t)]
        split_ifs <;> simp [Lit.eval, Lit.const]

theorem Gate.reads_of_lit_reads {g : Gate} {t : ℕ} (h : g.lit.Reads t) : g.Reads t := by
  obtain ⟨op, l, r⟩ := g
  unfold Reads
  cases l with
  | const b =>
    simp only [lit] at h
    split_ifs at h
    · simp [Lit.Reads, Lit.const] at h
    · exact Or.inr h
  | node s =>
    cases r with
    | const b =>
      simp only [lit] at h
      split_ifs at h
      · simp [Lit.Reads, Lit.const] at h
      · exact Or.inl h
    | node s' =>
      simp only [lit] at h
      split_ifs at h
      · simp [Lit.Reads, Lit.const] at h
      · exact Or.inl h

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Deletion steps and chains -/

/-- A deletion step from `S` to `S'`: the constraint `N` is deleted, the parameters and pairs are
kept, the size drops by one, the children of every parameter other than the target `t` lose
`N` and gain nothing, and the target is a parent of `N`. -/
structure DelStep (f : BooleanFunction n) (S S' : State n) (N : ℕ ⊕ ℕ) (t : Option ℕ) :
    Prop where
  valid : S'.Valid f
  params : S'.params = S.params
  pairs : S'.pairs = S.pairs
  size : S'.size + 1 = S.size
  children : ∀ z ∈ S.params, t ≠ some z → S'.children z ⊆ (S.children z).erase N
  target : ∀ z, t = some z → N ∈ S.children z

/-- A chain of deletion steps, recording each deleted constraint with its target. -/
inductive Chain (f : BooleanFunction n) :
    State n → State n → List ((ℕ ⊕ ℕ) × Option ℕ) → Prop
  | nil (S : State n) : Chain f S S []
  | cons {S S₁ S₂ : State n} {N : ℕ ⊕ ℕ} {t : Option ℕ} {l : List ((ℕ ⊕ ℕ) × Option ℕ)} :
      DelStep f S S₁ N t → Chain f S₁ S₂ l → Chain f S S₂ ((N, t) :: l)

namespace Chain

variable {S S' : State n} {l : List ((ℕ ⊕ ℕ) × Option ℕ)}

theorem valid (h : Chain f S S' l) (hS : S.Valid f) : S'.Valid f := by
  induction h with
  | nil => exact hS
  | cons hstep _ ih => exact ih hstep.valid

theorem params (h : Chain f S S' l) : S'.params = S.params := by
  induction h with
  | nil => rfl
  | cons hstep _ ih => rw [ih, hstep.params]

theorem pairs (h : Chain f S S' l) : S'.pairs = S.pairs := by
  induction h with
  | nil => rfl
  | cons hstep _ ih => rw [ih, hstep.pairs]

theorem size (h : Chain f S S' l) : S'.size + l.length = S.size := by
  induction h with
  | nil => rfl
  | cons hstep _ ih =>
    rw [List.length_cons, ← hstep.size, ← ih]
    omega

theorem append {S₁ S₂ : State n} {l₁ l₂ : List ((ℕ ⊕ ℕ) × Option ℕ)} (h₁ : Chain f S S₁ l₁)
    (h₂ : Chain f S₁ S₂ l₂) : Chain f S S₂ (l₁ ++ l₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons hstep _ ih => exact .cons hstep (ih h₂)

/-- Along a chain, the children of a parameter only lose the deleted constraints, unless some
deletion targets it; and then some deletion targeting it removes one of its original
children. -/
theorem children_cases (h : Chain f S S' l) {z : ℕ} (hz : z ∈ S.params) :
    S'.children z ⊆ S.children z \ (l.map Prod.fst).toFinset ∨
      ∃ q ∈ l, q.2 = some z ∧ q.1 ∈ S.children z := by
  induction h with
  | nil => exact Or.inl (by simp)
  | @cons S S₁ S₂ N t l hstep hchain ih =>
    have hz₁ : z ∈ S₁.params := hstep.params ▸ hz
    by_cases ht : t = some z
    · exact Or.inr ⟨(N, t), List.mem_cons_self, ht, hstep.target z ht⟩
    · have hsub := hstep.children z hz ht
      rcases ih hz₁ with ih | ⟨q, hq, hqz, hq₁⟩
      · refine Or.inl fun w hw => ?_
        have hw' := ih hw
        rw [Finset.mem_sdiff] at hw' ⊢
        have := Finset.mem_erase.1 (hsub hw'.1)
        refine ⟨this.2, ?_⟩
        simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert, not_or]
        exact ⟨this.1, hw'.2⟩
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hqz, Finset.mem_of_mem_erase (hsub hq₁)⟩

end Chain

/-! ### Deletion steps of the operations -/

/-- Deleting a gate is a deletion step targeting the internal value read by the literal. -/
theorem Valid.delStep_deleteGate {S : State n} (hS : S.Valid f) {J : ℕ} {ℓ : Lit}
    (h : S.DeleteGateOK J ℓ) : DelStep f S (S.deleteGate J ℓ) (.inl J) ℓ.target where
  valid := hS.deleteGate h
  params := rfl
  pairs := rfl
  size := deleteGate_size h
  children _ hz ht := deleteGate_children_of_ne hS h hz fun hr => ht (Lit.target_eq_some.2 hr)
  target z ht := (SemiCircuit.inl_mem_children _).2 ⟨h.mem, h.reads z (Lit.target_eq_some.1 ht)⟩

/-- Deleting an equation is a deletion step targeting the internal value read by the
literal. -/
theorem Valid.delStep_deleteEqn {S : State n} (hS : S.Valid f) {e v : ℕ} {ℓ : Lit}
    (h : S.DeleteEqnOK e v ℓ) : DelStep f S (S.deleteEqn e v ℓ) (.inr e) ℓ.target where
  valid := hS.deleteEqn h
  params := rfl
  pairs := rfl
  size := deleteEqn_size h
  children _ hz ht := deleteEqn_children_of_ne hS h hz fun hr => ht (Lit.target_eq_some.2 hr)
  target z ht := (SemiCircuit.inr_mem_children _).2
    ⟨h.mem, (h.reads z (Lit.target_eq_some.1 ht)).1⟩

/-- Deleting a trivial equation is a deletion step without target. -/
theorem Valid.delStep_dropTrivialEqn {S : State n} (hS : S.Valid f) {e : ℕ} (he : e ∈ S.eqns)
    (hterms : (S.eqn e).terms = ∅) : DelStep f S (S.dropTrivialEqn e) (.inr e) none where
  valid := hS.dropTrivialEqn he hterms
  params := rfl
  pairs := rfl
  size := dropTrivialEqn_size he
  children z _ _ := by rw [dropTrivialEqn_children]
  target _ h := by cases h

/-! ### Deletable constraints -/

/-- A deletable constraint: a gate with a constant argument or two equal arguments, or an
equation with at most two terms. -/
def Deletable (S : State n) : ℕ ⊕ ℕ → Prop
  | .inl J => J ∈ S.gates ∧ (S.gate J).Degenerate
  | .inr e => e ∈ S.eqns ∧ (S.eqn e).terms.card ≤ 2

theorem Gate.degenerate_subst {g : Gate} (hg : g.Degenerate) (v : ℕ) (ℓ : Lit) :
    (g.subst v ℓ).Degenerate := by
  unfold Gate.Degenerate at *
  change (∃ b, g.left.substArg v ℓ.arg = .const b) ∨ (∃ b, g.right.substArg v ℓ.arg = .const b) ∨
    g.left.substArg v ℓ.arg = g.right.substArg v ℓ.arg
  rcases hg with ⟨b, hb⟩ | ⟨b, hb⟩ | hb
  · exact Or.inl ⟨b, by rw [hb]; rfl⟩
  · exact Or.inr (Or.inl ⟨b, by rw [hb]; rfl⟩)
  · exact Or.inr (Or.inr (by rw [hb]))

/-- In a valid state, an equation whose terms are all parameters has no terms. -/
theorem Valid.terms_eq_empty_of_subset {S : State n} (hS : S.Valid f) {e : ℕ} (he : e ∈ S.eqns)
    (hsub : (S.eqn e).terms ⊆ S.params) : (S.eqn e).terms = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hne
  obtain ⟨val, hval, heq⟩ := hS.wf.solvable 0
  obtain ⟨val', hval', heq'⟩ := hS.wf.solvable (Function.update val x (!val x))
  have h1 := heq e he
  have h2 := heq' e he
  unfold Equation.Holds at h1 h2
  rw [← Finset.add_sum_erase _ _ hx] at h1 h2
  rw [Finset.sum_congr rfl fun i hi => by
    rw [hval' i (hsub (Finset.mem_of_mem_erase hi)),
      Function.update_of_ne (Finset.ne_of_mem_erase hi)], hval' x (hsub hx),
    Function.update_self, ← h1] at h2
  cases val x <;> simp at h2

/-- A deletable constraint of a valid state is deleted by a deletion step after which every
other deletable constraint stays deletable. -/
theorem Valid.exists_delStep {S : State n} (hS : S.Valid f) {N : ℕ ⊕ ℕ} (hN : S.Deletable N) :
    ∃ S' t, DelStep f S S' N t ∧ ∀ N', N' ≠ N → S.Deletable N' → S'.Deletable N' := by
  rcases N with J | e
  · obtain ⟨hJ, hdeg⟩ := hN
    have hok : S.DeleteGateOK J (S.gate J).lit :=
      ⟨hJ, fun t ht => Gate.reads_of_lit_reads ht, Or.inl fun val _ => Gate.eval_lit hdeg val⟩
    refine ⟨_, _, hS.delStep_deleteGate hok, fun N' hN' hdel => ?_⟩
    rcases N' with K | e'
    · obtain ⟨hK, hKdeg⟩ := hdel
      have hKJ : K ≠ J := fun he => hN' (by rw [he])
      exact ⟨Finset.mem_erase.2 ⟨hKJ, hK⟩, Gate.degenerate_subst hKdeg _ _⟩
    · obtain ⟨he', hcard⟩ := hdel
      exact ⟨he', Equation.card_subst_le.trans hcard⟩
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
        have hok : S.DeleteEqnOK e v ⟨.node U, (S.eqn e).rhs⟩ := by
          refine ⟨he, hva, fun val => ?_, fun t ht => ?_⟩
          · unfold Equation.Holds
            rw [hterms, Finset.sum_pair hUv.symm]
            simp only [Lit.eval, Arg.eval_node]
            generalize val v = a; generalize val U = b; generalize (S.eqn e).rhs = r
            revert a b r; decide
          · cases ht
            exact ⟨Finset.mem_of_mem_erase hUmem, hUv⟩
        refine ⟨_, _, hS.delStep_deleteEqn hok, fun N' hN' hdel => ?_⟩
        rcases N' with K | e'
        · obtain ⟨hK, hKdeg⟩ := hdel
          exact ⟨hK, Gate.degenerate_subst hKdeg _ _⟩
        · obtain ⟨he', hcard'⟩ := hdel
          have hee : e' ≠ e := fun h' => hN' (by rw [h'])
          exact ⟨Finset.mem_erase.2 ⟨hee, he'⟩, Equation.card_subst_le.trans hcard'⟩
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
        have hok : S.DeleteEqnOK e v (Lit.const (S.eqn e).rhs) := by
          refine ⟨he, hva, fun val => ?_, fun t ht => by cases ht⟩
          unfold Equation.Holds
          rw [hterms, Finset.sum_singleton, Lit.eval_const]
        refine ⟨_, _, hS.delStep_deleteEqn hok, fun N' hN' hdel => ?_⟩
        rcases N' with K | e'
        · obtain ⟨hK, hKdeg⟩ := hdel
          exact ⟨hK, Gate.degenerate_subst hKdeg _ _⟩
        · obtain ⟨he', hcard'⟩ := hdel
          have hee : e' ≠ e := fun h' => hN' (by rw [h'])
          exact ⟨Finset.mem_erase.2 ⟨hee, he'⟩, Equation.card_subst_le.trans hcard'⟩
    · push Not at haux
      have hsub : (S.eqn e).terms ⊆ S.params := fun i hi => by
        rcases Finset.mem_union.1 (hS.wf.terms_subset e he hi) with hp | ha
        · exact hp
        · exact absurd ha (haux i hi)
      have hempty := hS.terms_eq_empty_of_subset he hsub
      refine ⟨_, _, hS.delStep_dropTrivialEqn he hempty, fun N' hN' hdel => ?_⟩
      rcases N' with K | e'
      · exact hdel
      · obtain ⟨he', hcard'⟩ := hdel
        have hee : e' ≠ e := fun h' => hN' (by rw [h'])
        exact ⟨Finset.mem_erase.2 ⟨hee, he'⟩, hcard'⟩

/-- Distinct deletable constraints of a valid state are deleted by a chain, in order. -/
theorem Valid.exists_chain {S : State n} (hS : S.Valid f) (l : List (ℕ ⊕ ℕ)) (hl : l.Nodup)
    (hdel : ∀ N ∈ l, S.Deletable N) :
    ∃ S' tl, Chain f S S' tl ∧ tl.map Prod.fst = l := by
  induction l generalizing S with
  | nil => exact ⟨S, [], .nil S, rfl⟩
  | cons N l ih =>
    obtain ⟨S₁, t, hstep, hpres⟩ := hS.exists_delStep (hdel N List.mem_cons_self)
    have hl' := List.nodup_cons.1 hl
    obtain ⟨S', tl, hchain, hmap⟩ := ih hstep.valid hl'.2 fun N' hN' =>
      hpres N' (fun he => hl'.1 (he ▸ hN')) (hdel N' (List.mem_cons_of_mem _ hN'))
    exact ⟨S', (N, t) :: tl, .cons hstep hchain, by rw [List.map_cons, hmap]⟩

end State

end Cslib.Circuits.Boolean.B2
