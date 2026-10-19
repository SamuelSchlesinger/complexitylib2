/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AffineDisperser.State

/-!
# Operations of gate elimination

The operations of [Mishra and Santhanam, Sections 2.3, 2.4 and 3][MishraSanthanam2026] on states,
each with its validity and its effect on the counted quantities and on the children of the
parameters:

* `State.restrict`: fixing a parameter to a constant or to a literal of another parameter, the
  restrictions (UF) and (PF) of the source;
* `State.deleteGate`: deleting a gate that computes a literal of one of its inputs, or a constant,
  or that is unused, rerouting its uses (D1) and (D2);
* `State.deleteEqn`: deleting an equation `v = ℓ` of the affine system together with its
  auxiliary variable `v`, rerouting `v` to `ℓ` (D3);
* `State.dropEqn`: deleting an equation together with an auxiliary variable occurring nowhere
  else (the second half of D4), and `State.dropTrivialEqn`: deleting an equation without terms;
* `State.swap`: exchanging a parameter with an auxiliary variable depending on it, the affine
  reparameterisation (AR);
* `State.quad`: the quadratic reparameterisation (QR) deleting an AND-type gate and the XOR-type
  gate reading it;
* `State.moveAffine`: moving an affine gate reading no gates into the affine system;
* `State.rewire`: replacing a gate by one computing the same value on consistent assignments,
  used to reroute the children of the minimal AND.

Validity of a state whose parameter map changes is transported along a map `σ` from the new
assignments to the old ones (`State.Valid.of_map`).

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.of_map`: transporting validity.
* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.restrict`, `Valid.deleteGate`, `Valid.deleteEqn`,
  `Valid.dropEqn`, `Valid.dropTrivialEqn`, `Valid.swap`, `Valid.quad`, `Valid.moveAffine`,
  `Valid.rewire`: the operations preserve validity.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset Cslib.BitString SemiCircuit

theorem isAffine_lit_eval {k : ℕ} {τ : BitString k → ℕ → Bool} (hτ : IsAffine τ) (ℓ : Lit) :
    IsAffine fun u => ℓ.eval (τ u) := by
  intro u v w
  obtain ⟨_ | t, c⟩ := ℓ
  · simp only [Lit.eval, Arg.eval_const]
    generalize ‹Bool› = b
    revert b c; decide
  · simp only [Lit.eval, Arg.eval_node, congrFun (hτ u v w) t, Pi.add_apply]
    generalize τ u t = a; generalize τ v t = b; generalize τ w t = e
    revert a b e c; decide

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Transporting validity -/

/-- A state with the parameters, pairs and parameter map of a valid state is valid when its
semi-circuit is well formed and computes `f`. -/
theorem Valid.of_phi {S S' : State n} (hS : S.Valid f) (hparams : S'.params = S.params)
    (hpairs : S'.pairs = S.pairs) (hphi : S'.phi = S.phi) (hwf : S'.WellFormed)
    (hcomp : ∀ val, S'.Consistent val → S'.out.eval val = f (S'.phi val)) : S'.Valid f where
  wf := hwf
  pair_mem := by rw [hpairs, hparams]; exact hS.pair_mem
  pairs_disjoint := by rw [hpairs]; exact hS.pairs_disjoint
  phi_congr := by rw [hphi, hparams]; exact hS.phi_congr
  phi_affine := by rw [hphi, hpairs]; exact hS.phi_affine
  phi_injective := by rw [hphi, hparams]; exact hS.phi_injective
  computes := hcomp

/-- Validity transported along a map `σ` from the assignments of a new state to those of a valid
state: `σ` maps consistent assignments to consistent assignments with the same output, the new
parameter map is the old one after `σ`, `σ` matches the parameters of both states injectively,
and `σ` maps affine families on which the new pairs are tame to families agreeing on the old
parameters with affine families on which the old pairs are tame. -/
theorem Valid.of_map {S S' : State n} (hS : S.Valid f) (σ : (ℕ → Bool) → ℕ → Bool)
    (hwf : S'.WellFormed)
    (hpair_mem : ∀ pr ∈ S'.pairs, pr.1 ∈ S'.params ∧ pr.2 ∈ S'.params ∧ pr.1 ≠ pr.2)
    (hdisj : ∀ pr ∈ S'.pairs, ∀ pr' ∈ S'.pairs, pr ≠ pr' →
      pr.1 ≠ pr'.1 ∧ pr.1 ≠ pr'.2 ∧ pr.2 ≠ pr'.1 ∧ pr.2 ≠ pr'.2)
    (hphi : ∀ val, S'.phi val = S.phi (σ val))
    (hcongr : ∀ val val', (∀ j ∈ S'.params, val j = val' j) →
      ∀ j ∈ S.params, σ val j = σ val' j)
    (hinj : ∀ val val', (∀ j ∈ S.params, σ val j = σ val' j) →
      ∀ j ∈ S'.params, val j = val' j)
    (haff : ∀ (k : ℕ) (τ : BitString k → ℕ → Bool), IsAffine τ →
      (∀ pr ∈ S'.pairs, PairTame τ pr) → ∃ τ' : BitString k → ℕ → Bool, IsAffine τ' ∧
        (∀ pr ∈ S.pairs, PairTame τ' pr) ∧ ∀ u, ∀ j ∈ S.params, τ' u j = σ (τ u) j)
    (hcons : ∀ val, S'.Consistent val → S.Consistent (σ val))
    (hout : ∀ val, S'.Consistent val → S'.out.eval val = S.out.eval (σ val)) :
    S'.Valid f where
  wf := hwf
  pair_mem := hpair_mem
  pairs_disjoint := hdisj
  phi_congr val val' h := by
    rw [hphi, hphi]
    exact hS.phi_congr _ _ (hcongr val val' h)
  phi_affine k τ hτ htame := by
    obtain ⟨τ', hτ', htame', hagree⟩ := haff k τ hτ htame
    have : S'.phi ∘ τ = S.phi ∘ τ' := funext fun u => by
      simp only [Function.comp_apply, hphi]
      exact hS.phi_congr _ _ fun j hj => (hagree u j hj).symm
    rw [this]
    exact hS.phi_affine k τ' hτ' htame'
  phi_injective val val' h := hinj val val' (hS.phi_injective _ _ (by rwa [hphi, hphi] at h))
  computes val hval := by
    rw [hout val hval, hphi]
    exact hS.computes _ (hcons val hval)

/-! ### Restrictions (UF) and (PF) -/

/-- Restrict the parameter `x` to the literal `ℓ`, a constant or a literal of another parameter,
keeping the pairs `P`. -/
def restrict (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset (ℕ × ℕ)) : State n where
  toSemiCircuit := { S.toSemiCircuit.subst x ℓ with params := S.params.erase x }
  pairs := P
  phi val := S.phi (Function.update val x (ℓ.eval val))

/-- The hypotheses of a restriction: `x` is a parameter, `ℓ` reads at most another parameter,
the kept pairs avoid `x`, and every dropped pair contains `x` and the other parameter read by
`ℓ`, if any. -/
structure RestrictOK (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset (ℕ × ℕ)) : Prop where
  mem : x ∈ S.params
  reads : ∀ y, ℓ.Reads y → y ∈ S.params ∧ y ≠ x
  subset : P ⊆ S.pairs
  avoid : ∀ pr ∈ P, pr.1 ≠ x ∧ pr.2 ≠ x
  drop : ∀ pr ∈ S.pairs, pr ∉ P → (pr.1 = x ∨ pr.2 = x) ∧ ∀ y, ℓ.Reads y → y = pr.1 ∨ y = pr.2

@[simp] theorem restrict_params (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset (ℕ × ℕ)) :
    (S.restrict x ℓ P).params = S.params.erase x := rfl

@[simp] theorem restrict_pairs (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset (ℕ × ℕ)) :
    (S.restrict x ℓ P).pairs = P := rfl

theorem restrict_children (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset (ℕ × ℕ)) (z : ℕ) :
    (S.restrict x ℓ P).children z = (S.toSemiCircuit.subst x ℓ).children z := rfl

theorem restrict_size (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset (ℕ × ℕ)) :
    (S.restrict x ℓ P).size = S.size := rfl

@[simp] theorem restrict_gate (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset (ℕ × ℕ)) (J : ℕ) :
    (S.restrict x ℓ P).gate J = (S.gate J).subst x ℓ := rfl

@[simp] theorem restrict_eqn (S : State n) (x : ℕ) (ℓ : Lit) (P : Finset (ℕ × ℕ)) (e : ℕ) :
    (S.restrict x ℓ P).eqn e = (S.eqn e).subst x ℓ := rfl

/-- Restrictions preserve validity. -/
theorem Valid.restrict {S : State n} (hS : S.Valid f) {x : ℕ} {ℓ : Lit} {P : Finset (ℕ × ℕ)}
    (h : S.RestrictOK x ℓ P) : (S.restrict x ℓ P).Valid f := by
  have hℓx : ℓ.arg ≠ .node x := fun he => (h.reads x he).2 rfl
  have hℓeval : ∀ val val' : ℕ → Bool, (∀ j ∈ S.params.erase x, val j = val' j) →
      ℓ.eval val = ℓ.eval val' := fun val val' hv =>
    Lit.eval_congr fun y hy => hv y (Finset.mem_erase.2 ⟨(h.reads y hy).2, (h.reads y hy).1⟩)
  have hupd : ∀ val, ℓ.eval (Function.update val x (ℓ.eval val)) = ℓ.eval val := fun val =>
    hℓeval _ _ fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
  have hxg : x ∉ S.gates := fun hg => Finset.disjoint_left.1 hS.wf.disjoint_params_gates h.mem hg
  have hxa : x ∉ S.aux := fun ha => Finset.disjoint_left.1 hS.wf.disjoint_params_aux h.mem ha
  -- consistency of the substituted circuit does not see `x`
  have hcons_upd : ∀ val b, (S.toSemiCircuit.subst x ℓ).Consistent (Function.update val x b) ↔
      (S.toSemiCircuit.subst x ℓ).Consistent val :=
    SemiCircuit.consistent_update_iff hxg (fun J _ => Gate.not_reads_subst hℓx)
      (fun e _ => Equation.notMem_subst hℓx)
  have hwf : (S.restrict x ℓ P).WellFormed := by
    refine
      { disjoint_params_aux := Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
          hS.wf.disjoint_params_aux
        disjoint_params_gates := Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
          hS.wf.disjoint_params_gates
        disjoint_aux_gates := hS.wf.disjoint_aux_gates
        reads_lt := fun J hJ i hi hr => ?_
        reads_live := fun J hJ i hr => ?_
        terms_subset := fun e he z hz => ?_
        card_terms_le := fun e he => Equation.card_subst_le.trans (hS.wf.card_terms_le e he)
        out_live := fun i hi => ?_
        solvable := fun u => ?_
        unique := fun val val' hagree heq heq' v hv => ?_ }
    · rcases Gate.reads_of_reads_subst hr with hr | ⟨-, hr⟩
      · exact hS.wf.reads_lt J hJ i hi hr
      · exact absurd hi fun hg =>
          Finset.disjoint_left.1 hS.wf.disjoint_params_gates (h.reads i hr).1 hg
    · have hix : i ≠ x := by rintro rfl; exact Gate.not_reads_subst hℓx hr
      have hlive : i ∈ S.live := by
        rcases Gate.reads_of_reads_subst hr with hr | ⟨-, hr⟩
        · exact hS.wf.reads_live J hJ i hr
        · simp only [SemiCircuit.live, Finset.mem_union]; exact Or.inl (Or.inl (h.reads i hr).1)
      simp only [SemiCircuit.live, Finset.mem_union] at hlive ⊢
      change (i ∈ S.params.erase x ∨ i ∈ S.aux) ∨ i ∈ S.gates
      rw [Finset.mem_erase]
      tauto
    · have hzx : z ≠ x := by rintro rfl; exact Equation.notMem_subst hℓx hz
      have hmem : z ∈ S.params ∪ S.aux := by
        rcases Equation.mem_of_mem_subst hz with hz | ⟨-, hz⟩
        · exact hS.wf.terms_subset e he hz
        · exact Finset.mem_union_left _ (h.reads z hz).1
      simp only [Finset.mem_union] at hmem ⊢
      change z ∈ S.params.erase x ∨ z ∈ S.aux
      rw [Finset.mem_erase]
      tauto
    · have hix : i ≠ x := by rintro rfl; exact Lit.not_reads_subst hℓx hi
      have hlive : i ∈ S.live := by
        rcases Lit.reads_of_reads_subst hi with hi | ⟨-, hi⟩
        · exact hS.wf.out_live i hi
        · simp only [SemiCircuit.live, Finset.mem_union]; exact Or.inl (Or.inl (h.reads i hi).1)
      simp only [SemiCircuit.live, Finset.mem_union] at hlive ⊢
      change (i ∈ S.params.erase x ∨ i ∈ S.aux) ∨ i ∈ S.gates
      rw [Finset.mem_erase]
      tauto
    · obtain ⟨val, hu, heq⟩ := hS.wf.solvable (Function.update u x (ℓ.eval u))
      have hvx : val x = ℓ.eval val := by
        rw [hu x h.mem, Function.update_self]
        exact hℓeval _ _ fun j hj => by
          rw [hu j (Finset.mem_of_mem_erase hj), Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      refine ⟨val, fun j hj => ?_, fun e he => (Equation.holds_subst hvx).2 (heq e he)⟩
      rw [hu j (Finset.mem_of_mem_erase hj), Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    · have hold : ∀ w : ℕ → Bool, (S.restrict x ℓ P).EqnsHold w →
          S.EqnsHold (Function.update w x (ℓ.eval w)) := fun w hw e he => by
        have hx : Function.update w x (ℓ.eval w) x =
            ℓ.eval (Function.update w x (ℓ.eval w)) := by rw [Function.update_self, hupd]
        refine (Equation.holds_subst hx).1 ?_
        refine (Equation.holds_congr fun i hi => ?_).2 (hw e he)
        exact Function.update_of_ne (by rintro rfl; exact Equation.notMem_subst hℓx hi) _ _
      have := hS.wf.unique _ _ (fun j hj => by
          by_cases hjx : j = x
          · subst hjx
            simp only [Function.update_self]
            exact hℓeval _ _ hagree
          · simp only [Function.update_of_ne hjx]
            exact hagree j (Finset.mem_erase.2 ⟨hjx, hj⟩))
        (hold val heq) (hold val' heq') v hv
      have hvx : v ≠ x := by rintro rfl; exact hxa hv
      simpa only [Function.update_of_ne hvx] using this
  refine hS.of_map (fun val => Function.update val x (ℓ.eval val)) hwf ?_ ?_ (fun _ => rfl) ?_ ?_
    ?_ ?_ ?_
  · intro pr hpr
    obtain ⟨h1, h2, h12⟩ := hS.pair_mem pr (h.subset hpr)
    exact ⟨Finset.mem_erase.2 ⟨(h.avoid pr hpr).1, h1⟩,
      Finset.mem_erase.2 ⟨(h.avoid pr hpr).2, h2⟩, h12⟩
  · exact fun pr hpr pr' hpr' => hS.pairs_disjoint pr (h.subset hpr) pr' (h.subset hpr')
  · intro val val' hv j hj
    by_cases hjx : j = x
    · subst hjx
      simp only [Function.update_self]
      exact hℓeval _ _ hv
    · simp only [Function.update_of_ne hjx]
      exact hv j (Finset.mem_erase.2 ⟨hjx, hj⟩)
  · intro val val' hv j hj
    have := hv j (Finset.mem_of_mem_erase hj)
    simpa only [Function.update_of_ne (Finset.ne_of_mem_erase hj)] using this
  · intro k τ hτ htame
    refine ⟨fun u => Function.update (τ u) x (ℓ.eval (τ u)),
      isAffine_update hτ x (isAffine_lit_eval hτ ℓ), fun pr hpr => ?_, fun _ _ _ => rfl⟩
    by_cases hP : pr ∈ P
    · have hav := h.avoid pr hP
      rcases htame pr hP with ht | ht | ht
      · exact Or.inl fun u v => by simpa only [Function.update_of_ne hav.1] using ht u v
      · exact Or.inr (Or.inl fun u v => by simpa only [Function.update_of_ne hav.2] using ht u v)
      · exact Or.inr (Or.inr fun u v => by
          simpa only [Function.update_of_ne hav.1, Function.update_of_ne hav.2] using ht u v)
    · obtain ⟨hx, hy⟩ := h.drop pr hpr hP
      obtain ⟨p1, p2⟩ := pr
      obtain ⟨_ | t, c⟩ := ℓ
      · -- a constant restriction makes the member `x` constant
        simp only at hx
        rcases hx with rfl | rfl
        · exact Or.inl fun u v => by simp only [Function.update_self, Lit.eval, Arg.eval_const]
        · exact Or.inr (Or.inl fun u v => by
            simp only [Function.update_self, Lit.eval, Arg.eval_const])
      · -- a restriction to the partner makes the sum of the pair constant
        have ht := hy t rfl
        have htx : t ≠ x := (h.reads t rfl).2
        refine Or.inr (Or.inr fun u v => ?_)
        simp only at hx ht ⊢
        rcases hx with rfl | rfl <;> rcases ht with rfl | rfl
        · exact absurd rfl htx
        · simp only [Function.update_self, Function.update_of_ne htx, Lit.eval, Arg.eval_node]
          cases τ u t <;> cases τ v t <;> cases c <;> rfl
        · simp only [Function.update_self, Function.update_of_ne htx, Lit.eval, Arg.eval_node]
          cases τ u t <;> cases τ v t <;> cases c <;> rfl
        · exact absurd rfl htx
  · intro val hval
    have hx : Function.update val x (ℓ.eval val) x =
        ℓ.eval (Function.update val x (ℓ.eval val)) := by rw [Function.update_self, hupd]
    exact (SemiCircuit.consistent_subst hx).1 ((hcons_upd val _).2 hval)
  · intro val _
    have hx : Function.update val x (ℓ.eval val) x =
        ℓ.eval (Function.update val x (ℓ.eval val)) := by rw [Function.update_self, hupd]
    change (S.out.subst x ℓ).eval val = _
    rw [← Lit.eval_subst hx]
    exact Lit.eval_congr fun i hi =>
      (Function.update_of_ne (by rintro rfl; exact Lit.not_reads_subst hℓx hi) _ _).symm


/-! ### Deleting a gate (D1) and (D2) -/

/-- Delete the gate `J`, rerouting its uses to the literal `ℓ`. -/
def deleteGate (S : State n) (J : ℕ) (ℓ : Lit) : State n :=
  { S with toSemiCircuit := { S.toSemiCircuit.subst J ℓ with gates := S.gates.erase J } }

/-- The hypotheses of a gate deletion: `J` is a gate, `ℓ` reads at most an input of `J`, and
either `J` computes `ℓ` on the solutions of the affine system or nothing reads `J`. -/
structure DeleteGateOK (S : State n) (J : ℕ) (ℓ : Lit) : Prop where
  mem : J ∈ S.gates
  reads : ∀ t, ℓ.Reads t → (S.gate J).Reads t
  value : (∀ val, S.EqnsHold val → (S.gate J).eval val = ℓ.eval val) ∨
    ((∀ K ∈ S.gates, ¬ (S.gate K).Reads J) ∧ ¬ S.out.Reads J)

@[simp] theorem deleteGate_params (S : State n) (J : ℕ) (ℓ : Lit) :
    (S.deleteGate J ℓ).params = S.params := rfl

@[simp] theorem deleteGate_pairs (S : State n) (J : ℕ) (ℓ : Lit) :
    (S.deleteGate J ℓ).pairs = S.pairs := rfl

@[simp] theorem deleteGate_phi (S : State n) (J : ℕ) (ℓ : Lit) :
    (S.deleteGate J ℓ).phi = S.phi := rfl

@[simp] theorem deleteGate_gate (S : State n) (J : ℕ) (ℓ : Lit) (K : ℕ) :
    (S.deleteGate J ℓ).gate K = (S.gate K).subst J ℓ := rfl

@[simp] theorem deleteGate_eqn (S : State n) (J : ℕ) (ℓ : Lit) (e : ℕ) :
    (S.deleteGate J ℓ).eqn e = (S.eqn e).subst J ℓ := rfl

@[simp] theorem deleteGate_gates (S : State n) (J : ℕ) (ℓ : Lit) :
    (S.deleteGate J ℓ).gates = S.gates.erase J := rfl

theorem deleteGate_size {S : State n} {J : ℕ} {ℓ : Lit}
    (h : S.DeleteGateOK J ℓ) : (S.deleteGate J ℓ).size + 1 = S.size := by
  have := Finset.card_erase_add_one h.mem
  simp only [SemiCircuit.size] at *
  change (S.gates.erase J).card + S.eqns.card + 1 = _
  omega

theorem notMem_terms_of_mem_gates {S : State n} (hS : S.Valid f) {J e : ℕ} (hJ : J ∈ S.gates)
    (he : e ∈ S.eqns) : J ∉ (S.eqn e).terms := fun hJe => by
  rcases Finset.mem_union.1 (hS.wf.terms_subset e he hJe) with h | h
  · exact Finset.disjoint_left.1 hS.wf.disjoint_params_gates h hJ
  · exact Finset.disjoint_left.1 hS.wf.disjoint_aux_gates h hJ

theorem Valid.not_reads_self {S : State n} (hS : S.Valid f) {J : ℕ} (hJ : J ∈ S.gates) :
    ¬ (S.gate J).Reads J := fun h => lt_irrefl J (hS.wf.reads_lt J hJ J hJ h)

theorem DeleteGateOK.not_reads {S : State n} (hS : S.Valid f) {J : ℕ} {ℓ : Lit}
    (h : S.DeleteGateOK J ℓ) : ℓ.arg ≠ .node J := fun he =>
  hS.not_reads_self h.mem (h.reads J he)

theorem deleteGate_children_subset {S : State n} {J : ℕ} {ℓ : Lit} (z : ℕ) :
    (S.deleteGate J ℓ).children z ⊆ ((S.toSemiCircuit.subst J ℓ).children z).erase (.inl J) := by
  intro w hw
  rcases w with K | e
  · simp only [SemiCircuit.inl_mem_children] at hw
    refine Finset.mem_erase.2 ⟨fun he => ?_, ?_⟩
    · cases he; exact Finset.notMem_erase J _ hw.1
    · exact (SemiCircuit.inl_mem_children _).2 ⟨Finset.mem_of_mem_erase hw.1, hw.2⟩
  · simp only [SemiCircuit.inr_mem_children] at hw
    exact Finset.mem_erase.2 ⟨Sum.inr_ne_inl, (SemiCircuit.inr_mem_children _).2 hw⟩

/-- Deleting a gate removes it from the children of every parameter other than the target of
`ℓ`. -/
theorem deleteGate_children_of_ne {S : State n} (hS : S.Valid f) {J : ℕ} {ℓ : Lit}
    (h : S.DeleteGateOK J ℓ) {z : ℕ} (hz : z ∈ S.params) (hzℓ : ¬ ℓ.Reads z) :
    (S.deleteGate J ℓ).children z ⊆ (S.children z).erase (.inl J) := by
  have hzJ : z ≠ J := fun he => Finset.disjoint_left.1 hS.wf.disjoint_params_gates hz (he ▸ h.mem)
  have := deleteGate_children_subset (S := S) (J := J) (ℓ := ℓ) z
  rwa [SemiCircuit.children_subst hzJ hzℓ] at this

/-- After deleting a gate, the children of the target of `ℓ` are among its former children and
those of the gate. -/
theorem deleteGate_children_target {S : State n} {J : ℕ} {ℓ : Lit} (z : ℕ) :
    (S.deleteGate J ℓ).children z ⊆ (S.children z ∪ S.children J).erase (.inl J) :=
  (deleteGate_children_subset z).trans
    (Finset.erase_subset_erase _ (SemiCircuit.children_subst_subset J ℓ z))

/-- Deleting a gate preserves validity. -/
theorem Valid.deleteGate {S : State n} (hS : S.Valid f) {J : ℕ} {ℓ : Lit}
    (h : S.DeleteGateOK J ℓ) : (S.deleteGate J ℓ).Valid f := by
  have hℓJ := h.not_reads hS
  have heqn : ∀ e ∈ S.eqns, (S.eqn e).subst J ℓ = S.eqn e := fun e he =>
    Equation.subst_of_notMem (notMem_terms_of_mem_gates hS h.mem he)
  have heqns : ∀ val, (S.deleteGate J ℓ).EqnsHold val ↔ S.EqnsHold val := fun val =>
    forall₂_congr fun e he => by
      change ((S.eqn e).subst J ℓ).Holds val ↔ _
      rw [heqn e he]
  have hlive : ∀ i, i ∈ S.live → i ≠ J → i ∈ (S.deleteGate J ℓ).live := by
    intro i hi hiJ
    simp only [SemiCircuit.live, Finset.mem_union] at hi ⊢
    change (i ∈ S.params ∨ i ∈ S.aux) ∨ i ∈ S.gates.erase J
    rw [Finset.mem_erase]
    tauto
  have hreads_live : ∀ t, ℓ.Reads t → t ∈ S.live := fun t ht => hS.wf.reads_live J h.mem t (h.reads t ht)
  refine hS.of_phi rfl rfl rfl ?_ ?_
  · refine
      { disjoint_params_aux := hS.wf.disjoint_params_aux
        disjoint_params_gates := Finset.disjoint_of_subset_right (Finset.erase_subset _ _)
          hS.wf.disjoint_params_gates
        disjoint_aux_gates := Finset.disjoint_of_subset_right (Finset.erase_subset _ _)
          hS.wf.disjoint_aux_gates
        reads_lt := fun K hK i hi hr => ?_
        reads_live := fun K hK i hr => ?_
        terms_subset := fun e he => by
          change ((S.eqn e).subst J ℓ).terms ⊆ _
          rw [heqn e he]; exact hS.wf.terms_subset e he
        card_terms_le := fun e he => Equation.card_subst_le.trans (hS.wf.card_terms_le e he)
        out_live := fun i hi => ?_
        solvable := fun u => by
          obtain ⟨val, hu, heq⟩ := hS.wf.solvable u
          exact ⟨val, hu, (heqns val).2 heq⟩
        unique := fun val val' hagree heq heq' =>
          hS.wf.unique val val' hagree ((heqns val).1 heq) ((heqns val').1 heq') }
    · have hK' := Finset.mem_of_mem_erase hK
      have hi' := Finset.mem_of_mem_erase hi
      rcases Gate.reads_of_reads_subst hr with hr | ⟨hrJ, hr⟩
      · exact hS.wf.reads_lt K hK' i hi' hr
      · exact (hS.wf.reads_lt J h.mem i hi' (h.reads i hr)).trans
          (hS.wf.reads_lt K hK' J h.mem hrJ)
    · refine hlive i ?_ fun he => Gate.not_reads_subst hℓJ (he ▸ hr)
      rcases Gate.reads_of_reads_subst hr with hr | ⟨-, hr⟩
      · exact hS.wf.reads_live K (Finset.mem_of_mem_erase hK) i hr
      · exact hreads_live i hr
    · refine hlive i ?_ fun he => Lit.not_reads_subst hℓJ (he ▸ hi)
      rcases Lit.reads_of_reads_subst hi with hi | ⟨-, hi⟩
      · exact hS.wf.out_live i hi
      · exact hreads_live i hi
  · intro val hval
    set w := Function.update val J ((S.gate J).eval val)
    have hw : ∀ i, i ≠ J → w i = val i := fun i hi => Function.update_of_ne hi _ _
    have hwJval : w J = (S.gate J).eval val := Function.update_self _ _ _
    have hwJ : w J = (S.gate J).eval w := by
      rw [hwJval]
      exact Gate.eval_congr fun i hi => (hw i fun he => hS.not_reads_self h.mem (he ▸ hi)).symm
    have hℓw : ℓ.eval w = ℓ.eval val := Lit.eval_congr fun i hi => hw i fun he => hℓJ (he ▸ hi)
    have hcons : S.Consistent w := by
      refine ⟨fun e he => ?_, fun K hK => ?_⟩
      · refine (Equation.holds_congr fun i hi => hw i fun he' => ?_).2 ((heqns val).1 hval.1 e he)
        exact notMem_terms_of_mem_gates hS h.mem he (he' ▸ hi)
      · by_cases hKJ : K = J
        · subst hKJ; exact hwJ
        · have hK' : K ∈ (S.deleteGate J ℓ).gates := Finset.mem_erase.2 ⟨hKJ, hK⟩
          rw [hw K hKJ, hval.2 K hK']
          change ((S.gate K).subst J ℓ).eval val = _
          rcases h.value with hv | ⟨hun, -⟩
          · have hJw : w J = ℓ.eval w := by
              rw [hwJval, hv val ((heqns val).1 hval.1), hℓw]
            rw [← Gate.eval_subst hJw]
            exact Gate.eval_congr fun i hi =>
              (hw i fun he => Gate.not_reads_subst hℓJ (he ▸ hi)).symm
          · rw [Gate.eval_subst_of_not_reads (hun K hK)]
            exact Gate.eval_congr fun i hi => (hw i fun he => hun K hK (he ▸ hi)).symm
    have hout : (S.deleteGate J ℓ).out.eval val = S.out.eval w := by
      change (S.out.subst J ℓ).eval val = _
      rcases h.value with hv | ⟨-, hun⟩
      · have hJw : w J = ℓ.eval w := by
          rw [hwJval, hv val ((heqns val).1 hval.1), hℓw]
        rw [← Lit.eval_subst hJw]
        exact Lit.eval_congr fun i hi => (hw i fun he => Lit.not_reads_subst hℓJ (he ▸ hi)).symm
      · rw [Lit.subst_of_not_reads hun]
        exact Lit.eval_congr fun i hi => (hw i fun he => hun (he ▸ hi)).symm
    rw [hout, hS.computes w hcons]
    congr 1
    exact hS.phi_congr _ _ fun j hj =>
      hw j fun he => Finset.disjoint_left.1 hS.wf.disjoint_params_gates hj (he ▸ h.mem)

/-! ### Deleting an equation (D3) -/

/-- Delete the equation `e`, which reads `v = ℓ`, and the auxiliary variable `v`, rerouting `v`
to `ℓ`. -/
def deleteEqn (S : State n) (e v : ℕ) (ℓ : Lit) : State n :=
  { S with toSemiCircuit :=
    { S.toSemiCircuit.subst v ℓ with aux := S.aux.erase v, eqns := S.eqns.erase e } }

/-- The hypotheses of deleting an equation: `e` is an equation stating `v = ℓ` for an auxiliary
variable `v` and a literal `ℓ` reading at most another term of `e`. -/
structure DeleteEqnOK (S : State n) (e v : ℕ) (ℓ : Lit) : Prop where
  mem : e ∈ S.eqns
  aux : v ∈ S.aux
  holds : ∀ val, (S.eqn e).Holds val ↔ val v = ℓ.eval val
  reads : ∀ t, ℓ.Reads t → t ∈ (S.eqn e).terms ∧ t ≠ v

@[simp] theorem deleteEqn_params (S : State n) (e v : ℕ) (ℓ : Lit) :
    (S.deleteEqn e v ℓ).params = S.params := rfl

@[simp] theorem deleteEqn_pairs (S : State n) (e v : ℕ) (ℓ : Lit) :
    (S.deleteEqn e v ℓ).pairs = S.pairs := rfl

@[simp] theorem deleteEqn_phi (S : State n) (e v : ℕ) (ℓ : Lit) :
    (S.deleteEqn e v ℓ).phi = S.phi := rfl

theorem deleteEqn_size {S : State n} {e v : ℕ} {ℓ : Lit} (h : S.DeleteEqnOK e v ℓ) :
    (S.deleteEqn e v ℓ).size + 1 = S.size := by
  have := Finset.card_erase_add_one h.mem
  simp only [SemiCircuit.size] at *
  change S.gates.card + (S.eqns.erase e).card + 1 = _
  omega

theorem deleteEqn_children_subset {S : State n} {e v : ℕ} {ℓ : Lit} (z : ℕ) :
    (S.deleteEqn e v ℓ).children z ⊆ ((S.toSemiCircuit.subst v ℓ).children z).erase (.inr e) := by
  intro w hw
  rcases w with K | e'
  · simp only [SemiCircuit.inl_mem_children] at hw
    exact Finset.mem_erase.2 ⟨Sum.inl_ne_inr, (SemiCircuit.inl_mem_children _).2 hw⟩
  · simp only [SemiCircuit.inr_mem_children] at hw
    refine Finset.mem_erase.2 ⟨fun he => ?_, ?_⟩
    · cases he; exact Finset.notMem_erase e _ hw.1
    · exact (SemiCircuit.inr_mem_children _).2 ⟨Finset.mem_of_mem_erase hw.1, hw.2⟩

theorem deleteEqn_children_of_ne {S : State n} (hS : S.Valid f) {e v : ℕ} {ℓ : Lit}
    (h : S.DeleteEqnOK e v ℓ) {z : ℕ} (hz : z ∈ S.params) (hzℓ : ¬ ℓ.Reads z) :
    (S.deleteEqn e v ℓ).children z ⊆ (S.children z).erase (.inr e) := by
  have hzv : z ≠ v := fun he => Finset.disjoint_left.1 hS.wf.disjoint_params_aux hz (he ▸ h.aux)
  have := deleteEqn_children_subset (S := S) (e := e) (v := v) (ℓ := ℓ) z
  rwa [SemiCircuit.children_subst hzv hzℓ] at this

theorem deleteEqn_children_target {S : State n} {e v : ℕ} {ℓ : Lit} (z : ℕ) :
    (S.deleteEqn e v ℓ).children z ⊆ (S.children z ∪ S.children v).erase (.inr e) :=
  (deleteEqn_children_subset z).trans
    (Finset.erase_subset_erase _ (SemiCircuit.children_subst_subset v ℓ z))

/-- Deleting an equation `v = ℓ` with its auxiliary variable preserves validity. -/
theorem Valid.deleteEqn {S : State n} (hS : S.Valid f) {e v : ℕ} {ℓ : Lit}
    (h : S.DeleteEqnOK e v ℓ) : (S.deleteEqn e v ℓ).Valid f := by
  have hℓv : ℓ.arg ≠ .node v := fun he => (h.reads v he).2 rfl
  have hℓpa : ∀ t, ℓ.Reads t → t ∈ S.params ∪ S.aux ∧ t ≠ v := fun t ht =>
    ⟨hS.wf.terms_subset e h.mem (h.reads t ht).1, (h.reads t ht).2⟩
  have hvp : v ∉ S.params := fun hp => Finset.disjoint_left.1 hS.wf.disjoint_params_aux hp h.aux
  have hvg : v ∉ S.gates := fun hg => Finset.disjoint_left.1 hS.wf.disjoint_aux_gates h.aux hg
  -- extending an assignment by the value of `v`
  let ext : (ℕ → Bool) → ℕ → Bool := fun val => Function.update val v (ℓ.eval val)
  have hext : ∀ val i, i ≠ v → ext val i = val i := fun val i hi => Function.update_of_ne hi _ _
  have hextv : ∀ val, ext val v = ℓ.eval (ext val) := fun val => by
    change Function.update val v (ℓ.eval val) v = _
    rw [Function.update_self]
    exact Lit.eval_congr fun i hi => (hext val i fun he => hℓv (he ▸ hi)).symm
  have hold : ∀ val, (S.deleteEqn e v ℓ).EqnsHold val → S.EqnsHold (ext val) := by
    intro val hval e' he'
    by_cases hee : e' = e
    · subst hee; exact (h.holds _).2 (hextv val)
    · refine (Equation.holds_subst (hextv val)).1 ?_
      refine (Equation.holds_congr fun i hi => hext val i fun he => ?_).2
        (hval e' (Finset.mem_erase.2 ⟨hee, he'⟩))
      exact Equation.notMem_subst hℓv (he ▸ hi)
  have hlive : ∀ i, i ∈ S.live → i ≠ v → i ∈ (S.deleteEqn e v ℓ).live := by
    intro i hi hiv
    simp only [SemiCircuit.live, Finset.mem_union] at hi ⊢
    change (i ∈ S.params ∨ i ∈ S.aux.erase v) ∨ i ∈ S.gates
    rw [Finset.mem_erase]
    tauto
  refine hS.of_phi rfl rfl rfl ?_ ?_
  · refine
      { disjoint_params_aux := Finset.disjoint_of_subset_right (Finset.erase_subset _ _)
          hS.wf.disjoint_params_aux
        disjoint_params_gates := hS.wf.disjoint_params_gates
        disjoint_aux_gates := Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
          hS.wf.disjoint_aux_gates
        reads_lt := fun K hK i hi hr => ?_
        reads_live := fun K hK i hr => ?_
        terms_subset := fun e' he' z hz => ?_
        card_terms_le := fun e' he' => Equation.card_subst_le.trans
          (hS.wf.card_terms_le e' (Finset.mem_of_mem_erase he'))
        out_live := fun i hi => ?_
        solvable := fun u => ?_
        unique := fun val val' hagree heq heq' a ha => ?_ }
    · rcases Gate.reads_of_reads_subst hr with hr | ⟨-, hr⟩
      · exact hS.wf.reads_lt K hK i hi hr
      · exfalso
        rcases Finset.mem_union.1 (hℓpa i hr).1 with hp | ha
        · exact Finset.disjoint_left.1 hS.wf.disjoint_params_gates hp hi
        · exact Finset.disjoint_left.1 hS.wf.disjoint_aux_gates ha hi
    · refine hlive i ?_ fun he => Gate.not_reads_subst hℓv (he ▸ hr)
      rcases Gate.reads_of_reads_subst hr with hr | ⟨-, hr⟩
      · exact hS.wf.reads_live K hK i hr
      · simp only [SemiCircuit.live, Finset.mem_union]
        exact Or.inl (Finset.mem_union.1 (hℓpa i hr).1)
    · have hzv : z ≠ v := fun he => Equation.notMem_subst hℓv (he ▸ hz)
      have hmem : z ∈ S.params ∪ S.aux := by
        rcases Equation.mem_of_mem_subst hz with hz | ⟨-, hz⟩
        · exact hS.wf.terms_subset e' (Finset.mem_of_mem_erase he') hz
        · exact (hℓpa z hz).1
      change z ∈ S.params ∪ S.aux.erase v
      simp only [Finset.mem_union, Finset.mem_erase] at hmem ⊢
      tauto
    · refine hlive i ?_ fun he => Lit.not_reads_subst hℓv (he ▸ hi)
      rcases Lit.reads_of_reads_subst hi with hi | ⟨-, hi⟩
      · exact hS.wf.out_live i hi
      · simp only [SemiCircuit.live, Finset.mem_union]
        exact Or.inl (Finset.mem_union.1 (hℓpa i hi).1)
    · obtain ⟨val, hu, heq⟩ := hS.wf.solvable u
      have hv : val v = ℓ.eval val := (h.holds val).1 (heq e h.mem)
      exact ⟨val, hu, fun e' he' =>
        (Equation.holds_subst hv).2 (heq e' (Finset.mem_of_mem_erase he'))⟩
    · have := hS.wf.unique (ext val) (ext val') (fun j hj => by
          rw [hext val j fun he => hvp (he ▸ hj), hext val' j fun he => hvp (he ▸ hj)]
          exact hagree j hj) (hold val heq) (hold val' heq') a (Finset.mem_of_mem_erase ha)
      rwa [hext val a (Finset.ne_of_mem_erase ha), hext val' a (Finset.ne_of_mem_erase ha)] at this
  · intro val hval
    have hcons : S.Consistent (ext val) := by
      refine ⟨hold val hval.1, fun K hK => ?_⟩
      rw [hext val K fun he => hvg (he ▸ hK), hval.2 K hK]
      change ((S.gate K).subst v ℓ).eval val = _
      rw [← Gate.eval_subst (hextv val)]
      exact Gate.eval_congr fun i hi =>
        (hext val i fun he => Gate.not_reads_subst hℓv (he ▸ hi)).symm
    have hout : (S.deleteEqn e v ℓ).out.eval val = S.out.eval (ext val) := by
      change (S.out.subst v ℓ).eval val = _
      rw [← Lit.eval_subst (hextv val)]
      exact Lit.eval_congr fun i hi =>
        (hext val i fun he => Lit.not_reads_subst hℓv (he ▸ hi)).symm
    rw [hout, hS.computes _ hcons]
    congr 1
    exact hS.phi_congr _ _ fun j hj => hext val j fun he => hvp (he ▸ hj)


/-! ### Dropping an equation (D4) -/

/-- Delete the equation `e` together with an auxiliary variable `v` occurring nowhere else. -/
def dropEqn (S : State n) (e v : ℕ) : State n :=
  { S with aux := S.aux.erase v, eqns := S.eqns.erase e }

/-- The hypotheses of dropping an equation: the auxiliary variable `v` occurs in the equation
`e` and nowhere else. -/
structure DropEqnOK (S : State n) (e v : ℕ) : Prop where
  mem : e ∈ S.eqns
  aux : v ∈ S.aux
  mem_terms : v ∈ (S.eqn e).terms
  only : ∀ e' ∈ S.eqns, e' ≠ e → v ∉ (S.eqn e').terms
  gates : ∀ K ∈ S.gates, ¬ (S.gate K).Reads v
  out : ¬ S.out.Reads v

@[simp] theorem dropEqn_params (S : State n) (e v : ℕ) : (S.dropEqn e v).params = S.params := rfl

@[simp] theorem dropEqn_pairs (S : State n) (e v : ℕ) : (S.dropEqn e v).pairs = S.pairs := rfl

theorem dropEqn_size {S : State n} {e v : ℕ} (h : S.DropEqnOK e v) :
    (S.dropEqn e v).size + 1 = S.size := by
  have := Finset.card_erase_add_one h.mem
  simp only [SemiCircuit.size] at *
  change S.gates.card + (S.eqns.erase e).card + 1 = _
  omega

theorem dropEqn_children (S : State n) (e v z : ℕ) :
    (S.dropEqn e v).children z = (S.children z).erase (.inr e) := by
  ext (K | e')
  · simp only [SemiCircuit.inl_mem_children, Finset.mem_erase, ne_eq, reduceCtorEq,
      not_false_eq_true, true_and]
    rfl
  · simp only [SemiCircuit.inr_mem_children, Finset.mem_erase, ne_eq, Sum.inr.injEq]
    change (e' ∈ S.eqns.erase e ∧ _) ↔ _
    rw [Finset.mem_erase]
    tauto

/-- Dropping an equation with an auxiliary variable occurring only there preserves validity. -/
theorem Valid.dropEqn {S : State n} (hS : S.Valid f) {e v : ℕ} (h : S.DropEqnOK e v) :
    (S.dropEqn e v).Valid f := by
  have hvp : v ∉ S.params := fun hp => Finset.disjoint_left.1 hS.wf.disjoint_params_aux hp h.aux
  have hvg : v ∉ S.gates := fun hg => Finset.disjoint_left.1 hS.wf.disjoint_aux_gates h.aux hg
  let ext : (ℕ → Bool) → ℕ → Bool := fun val =>
    Function.update val v ((S.eqn e).rhs + ∑ i ∈ (S.eqn e).terms.erase v, val i)
  have hext : ∀ val i, i ≠ v → ext val i = val i := fun val i hi => Function.update_of_ne hi _ _
  have hold : ∀ val, (S.dropEqn e v).EqnsHold val → S.EqnsHold (ext val) := by
    intro val hval e' he'
    by_cases hee : e' = e
    · subst hee
      unfold Equation.Holds
      rw [← Finset.add_sum_erase _ _ h.mem_terms,
        Finset.sum_congr rfl fun i hi => hext val i (Finset.ne_of_mem_erase hi)]
      change Function.update val v _ v + _ = _
      rw [Function.update_self, add_assoc, BooleanRing.add_self, add_zero]
    · exact (Equation.holds_congr fun i hi => hext val i fun he => h.only e' he' hee (he ▸ hi)).2
        (hval e' (Finset.mem_erase.2 ⟨hee, he'⟩))
  refine hS.of_phi rfl rfl rfl ?_ ?_
  · refine
      { disjoint_params_aux := Finset.disjoint_of_subset_right (Finset.erase_subset _ _)
          hS.wf.disjoint_params_aux
        disjoint_params_gates := hS.wf.disjoint_params_gates
        disjoint_aux_gates := Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
          hS.wf.disjoint_aux_gates
        reads_lt := hS.wf.reads_lt
        reads_live := fun K hK i hr => ?_
        terms_subset := fun e' he' z hz => ?_
        card_terms_le := fun e' he' => hS.wf.card_terms_le e' (Finset.mem_of_mem_erase he')
        out_live := fun i hi => ?_
        solvable := fun u => by
          obtain ⟨val, hu, heq⟩ := hS.wf.solvable u
          exact ⟨val, hu, fun e' he' => heq e' (Finset.mem_of_mem_erase he')⟩
        unique := fun val val' hagree heq heq' a ha => ?_ }
    · have := hS.wf.reads_live K hK i hr
      have hiv : i ≠ v := fun he => h.gates K hK (he ▸ hr)
      simp only [SemiCircuit.live, Finset.mem_union] at this ⊢
      change (i ∈ S.params ∨ i ∈ S.aux.erase v) ∨ i ∈ S.gates
      rw [Finset.mem_erase]
      tauto
    · have := hS.wf.terms_subset e' (Finset.mem_of_mem_erase he') hz
      have hzv : z ≠ v := fun he =>
        h.only e' (Finset.mem_of_mem_erase he') (Finset.ne_of_mem_erase he') (he ▸ hz)
      change z ∈ S.params ∪ S.aux.erase v
      simp only [Finset.mem_union, Finset.mem_erase] at this ⊢
      tauto
    · have := hS.wf.out_live i hi
      have hiv : i ≠ v := fun he => h.out (he ▸ hi)
      simp only [SemiCircuit.live, Finset.mem_union] at this ⊢
      change (i ∈ S.params ∨ i ∈ S.aux.erase v) ∨ i ∈ S.gates
      rw [Finset.mem_erase]
      tauto
    · have := hS.wf.unique (ext val) (ext val') (fun j hj => by
          rw [hext val j fun he => hvp (he ▸ hj), hext val' j fun he => hvp (he ▸ hj)]
          exact hagree j hj) (hold val heq) (hold val' heq') a (Finset.mem_of_mem_erase ha)
      rwa [hext val a (Finset.ne_of_mem_erase ha), hext val' a (Finset.ne_of_mem_erase ha)] at this
  · intro val hval
    have hcons : S.Consistent (ext val) := by
      refine ⟨hold val hval.1, fun K hK => ?_⟩
      rw [hext val K fun he => hvg (he ▸ hK), hval.2 K hK]
      exact Gate.eval_congr fun i hi => (hext val i fun he => h.gates K hK (he ▸ hi)).symm
    have hout : S.out.eval val = S.out.eval (ext val) :=
      Lit.eval_congr fun i hi => (hext val i fun he => h.out (he ▸ hi)).symm
    change S.out.eval val = f (S.phi val)
    rw [hout, hS.computes _ hcons]
    congr 1
    exact hS.phi_congr _ _ fun j hj => hext val j fun he => hvp (he ▸ hj)

/-- Delete an equation without terms. -/
def dropTrivialEqn (S : State n) (e : ℕ) : State n :=
  { S with eqns := S.eqns.erase e }

@[simp] theorem dropTrivialEqn_params (S : State n) (e : ℕ) :
    (S.dropTrivialEqn e).params = S.params := rfl

@[simp] theorem dropTrivialEqn_pairs (S : State n) (e : ℕ) :
    (S.dropTrivialEqn e).pairs = S.pairs := rfl

theorem dropTrivialEqn_size {S : State n} {e : ℕ} (he : e ∈ S.eqns) :
    (S.dropTrivialEqn e).size + 1 = S.size := by
  have := Finset.card_erase_add_one he
  simp only [SemiCircuit.size] at *
  change S.gates.card + (S.eqns.erase e).card + 1 = _
  omega

theorem dropTrivialEqn_children (S : State n) (e z : ℕ) :
    (S.dropTrivialEqn e).children z = (S.children z).erase (.inr e) := by
  ext (K | e')
  · simp only [SemiCircuit.inl_mem_children, Finset.mem_erase, ne_eq, reduceCtorEq,
      not_false_eq_true, true_and]
    rfl
  · simp only [SemiCircuit.inr_mem_children, Finset.mem_erase, ne_eq, Sum.inr.injEq]
    change (e' ∈ S.eqns.erase e ∧ _) ↔ _
    rw [Finset.mem_erase]
    tauto

/-- An equation without terms of a valid state holds trivially, and deleting it preserves
validity. -/
theorem Valid.dropTrivialEqn {S : State n} (hS : S.Valid f) {e : ℕ} (he : e ∈ S.eqns)
    (hterms : (S.eqn e).terms = ∅) : (S.dropTrivialEqn e).Valid f := by
  have htriv : ∀ val, (S.eqn e).Holds val := by
    obtain ⟨val₀, -, heq⟩ := hS.wf.solvable 0
    intro val
    have h0 := heq e he
    unfold Equation.Holds at h0 ⊢
    rw [hterms, Finset.sum_empty] at h0 ⊢
    exact h0
  have heqns : ∀ val, (S.dropTrivialEqn e).EqnsHold val ↔ S.EqnsHold val := fun val =>
    ⟨fun h e' he' => by
      by_cases hee : e' = e
      · subst hee; exact htriv val
      · exact h e' (Finset.mem_erase.2 ⟨hee, he'⟩),
     fun h e' he' => h e' (Finset.mem_of_mem_erase he')⟩
  refine hS.of_phi rfl rfl rfl ?_ ?_
  · exact
      { disjoint_params_aux := hS.wf.disjoint_params_aux
        disjoint_params_gates := hS.wf.disjoint_params_gates
        disjoint_aux_gates := hS.wf.disjoint_aux_gates
        reads_lt := hS.wf.reads_lt
        reads_live := hS.wf.reads_live
        terms_subset := fun e' he' => hS.wf.terms_subset e' (Finset.mem_of_mem_erase he')
        card_terms_le := fun e' he' => hS.wf.card_terms_le e' (Finset.mem_of_mem_erase he')
        out_live := hS.wf.out_live
        solvable := fun u => by
          obtain ⟨val, hu, heq⟩ := hS.wf.solvable u
          exact ⟨val, hu, (heqns val).2 heq⟩
        unique := fun val val' hagree heq heq' =>
          hS.wf.unique val val' hagree ((heqns val).1 heq) ((heqns val').1 heq') }
  · exact fun val hval => hS.computes val ⟨(heqns val).1 hval.1, hval.2⟩

/-! ### Affine reparameterisation (AR) -/

/-- Exchange the parameter `x` with the auxiliary variable `Q = c + ∑ j ∈ T, u j` depending on
it: `Q` becomes a parameter, `x` an auxiliary variable, and the parameter map substitutes
`x = Q + c + ∑ j ∈ T \ {x}, u j`. No equation or gate changes. -/
def swap (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) : State n :=
  { S with
    params := insert Q (S.params.erase x)
    aux := insert x (S.aux.erase Q)
    phi := fun val => S.phi (Function.update val x (val Q + c + ∑ j ∈ T.erase x, val j)) }

/-- The hypotheses of the affine reparameterisation. -/
structure SwapOK (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) : Prop where
  mem : x ∈ S.params
  unpaired : ¬ S.Paired x
  aux : Q ∈ S.aux
  affine : S.AffineIn Q c T
  mem_T : x ∈ T

@[simp] theorem swap_params (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) :
    (S.swap x Q c T).params = insert Q (S.params.erase x) := rfl

@[simp] theorem swap_pairs (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) :
    (S.swap x Q c T).pairs = S.pairs := rfl

theorem swap_size (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) :
    (S.swap x Q c T).size = S.size := rfl

theorem swap_children (S : State n) (x Q : ℕ) (c : Bool) (T : Finset ℕ) (z : ℕ) :
    (S.swap x Q c T).children z = S.children z := rfl

/-- The affine reparameterisation preserves validity. -/
theorem Valid.swap {S : State n} (hS : S.Valid f) {x Q : ℕ} {c : Bool} {T : Finset ℕ}
    (h : S.SwapOK x Q c T) : (S.swap x Q c T).Valid f := by
  have hQp : Q ∉ S.params := fun hp => Finset.disjoint_left.1 hS.wf.disjoint_params_aux hp h.aux
  have hxa : x ∉ S.aux := fun ha => Finset.disjoint_left.1 hS.wf.disjoint_params_aux h.mem ha
  have hQx : Q ≠ x := fun he => hQp (he ▸ h.mem)
  have hTx : ∀ j ∈ T.erase x, j ∈ S.params.erase x := fun j hj =>
    Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hj, h.affine.1 (Finset.mem_of_mem_erase hj)⟩
  -- the solved value of `x`
  have hsolve : ∀ val, S.EqnsHold val → val x = val Q + c + ∑ j ∈ T.erase x, val j := by
    intro val hval
    rw [h.affine.2 val hval, ← Finset.add_sum_erase T _ h.mem_T]
    generalize val x = a; generalize ∑ j ∈ T.erase x, val j = b
    cases a <;> cases b <;> cases c <;> rfl
  let σ : (ℕ → Bool) → ℕ → Bool := fun val =>
    Function.update val x (val Q + c + ∑ j ∈ T.erase x, val j)
  have hσ : ∀ val i, i ≠ x → σ val i = val i := fun val i hi => Function.update_of_ne hi _ _
  have hσx : ∀ val, σ val x = val Q + c + ∑ j ∈ T.erase x, val j := fun val =>
    Function.update_self _ _ _
  have hσid : ∀ val, S.EqnsHold val → σ val = val := fun val hval => by
    funext i
    by_cases hi : i = x
    · subst hi; rw [hσx, hsolve val hval]
    · exact hσ val i hi
  have hlive : (S.swap x Q c T).live = S.live := by
    ext i
    simp only [SemiCircuit.live, Finset.mem_union]
    change ((i ∈ insert Q (S.params.erase x)) ∨ i ∈ insert x (S.aux.erase Q)) ∨ i ∈ S.gates ↔ _
    simp only [Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro (((h1 | ⟨-, hp⟩) | (h2 | ⟨-, ha⟩)) | hg)
      · exact Or.inl (Or.inr (h1 ▸ h.aux))
      · exact Or.inl (Or.inl hp)
      · exact Or.inl (Or.inl (h2 ▸ h.mem))
      · exact Or.inl (Or.inr ha)
      · exact Or.inr hg
    · rintro ((hp | ha) | hg)
      · by_cases hix : i = x
        · exact Or.inl (Or.inr (Or.inl hix))
        · exact Or.inl (Or.inl (Or.inr ⟨hix, hp⟩))
      · by_cases hiQ : i = Q
        · exact Or.inl (Or.inl (Or.inl hiQ))
        · exact Or.inl (Or.inr (Or.inr ⟨hiQ, ha⟩))
      · exact Or.inr hg
  have hpa : ∀ i, i ∈ (S.swap x Q c T).params ∪ (S.swap x Q c T).aux ↔ i ∈ S.params ∪ S.aux := by
    intro i
    change i ∈ insert Q (S.params.erase x) ∪ insert x (S.aux.erase Q) ↔ _
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ((h1 | ⟨-, hp⟩) | (h2 | ⟨-, ha⟩))
      · exact Or.inr (h1 ▸ h.aux)
      · exact Or.inl hp
      · exact Or.inl (h2 ▸ h.mem)
      · exact Or.inr ha
    · rintro (hp | ha)
      · by_cases hix : i = x
        · exact Or.inr (Or.inl hix)
        · exact Or.inl (Or.inr ⟨hix, hp⟩)
      · by_cases hiQ : i = Q
        · exact Or.inl (Or.inl hiQ)
        · exact Or.inr (Or.inr ⟨hiQ, ha⟩)
  have hwf : (S.swap x Q c T).WellFormed := by
    refine
      { disjoint_params_aux := ?_
        disjoint_params_gates := ?_
        disjoint_aux_gates := ?_
        reads_lt := hS.wf.reads_lt
        reads_live := fun K hK i hr => hlive ▸ hS.wf.reads_live K hK i hr
        terms_subset := fun e he z hz => (hpa z).2 (hS.wf.terms_subset e he hz)
        card_terms_le := hS.wf.card_terms_le
        out_live := fun i hi => hlive ▸ hS.wf.out_live i hi
        solvable := fun u => ?_
        unique := fun val val' hagree heq heq' a ha => ?_ }
    · rw [Finset.disjoint_left]
      intro i hi hi'
      change i ∈ insert Q (S.params.erase x) at hi
      change i ∈ insert x (S.aux.erase Q) at hi'
      simp only [Finset.mem_insert, Finset.mem_erase] at hi hi'
      rcases hi with rfl | ⟨hix, hp⟩ <;> rcases hi' with rfl | ⟨hiQ, ha⟩
      · exact hQx rfl
      · exact hiQ rfl
      · exact hix rfl
      · exact Finset.disjoint_left.1 hS.wf.disjoint_params_aux hp ha
    · rw [Finset.disjoint_left]
      intro i hi hg
      change i ∈ insert Q (S.params.erase x) at hi
      simp only [Finset.mem_insert, Finset.mem_erase] at hi
      rcases hi with rfl | ⟨-, hp⟩
      · exact Finset.disjoint_left.1 hS.wf.disjoint_aux_gates h.aux hg
      · exact Finset.disjoint_left.1 hS.wf.disjoint_params_gates hp hg
    · rw [Finset.disjoint_left]
      intro i hi hg
      change i ∈ insert x (S.aux.erase Q) at hi
      simp only [Finset.mem_insert, Finset.mem_erase] at hi
      rcases hi with rfl | ⟨-, ha⟩
      · exact Finset.disjoint_left.1 hS.wf.disjoint_params_gates h.mem hg
      · exact Finset.disjoint_left.1 hS.wf.disjoint_aux_gates ha hg
    · obtain ⟨val, hu, heq⟩ := hS.wf.solvable (σ u)
      refine ⟨val, fun j hj => ?_, heq⟩
      change j ∈ insert Q (S.params.erase x) at hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · have h1 := h.affine.2 val heq
        rw [← Finset.add_sum_erase T _ h.mem_T, hu x h.mem, hσx,
          Finset.sum_congr rfl fun i hi => (hu i (h.affine.1 (Finset.mem_of_mem_erase hi))).trans
            (hσ u i (Finset.ne_of_mem_erase hi))] at h1
        rw [h1]
        generalize u j = a; generalize ∑ i ∈ T.erase x, u i = b
        cases a <;> cases b <;> cases c <;> rfl
      · rw [hu j (Finset.mem_of_mem_erase hj), hσ u j (Finset.ne_of_mem_erase hj)]
    · have hparams : ∀ j ∈ S.params, val j = val' j := by
        intro j hj
        by_cases hjx : j = x
        · subst hjx
          rw [hsolve val heq, hsolve val' heq', hagree Q (Finset.mem_insert_self _ _),
            Finset.sum_congr rfl fun i hi => hagree i (Finset.mem_insert_of_mem (hTx i hi))]
        · exact hagree j (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjx, hj⟩))
      change a ∈ insert x (S.aux.erase Q) at ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hparams a h.mem
      · exact hS.wf.unique val val' hparams heq heq' a (Finset.mem_of_mem_erase ha)
  refine hS.of_map σ hwf ?_ hS.pairs_disjoint (fun _ => rfl) ?_ ?_ ?_ ?_ ?_
  · intro pr hpr
    obtain ⟨h1, h2, h12⟩ := hS.pair_mem pr hpr
    have hx1 : pr.1 ≠ x := fun he => h.unpaired ⟨pr, hpr, Or.inl he⟩
    have hx2 : pr.2 ≠ x := fun he => h.unpaired ⟨pr, hpr, Or.inr he⟩
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hx1, h1⟩),
      Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hx2, h2⟩), h12⟩
  · intro val val' hv j hj
    by_cases hjx : j = x
    · subst hjx
      rw [hσx, hσx, hv Q (Finset.mem_insert_self _ _),
        Finset.sum_congr rfl fun i hi => hv i (Finset.mem_insert_of_mem (hTx i hi))]
    · rw [hσ val j hjx, hσ val' j hjx]
      exact hv j (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjx, hj⟩))
  · intro val val' hv j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · have h1 := hv x h.mem
      rw [hσx, hσx, Finset.sum_congr rfl fun i hi => (hσ val i (Finset.ne_of_mem_erase hi)).symm.trans
        ((hv i (Finset.mem_of_mem_erase (hTx i hi))).trans
          (hσ val' i (Finset.ne_of_mem_erase hi)))] at h1
      simpa using h1
    · have := hv j (Finset.mem_of_mem_erase hj)
      rwa [hσ val j (Finset.ne_of_mem_erase hj), hσ val' j (Finset.ne_of_mem_erase hj)] at this
  · intro k τ hτ htame
    refine ⟨fun u => σ (τ u), ?_, fun pr hpr => ?_, fun _ _ _ => rfl⟩
    · refine isAffine_update hτ x fun u v w => ?_
      simp only [congrFun (hτ u v w), Pi.add_apply, Finset.sum_add_distrib]
      generalize τ u Q = a₁; generalize τ v Q = a₂; generalize τ w Q = a₃
      generalize ∑ i ∈ T.erase x, τ u i = b₁; generalize ∑ i ∈ T.erase x, τ v i = b₂
      generalize ∑ i ∈ T.erase x, τ w i = b₃
      cases a₁ <;> cases a₂ <;> cases a₃ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> cases c <;> rfl
    · have hx1 : pr.1 ≠ x := fun he => h.unpaired ⟨pr, hpr, Or.inl he⟩
      have hx2 : pr.2 ≠ x := fun he => h.unpaired ⟨pr, hpr, Or.inr he⟩
      rcases htame pr hpr with ht | ht | ht
      · exact Or.inl fun u v => by dsimp only; rw [hσ _ _ hx1, hσ _ _ hx1]; exact ht u v
      · exact Or.inr (Or.inl fun u v => by dsimp only; rw [hσ _ _ hx2, hσ _ _ hx2]; exact ht u v)
      · exact Or.inr (Or.inr fun u v => by
          dsimp only; rw [hσ _ _ hx1, hσ _ _ hx1, hσ _ _ hx2, hσ _ _ hx2]; exact ht u v)
  · intro val hval
    rw [hσid val hval.1]
    exact hval
  · intro val hval
    rw [hσid val hval.1]
    rfl


/-! ### Quadratic reparameterisation (QR) -/

/-- Along an affine family on which the pair `(x, y)` is tame, the product
`(u x + α) (u y + β)` is affine. -/
theorem isAffine_mul_of_pairTame {k : ℕ} {τ : BitString k → ℕ → Bool} (hτ : IsAffine τ)
    {x y : ℕ} (ht : PairTame τ (x, y)) (α β : Bool) :
    IsAffine fun u => (τ u x + α) * (τ u y + β) := by
  intro u v w
  dsimp only
  have hy := congrFun (hτ u v w) y
  have hx := congrFun (hτ u v w) x
  simp only [Pi.add_apply] at hx hy
  rcases ht with ht | ht | ht
  · have h0 : ∀ u', τ u' x = τ 0 x := fun u' => ht u' 0
    rw [h0 (u + v + w), h0 u, h0 v, h0 w, hy]
    generalize τ 0 x = a; generalize τ u y = b₁; generalize τ v y = b₂; generalize τ w y = b₃
    revert a b₁ b₂ b₃ α β; decide
  · have h0 : ∀ u', τ u' y = τ 0 y := fun u' => ht u' 0
    rw [h0 (u + v + w), h0 u, h0 v, h0 w, hx]
    generalize τ 0 y = a; generalize τ u x = b₁; generalize τ v x = b₂; generalize τ w x = b₃
    revert a b₁ b₂ b₃ α β; decide
  · have h0 : ∀ u', τ u' x = τ u' y + (τ 0 x + τ 0 y) := fun u' => by
      have := ht u' 0
      simp only at this
      rw [← this]
      generalize τ u' x = a; generalize τ u' y = b
      revert a b; decide
    rw [h0 (u + v + w), h0 u, h0 v, h0 w, hy]
    generalize τ 0 x + τ 0 y = a; generalize τ u y = b₁; generalize τ v y = b₂
    generalize τ w y = b₃
    revert a b₁ b₂ b₃ α β; decide

/-- The quadratic reparameterisation: for an AND-type gate `G = (x + α)(y + β) + γ` whose only
child is the XOR-type gate `D = G + z + c`, where `z` is an isolated parameter, substitute
`z = D + G + c` in the parameter map, turn `D` into a parameter (it computes the new parameter
`w` of the source), delete the gates `G` and `D`, and pair `x` with `y`. -/
def quad (S : State n) (x y z G D : ℕ) (α β γ c : Bool) : State n :=
  { S with
    params := insert D (S.params.erase z)
    gates := (S.gates.erase D).erase G
    pairs := insert (x, y) S.pairs
    phi := fun val => S.phi (Function.update val z (val D + ((val x + α) * (val y + β) + γ) + c)) }

/-- The hypotheses of the quadratic reparameterisation. -/
structure QuadOK (S : State n) (x y z G D : ℕ) (α β γ c : Bool) : Prop where
  mem_x : x ∈ S.params
  mem_y : y ∈ S.params
  mem_z : z ∈ S.params
  unpaired_x : ¬ S.Paired x
  unpaired_y : ¬ S.Paired y
  unpaired_z : ¬ S.Paired z
  x_ne_y : x ≠ y
  x_ne_z : x ≠ z
  y_ne_z : y ≠ z
  mem_G : G ∈ S.gates
  mem_D : D ∈ S.gates
  G_ne_D : G ≠ D
  eval_G : ∀ val, (S.gate G).eval val = (val x + α) * (val y + β) + γ
  eval_D : ∀ val, (S.gate D).eval val = val G + val z + c
  children_G : S.children G = {.inl D}
  children_z : S.children z = {.inl D}
  out_G : ¬ S.out.Reads G
  out_z : ¬ S.out.Reads z

@[simp] theorem quad_params (S : State n) (x y z G D : ℕ) (α β γ c : Bool) :
    (S.quad x y z G D α β γ c).params = insert D (S.params.erase z) := rfl

@[simp] theorem quad_pairs (S : State n) (x y z G D : ℕ) (α β γ c : Bool) :
    (S.quad x y z G D α β γ c).pairs = insert (x, y) S.pairs := rfl

theorem quad_size {S : State n} {x y z G D : ℕ} {α β γ c : Bool}
    (h : S.QuadOK x y z G D α β γ c) : (S.quad x y z G D α β γ c).size + 2 = S.size := by
  have h1 := Finset.card_erase_add_one h.mem_D
  have h2 := Finset.card_erase_add_one (Finset.mem_erase.2 ⟨h.G_ne_D, h.mem_G⟩)
  simp only [SemiCircuit.size] at *
  change ((S.gates.erase D).erase G).card + S.eqns.card + 2 = _
  omega

theorem quad_children_subset (S : State n) (x y z G D : ℕ) (α β γ c : Bool) (w : ℕ) :
    (S.quad x y z G D α β γ c).children w ⊆ ((S.children w).erase (.inl D)).erase (.inl G) := by
  intro v hv
  rcases v with K | e
  · simp only [SemiCircuit.inl_mem_children] at hv
    change K ∈ (S.gates.erase D).erase G ∧ _ at hv
    obtain ⟨hK, hr⟩ := hv
    simp only [Finset.mem_erase] at hK ⊢
    exact ⟨fun he => hK.1 (Sum.inl.inj he), fun he => hK.2.1 (Sum.inl.inj he),
      (SemiCircuit.inl_mem_children _).2 ⟨hK.2.2, hr⟩⟩
  · simp only [SemiCircuit.inr_mem_children] at hv
    simp only [Finset.mem_erase, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    exact (SemiCircuit.inr_mem_children _).2 hv

/-- The quadratic reparameterisation preserves validity. -/
theorem Valid.quad {S : State n} (hS : S.Valid f) {x y z G D : ℕ} {α β γ c : Bool}
    (h : S.QuadOK x y z G D α β γ c) : (S.quad x y z G D α β γ c).Valid f := by
  have hgp : ∀ {i}, i ∈ S.gates → i ∉ S.params := fun hg hp =>
    Finset.disjoint_left.1 hS.wf.disjoint_params_gates hp hg
  have hga : ∀ {i}, i ∈ S.gates → i ∉ S.aux := fun hg ha =>
    Finset.disjoint_left.1 hS.wf.disjoint_aux_gates ha hg
  have hzterms : ∀ e ∈ S.eqns, z ∉ (S.eqn e).terms := fun e he hz => by
    have : Sum.inr e ∈ S.children z := (SemiCircuit.inr_mem_children _).2 ⟨he, hz⟩
    rw [h.children_z] at this
    simp at this
  have hGterms : ∀ e ∈ S.eqns, G ∉ (S.eqn e).terms := fun e he =>
    notMem_terms_of_mem_gates hS h.mem_G he
  have hDterms : ∀ e ∈ S.eqns, D ∉ (S.eqn e).terms := fun e he =>
    notMem_terms_of_mem_gates hS h.mem_D he
  have hzreads : ∀ K ∈ S.gates, K ≠ D → ¬ (S.gate K).Reads z := fun K hK hKD hr => by
    have : Sum.inl K ∈ S.children z := (SemiCircuit.inl_mem_children _).2 ⟨hK, hr⟩
    rw [h.children_z] at this
    exact hKD (Sum.inl.inj (Finset.mem_singleton.1 this))
  have hGreads : ∀ K ∈ S.gates, K ≠ D → ¬ (S.gate K).Reads G := fun K hK hKD hr => by
    have : Sum.inl K ∈ S.children G := (SemiCircuit.inl_mem_children _).2 ⟨hK, hr⟩
    rw [h.children_G] at this
    exact hKD (Sum.inl.inj (Finset.mem_singleton.1 this))
  have hzG : z ≠ G := fun he => hgp h.mem_G (he ▸ h.mem_z)
  have hxG : x ≠ G := fun he => hgp h.mem_G (he ▸ h.mem_x)
  have hyG : y ≠ G := fun he => hgp h.mem_G (he ▸ h.mem_y)
  have hDz : D ≠ z := fun he => hgp h.mem_D (he ▸ h.mem_z)
  have hDx : D ≠ x := fun he => hgp h.mem_D (he ▸ h.mem_x)
  have hDy : D ≠ y := fun he => hgp h.mem_D (he ▸ h.mem_y)
  let Gq : (ℕ → Bool) → Bool := fun val => (val x + α) * (val y + β) + γ
  let σ : (ℕ → Bool) → ℕ → Bool := fun val =>
    Function.update (Function.update val z (val D + Gq val + c)) G (Gq val)
  have hσ : ∀ val i, i ≠ z → i ≠ G → σ val i = val i := fun val i hz hG => by
    simp only [σ, Function.update_of_ne hG, Function.update_of_ne hz]
  have hσz : ∀ val, σ val z = val D + Gq val + c := fun val => by
    simp only [σ, Function.update_of_ne hzG, Function.update_self]
  have hσG : ∀ val, σ val G = Gq val := fun val => by simp only [σ, Function.update_self]
  have hGqσ : ∀ val, Gq (σ val) = Gq val := fun val => by
    simp only [Gq, hσ val x h.x_ne_z hxG, hσ val y h.y_ne_z hyG]
  have hlive : ∀ i, i ∈ S.live → i ≠ z → i ≠ G → i ∈ (S.quad x y z G D α β γ c).live := by
    intro i hi hiz hiG
    simp only [SemiCircuit.live, Finset.mem_union] at hi ⊢
    change (i ∈ insert D (S.params.erase z) ∨ i ∈ S.aux) ∨ i ∈ (S.gates.erase D).erase G
    simp only [Finset.mem_insert, Finset.mem_erase]
    by_cases hiD : i = D
    · exact Or.inl (Or.inl (Or.inl hiD))
    · tauto
  have hwf : (S.quad x y z G D α β γ c).WellFormed := by
    refine
      { disjoint_params_aux := ?_
        disjoint_params_gates := ?_
        disjoint_aux_gates := Finset.disjoint_of_subset_right
          ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) hS.wf.disjoint_aux_gates
        reads_lt := fun K hK i hi hr => hS.wf.reads_lt K
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hK)) i
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)) hr
        reads_live := fun K hK i hr => ?_
        terms_subset := fun e he t ht => ?_
        card_terms_le := hS.wf.card_terms_le
        out_live := fun i hi => hlive i (hS.wf.out_live i hi) (fun he => h.out_z (he ▸ hi))
          (fun he => h.out_G (he ▸ hi))
        solvable := fun u => ?_
        unique := fun val val' hagree heq heq' a ha => ?_ }
    · rw [Finset.disjoint_left]
      intro i hi ha
      change i ∈ insert D (S.params.erase z) at hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hga h.mem_D ha
      · exact Finset.disjoint_left.1 hS.wf.disjoint_params_aux (Finset.mem_of_mem_erase hi) ha
    · rw [Finset.disjoint_left]
      intro i hi hg
      change i ∈ insert D (S.params.erase z) at hi
      change i ∈ (S.gates.erase D).erase G at hg
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact Finset.notMem_erase i _ (Finset.mem_of_mem_erase hg)
      · exact hgp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hg))
          (Finset.mem_of_mem_erase hi)
    · change K ∈ (S.gates.erase D).erase G at hK
      have hKD := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hK)
      have hK' := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hK)
      exact hlive i (hS.wf.reads_live K hK' i hr) (fun he => hzreads K hK' hKD (he ▸ hr))
        (fun he => hGreads K hK' hKD (he ▸ hr))
    · have := hS.wf.terms_subset e he ht
      have htz : t ≠ z := fun he' => hzterms e he (he' ▸ ht)
      change t ∈ insert D (S.params.erase z) ∪ S.aux
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase] at this ⊢
      tauto
    · obtain ⟨val, hu, heq⟩ := hS.wf.solvable u
      refine ⟨Function.update val D (u D), fun j hj => ?_, fun e he => ?_⟩
      · change j ∈ insert D (S.params.erase z) at hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact Function.update_self _ _ _
        · rw [Function.update_of_ne (show j ≠ D from fun he =>
            hgp h.mem_D (he ▸ Finset.mem_of_mem_erase hj)),
            hu j (Finset.mem_of_mem_erase hj)]
      · exact (Equation.holds_congr fun i hi =>
          Function.update_of_ne (show i ≠ D from fun he' => hDterms e he (he' ▸ hi)) _ _).2
            (heq e he)
    · have hold : ∀ w : ℕ → Bool, S.EqnsHold w → S.EqnsHold (Function.update w z false) :=
        fun w hw e he => (Equation.holds_congr fun i hi =>
          Function.update_of_ne (show i ≠ z from fun he' => hzterms e he (he' ▸ hi)) _ _).2
            (hw e he)
      have := hS.wf.unique _ _ (fun j hj => by
          by_cases hjz : j = z
          · subst hjz; simp only [Function.update_self]
          · simp only [Function.update_of_ne hjz]
            exact hagree j (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjz, hj⟩)))
        (hold val heq) (hold val' heq') a ha
      have haz : a ≠ z := fun he => Finset.disjoint_left.1 hS.wf.disjoint_params_aux
        (he ▸ h.mem_z) ha
      simpa only [Function.update_of_ne haz] using this
  refine hS.of_map σ hwf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro pr hpr
    rcases Finset.mem_insert.1 hpr with rfl | hpr
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h.x_ne_z, h.mem_x⟩),
        Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h.y_ne_z, h.mem_y⟩), h.x_ne_y⟩
    · obtain ⟨h1, h2, h12⟩ := hS.pair_mem pr hpr
      have hz1 : pr.1 ≠ z := fun he => h.unpaired_z ⟨pr, hpr, Or.inl he⟩
      have hz2 : pr.2 ≠ z := fun he => h.unpaired_z ⟨pr, hpr, Or.inr he⟩
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hz1, h1⟩),
        Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hz2, h2⟩), h12⟩
  · have hnew : ∀ pr ∈ S.pairs, x ≠ pr.1 ∧ x ≠ pr.2 ∧ y ≠ pr.1 ∧ y ≠ pr.2 := fun pr hpr =>
      ⟨fun he => h.unpaired_x ⟨pr, hpr, Or.inl he.symm⟩,
        fun he => h.unpaired_x ⟨pr, hpr, Or.inr he.symm⟩,
        fun he => h.unpaired_y ⟨pr, hpr, Or.inl he.symm⟩,
        fun he => h.unpaired_y ⟨pr, hpr, Or.inr he.symm⟩⟩
    intro pr hpr pr' hpr' hne
    rcases Finset.mem_insert.1 hpr with rfl | hpr <;>
      rcases Finset.mem_insert.1 hpr' with rfl | hpr'
    · exact absurd rfl hne
    · exact hnew pr' hpr'
    · obtain ⟨h1, h2, h3, h4⟩ := hnew pr hpr
      exact ⟨Ne.symm h1, Ne.symm h3, Ne.symm h2, Ne.symm h4⟩
    · exact hS.pairs_disjoint pr hpr pr' hpr' hne
  · intro val
    refine hS.phi_congr _ _ fun j hj => ?_
    have hjG : j ≠ G := fun he => hgp h.mem_G (he ▸ hj)
    simp only [σ, Function.update_of_ne hjG]
    rfl
  · intro val val' hv j hj
    have hjG : j ≠ G := fun he => hgp h.mem_G (he ▸ hj)
    by_cases hjz : j = z
    · subst hjz
      have hD := hv D (Finset.mem_insert_self _ _)
      have hx := hv x (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h.x_ne_z, h.mem_x⟩))
      have hy := hv y (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h.y_ne_z, h.mem_y⟩))
      simp only [hσz, Gq, hD, hx, hy]
    · rw [hσ val j hjz hjG, hσ val' j hjz hjG]
      exact hv j (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjz, hj⟩))
  · intro val val' hv j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · have hz := hv z h.mem_z
      have hx := hv x h.mem_x
      have hy := hv y h.mem_y
      rw [hσ val x h.x_ne_z hxG, hσ val' x h.x_ne_z hxG] at hx
      rw [hσ val y h.y_ne_z hyG, hσ val' y h.y_ne_z hyG] at hy
      rw [hσz, hσz] at hz
      simp only [Gq, hx, hy] at hz
      simpa using hz
    · have := hv j (Finset.mem_of_mem_erase hj)
      have hjG : j ≠ G := fun he => hgp h.mem_G (he ▸ Finset.mem_of_mem_erase hj)
      rwa [hσ val j (Finset.ne_of_mem_erase hj) hjG,
        hσ val' j (Finset.ne_of_mem_erase hj) hjG] at this
  · intro k τ hτ htame
    refine ⟨fun u => Function.update (τ u) z (τ u D + Gq (τ u) + c), ?_, fun pr hpr => ?_,
      fun u j hj => ?_⟩
    · refine isAffine_update hτ z fun u v w => ?_
      have hm := isAffine_mul_of_pairTame hτ (htame (x, y) (Finset.mem_insert_self _ _)) α β u v w
      have hD := congrFun (hτ u v w) D
      simp only [Pi.add_apply] at hm hD
      simp only [Gq, hD, hm]
      generalize τ u D = a₁; generalize τ v D = a₂; generalize τ w D = a₃
      generalize (τ u x + α) * (τ u y + β) = b₁; generalize (τ v x + α) * (τ v y + β) = b₂
      generalize (τ w x + α) * (τ w y + β) = b₃
      cases a₁ <;> cases a₂ <;> cases a₃ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> cases γ <;>
        cases c <;> rfl
    · have hz1 : pr.1 ≠ z := fun he => h.unpaired_z ⟨pr, hpr, Or.inl he⟩
      have hz2 : pr.2 ≠ z := fun he => h.unpaired_z ⟨pr, hpr, Or.inr he⟩
      rcases htame pr (Finset.mem_insert_of_mem hpr) with ht | ht | ht
      · exact Or.inl fun u v => by
          simp only [Function.update_of_ne hz1]; exact ht u v
      · exact Or.inr (Or.inl fun u v => by
          simp only [Function.update_of_ne hz2]; exact ht u v)
      · exact Or.inr (Or.inr fun u v => by
          simp only [Function.update_of_ne hz1, Function.update_of_ne hz2]; exact ht u v)
    · have hjG : j ≠ G := fun he => hgp h.mem_G (he ▸ hj)
      simp only [σ, Function.update_of_ne hjG]
  · intro val hval
    refine ⟨fun e he => (Equation.holds_congr fun i hi => hσ val i
      (fun he' => hzterms e he (he' ▸ hi)) (fun he' => hGterms e he (he' ▸ hi))).2 (hval.1 e he),
      fun K hK => ?_⟩
    by_cases hKG : K = G
    · subst hKG
      rw [hσG, h.eval_G, ← hGqσ]
    · by_cases hKD : K = D
      · subst hKD
        rw [hσ val K hDz hKG, h.eval_D, hσG, hσz]
        generalize val K = a; generalize Gq val = b
        cases a <;> cases b <;> cases c <;> rfl
      · have hK' : K ∈ (S.quad x y z G D α β γ c).gates :=
          Finset.mem_erase.2 ⟨hKG, Finset.mem_erase.2 ⟨hKD, hK⟩⟩
        have hKz : K ≠ z := fun he => hgp hK (he ▸ h.mem_z)
        rw [hσ val K hKz hKG, hval.2 K hK']
        exact Gate.eval_congr fun i hi => (hσ val i (fun he => hzreads K hK hKD (he ▸ hi))
          (fun he => hGreads K hK hKD (he ▸ hi))).symm
  · intro val _
    exact Lit.eval_congr fun i hi => (hσ val i (fun he => h.out_z (he ▸ hi))
      (fun he => h.out_G (he ▸ hi))).symm

/-! ### Moving affine gates into the affine system -/

/-- Move the affine gate `J` into the affine system as the auxiliary variable `J` with the new
equation `e`. -/
def moveAffine (S : State n) (J e : ℕ) : State n :=
  { S with
    gates := S.gates.erase J
    aux := insert J S.aux
    eqns := insert e S.eqns
    eqn := Function.update S.eqn e (affEqn (S.gate J) J) }

/-- The hypotheses of moving a gate into the affine system: `J` is an affine gate reading no
gates and `e` is a fresh equation name. -/
structure MoveOK (S : State n) (J e : ℕ) : Prop where
  mem : J ∈ S.gates
  fresh : e ∉ S.eqns
  affine : IsAffineOp (S.gate J).op
  inputs : ∀ i, (S.gate J).Reads i → i ∉ S.gates

@[simp] theorem moveAffine_params (S : State n) (J e : ℕ) :
    (S.moveAffine J e).params = S.params := rfl

@[simp] theorem moveAffine_pairs (S : State n) (J e : ℕ) :
    (S.moveAffine J e).pairs = S.pairs := rfl

theorem moveAffine_size {S : State n} {J e : ℕ} (h : S.MoveOK J e) :
    (S.moveAffine J e).size = S.size := by
  have h1 := Finset.card_erase_add_one h.mem
  have h2 := Finset.card_insert_of_notMem h.fresh
  simp only [SemiCircuit.size] at *
  change (S.gates.erase J).card + (insert e S.eqns).card = _
  omega

theorem moveAffine_gates_card {S : State n} {J e : ℕ} (h : S.MoveOK J e) :
    (S.moveAffine J e).gates.card + 1 = S.gates.card :=
  Finset.card_erase_add_one h.mem

/-- Moving a gate into the affine system does not increase the degree of any parameter. -/
theorem moveAffine_deg_le {S : State n} (hS : S.Valid f) {J e : ℕ} (h : S.MoveOK J e)
    {z : ℕ} (hz : z ∈ S.params) : (S.moveAffine J e).deg z ≤ S.deg z := by
  have hzJ : z ≠ J := fun he => Finset.disjoint_left.1 hS.wf.disjoint_params_gates hz (he ▸ h.mem)
  have hsub : (S.moveAffine J e).children z ⊆
      ((S.children z).erase (.inl J)).image id ∪
        (if Sum.inl J ∈ S.children z then {.inr e} else ∅) := by
    intro w hw
    rcases w with K | e'
    · simp only [SemiCircuit.inl_mem_children] at hw
      change K ∈ S.gates.erase J ∧ _ at hw
      refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨.inl K, Finset.mem_erase.2
        ⟨fun he => by cases Sum.inl.inj he; exact Finset.notMem_erase _ _ hw.1, ?_⟩, rfl⟩)
      exact (SemiCircuit.inl_mem_children _).2 ⟨Finset.mem_of_mem_erase hw.1, hw.2⟩
    · simp only [SemiCircuit.inr_mem_children] at hw
      change e' ∈ insert e S.eqns ∧ z ∈ (Function.update S.eqn e _ e').terms at hw
      by_cases hee : e' = e
      · subst hee
        rw [Function.update_self] at hw
        rcases mem_affEqn hw.2 with h' | h'
        · exact absurd h' hzJ
        · refine Finset.mem_union_right _ ?_
          rw [ite_eq_left ((SemiCircuit.inl_mem_children _).2 ⟨h.mem, h'⟩)]
          exact Finset.mem_singleton_self _
      · rw [Function.update_of_ne hee] at hw
        refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨.inr e', Finset.mem_erase.2
          ⟨Sum.inr_ne_inl, (SemiCircuit.inr_mem_children _).2
            ⟨Finset.mem_of_mem_insert_of_ne hw.1 hee, hw.2⟩⟩, rfl⟩)
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  rw [Finset.image_id]
  unfold SemiCircuit.deg
  split_ifs with hJ
  · rw [Finset.card_singleton, Finset.card_erase_add_one hJ]
  · rw [Finset.card_empty, add_zero, Finset.erase_eq_of_notMem hJ]

/-- Moving an affine gate reading no gates into the affine system preserves validity. -/
theorem Valid.moveAffine {S : State n} (hS : S.Valid f) {J e : ℕ} (h : S.MoveOK J e) :
    (S.moveAffine J e).Valid f := by
  set g := S.gate J
  have hJp : J ∉ S.params := fun hp => Finset.disjoint_left.1 hS.wf.disjoint_params_gates hp h.mem
  have hJa : J ∉ S.aux := fun ha => Finset.disjoint_left.1 hS.wf.disjoint_aux_gates ha h.mem
  have hgJ : ¬ g.Reads J := fun hr => h.inputs J hr h.mem
  have hgpa : ∀ i, g.Reads i → i ∈ S.params ∪ S.aux := fun i hi => by
    have := hS.wf.reads_live J h.mem i hi
    simp only [SemiCircuit.live, Finset.mem_union] at this
    rcases this with hpa | hg
    · exact Finset.mem_union.2 hpa
    · exact absurd hg (h.inputs i hi)
  have heqn : ∀ e' ∈ S.eqns, (S.moveAffine J e).eqn e' = S.eqn e' := fun e' he' =>
    Function.update_of_ne (show e' ≠ e from fun he => h.fresh (he ▸ he')) _ _
  have heqns : ∀ val, (S.moveAffine J e).EqnsHold val ↔
      S.EqnsHold val ∧ (affEqn g J).Holds val := fun val => by
    constructor
    · intro hv
      refine ⟨fun e' he' => ?_, ?_⟩
      · rw [← heqn e' he']; exact hv e' (Finset.mem_insert_of_mem he')
      · have := hv e (Finset.mem_insert_self _ _)
        change (Function.update S.eqn e _ e).Holds val at this
        rwa [Function.update_self] at this
    · rintro ⟨hv, hJv⟩ e' he'
      rcases Finset.mem_insert.1 he' with rfl | he'
      · change (Function.update S.eqn e' _ e').Holds val
        rwa [Function.update_self]
      · rw [heqn e' he']; exact hv e' he'
  have hlive : (S.moveAffine J e).live = S.live := by
    ext i
    simp only [SemiCircuit.live, Finset.mem_union]
    change (i ∈ S.params ∨ i ∈ insert J S.aux) ∨ i ∈ S.gates.erase J ↔ _
    simp only [Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ((hp | (rfl | ha)) | ⟨-, hg⟩)
      · exact Or.inl (Or.inl hp)
      · exact Or.inr h.mem
      · exact Or.inl (Or.inr ha)
      · exact Or.inr hg
    · rintro ((hp | ha) | hg)
      · exact Or.inl (Or.inl hp)
      · exact Or.inl (Or.inr (Or.inr ha))
      · by_cases hiJ : i = J
        · exact Or.inl (Or.inr (Or.inl hiJ))
        · exact Or.inr ⟨hiJ, hg⟩
  refine hS.of_phi rfl rfl rfl ?_ ?_
  · refine
      { disjoint_params_aux := ?_
        disjoint_params_gates := Finset.disjoint_of_subset_right (Finset.erase_subset _ _)
          hS.wf.disjoint_params_gates
        disjoint_aux_gates := ?_
        reads_lt := fun K hK i hi hr => hS.wf.reads_lt K (Finset.mem_of_mem_erase hK) i
          (Finset.mem_of_mem_erase hi) hr
        reads_live := fun K hK i hr => hlive ▸ hS.wf.reads_live K (Finset.mem_of_mem_erase hK) i hr
        terms_subset := fun e' he' t ht => ?_
        card_terms_le := fun e' he' => ?_
        out_live := fun i hi => hlive ▸ hS.wf.out_live i hi
        solvable := fun u => ?_
        unique := fun val val' hagree heq heq' a ha => ?_ }
    · rw [Finset.disjoint_left]
      intro i hp ha
      change i ∈ insert J S.aux at ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hJp hp
      · exact Finset.disjoint_left.1 hS.wf.disjoint_params_aux hp ha
    · rw [Finset.disjoint_left]
      intro i ha hg
      change i ∈ insert J S.aux at ha
      change i ∈ S.gates.erase J at hg
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact Finset.notMem_erase i _ hg
      · exact Finset.disjoint_left.1 hS.wf.disjoint_aux_gates ha (Finset.mem_of_mem_erase hg)
    · change t ∈ S.params ∪ insert J S.aux
      rcases Finset.mem_insert.1 he' with rfl | he'
      · change t ∈ (Function.update S.eqn e' _ e').terms at ht
        rw [Function.update_self] at ht
        rcases mem_affEqn ht with rfl | ht
        · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
        · rcases Finset.mem_union.1 (hgpa t ht) with hp | ha
          · exact Finset.mem_union_left _ hp
          · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem ha)
      · rw [heqn e' he'] at ht
        rcases Finset.mem_union.1 (hS.wf.terms_subset e' he' ht) with hp | ha
        · exact Finset.mem_union_left _ hp
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem ha)
    · rcases Finset.mem_insert.1 he' with rfl | he'
      · change (Function.update S.eqn e' _ e').terms.card ≤ 3
        rw [Function.update_self]
        exact card_affEqn_le _ _
      · rw [heqn e' he']; exact hS.wf.card_terms_le e' he'
    · obtain ⟨val, hu, heq⟩ := hS.wf.solvable u
      have hw : ∀ i, i ≠ J → Function.update val J (g.eval val) i = val i := fun i hi =>
        Function.update_of_ne hi _ _
      refine ⟨Function.update val J (g.eval val), fun j hj => (hw j fun he => hJp (he ▸ hj)).trans
        (hu j hj), (heqns _).2 ⟨fun e' he' => (Equation.holds_congr fun i hi => hw i fun he =>
          notMem_terms_of_mem_gates hS h.mem he' (he ▸ hi)).2 (heq e' he'), ?_⟩⟩
      rw [affEqn_holds h.affine, Function.update_self]
      exact Gate.eval_congr fun i hi => (hw i fun he => hgJ (he ▸ hi)).symm
    · obtain ⟨heq, hJv⟩ := (heqns val).1 heq
      obtain ⟨heq', hJv'⟩ := (heqns val').1 heq'
      have hagree' := hS.wf.unique val val' hagree heq heq'
      change a ∈ insert J S.aux at ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · rw [(affEqn_holds h.affine _ _).1 hJv, (affEqn_holds h.affine _ _).1 hJv']
        refine Gate.eval_congr fun i hi => ?_
        rcases Finset.mem_union.1 (hgpa i hi) with hp | ha
        · exact hagree i hp
        · exact hagree' i ha
      · exact hagree' a ha
  · intro val hval
    obtain ⟨heq, hJv⟩ := (heqns val).1 hval.1
    refine hS.computes val ⟨heq, fun K hK => ?_⟩
    by_cases hKJ : K = J
    · subst hKJ; exact (affEqn_holds h.affine _ _).1 hJv
    · exact hval.2 K (Finset.mem_erase.2 ⟨hKJ, hK⟩)

/-! ### Rewiring a gate -/

/-- Replace the gate `J` by the gate `g`. -/
def rewire (S : State n) (J : ℕ) (g : Gate) : State n :=
  { S with gate := Function.update S.gate J g }

/-- The hypotheses of rewiring: `g` reads only parameters and computes the value of `J`
whenever all other gates take their values. -/
structure RewireOK (S : State n) (J : ℕ) (g : Gate) : Prop where
  mem : J ∈ S.gates
  reads : ∀ i, g.Reads i → i ∈ S.params
  value : ∀ val, (∀ K ∈ S.gates, K ≠ J → val K = (S.gate K).eval val) →
    g.eval val = (S.gate J).eval val

@[simp] theorem rewire_params (S : State n) (J : ℕ) (g : Gate) :
    (S.rewire J g).params = S.params := rfl

@[simp] theorem rewire_pairs (S : State n) (J : ℕ) (g : Gate) :
    (S.rewire J g).pairs = S.pairs := rfl

theorem rewire_size (S : State n) (J : ℕ) (g : Gate) : (S.rewire J g).size = S.size := rfl

theorem rewire_gates (S : State n) (J : ℕ) (g : Gate) : (S.rewire J g).gates = S.gates := rfl

theorem inl_mem_children_rewire (S : State n) (J : ℕ) (g : Gate) (z K : ℕ) :
    Sum.inl K ∈ (S.rewire J g).children z ↔
      K ∈ S.gates ∧ (if K = J then g.Reads z else (S.gate K).Reads z) := by
  rw [SemiCircuit.inl_mem_children]
  change K ∈ S.gates ∧ (Function.update S.gate J g K).Reads z ↔ _
  by_cases hKJ : K = J
  · subst hKJ; rw [Function.update_self, ite_eq_left rfl]
  · rw [Function.update_of_ne hKJ, ite_eq_right hKJ]

theorem inr_mem_children_rewire (S : State n) (J : ℕ) (g : Gate) (z e : ℕ) :
    Sum.inr e ∈ (S.rewire J g).children z ↔ Sum.inr e ∈ S.children z := by
  simp only [SemiCircuit.inr_mem_children]
  rfl

/-- Rewiring a gate preserves validity. -/
theorem Valid.rewire {S : State n} (hS : S.Valid f) {J : ℕ} {g : Gate} (h : S.RewireOK J g) :
    (S.rewire J g).Valid f := by
  have hgate : ∀ K, K ≠ J → (S.rewire J g).gate K = S.gate K := fun K hK =>
    Function.update_of_ne hK _ _
  have hgateJ : (S.rewire J g).gate J = g := Function.update_self _ _ _
  refine hS.of_phi rfl rfl rfl ?_ ?_
  · refine
      { disjoint_params_aux := hS.wf.disjoint_params_aux
        disjoint_params_gates := hS.wf.disjoint_params_gates
        disjoint_aux_gates := hS.wf.disjoint_aux_gates
        reads_lt := fun K hK i hi hr => ?_
        reads_live := fun K hK i hr => ?_
        terms_subset := hS.wf.terms_subset
        card_terms_le := hS.wf.card_terms_le
        out_live := hS.wf.out_live
        solvable := hS.wf.solvable
        unique := hS.wf.unique }
    · by_cases hKJ : K = J
      · subst hKJ
        rw [hgateJ] at hr
        exact absurd hi fun hg => Finset.disjoint_left.1 hS.wf.disjoint_params_gates
          (h.reads i hr) hg
      · rw [hgate K hKJ] at hr; exact hS.wf.reads_lt K hK i hi hr
    · by_cases hKJ : K = J
      · subst hKJ
        rw [hgateJ] at hr
        simp only [SemiCircuit.live, Finset.mem_union]
        exact Or.inl (Or.inl (h.reads i hr))
      · rw [hgate K hKJ] at hr; exact hS.wf.reads_live K hK i hr
  · intro val hval
    have hothers : ∀ K ∈ S.gates, K ≠ J → val K = (S.gate K).eval val := fun K hK hKJ => by
      rw [← hgate K hKJ]; exact hval.2 K hK
    refine hS.computes val ⟨hval.1, fun K hK => ?_⟩
    by_cases hKJ : K = J
    · subst hKJ
      rw [← h.value val hothers, ← hgateJ]
      exact hval.2 K hK
    · exact hothers K hK hKJ

end State

end Cslib.Circuits.Boolean.AffineDisperser
