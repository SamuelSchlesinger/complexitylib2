/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.B2.State

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

* `Cslib.Circuits.Boolean.B2.State.Valid.of_map`: transporting validity.
* `Cslib.Circuits.Boolean.B2.State.Valid.restrict`, `Valid.deleteGate`, `Valid.deleteEqn`,
  `Valid.dropEqn`, `Valid.dropTrivialEqn`, `Valid.swap`, `Valid.quad`, `Valid.moveAffine`,
  `Valid.rewire`: the operations preserve validity.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.B2

open Finset Cslib.BitString

namespace SemiCircuit

variable {C : SemiCircuit}

/-- Changing the value of a name that no gate or equation reads and that is not a gate keeps
consistency. -/
theorem consistent_update_iff {x : ℕ} (hxg : x ∉ C.gates)
    (hgate : ∀ J ∈ C.gates, ¬ (C.gate J).Reads x) (heqn : ∀ e ∈ C.eqns, x ∉ (C.eqn e).terms)
    (val : ℕ → Bool) (b : Bool) : C.Consistent (Function.update val x b) ↔ C.Consistent val := by
  have hupd : ∀ i, i ≠ x → Function.update val x b i = val i := fun i hi =>
    Function.update_of_ne hi _ _
  refine and_congr (forall₂_congr fun e he => Equation.holds_congr fun i hi =>
    hupd i fun h => heqn e he (h ▸ hi)) (forall₂_congr fun J hJ => ?_)
  rw [hupd J fun h => hxg (h ▸ hJ), Gate.eval_congr fun i hi => hupd i fun h => hgate J hJ (h ▸ hi)]

end SemiCircuit

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

end State

end Cslib.Circuits.Boolean.B2
