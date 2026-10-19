/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AffineDisperser.MinimalAnd

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

* `Cslib.Circuits.Boolean.AffineDisperser.State.auxIn`, `Cslib.Circuits.Boolean.AffineDisperser.State.childIn`: the
  measures of the restructuring.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.exists_step`: Lemma 4.2.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset Cslib.BitString SemiCircuit

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Composing preparatory operations with steps -/

theorem Step.of_prep {S S₁ S' : State n} (h : Step f S₁ S') (hms : S₁.m + S₁.s = S.m + S.s)
    (ha : S₁.a = S.a) (hW : S₁.W ≤ S.W) : Step f S S' := by
  obtain ⟨hS', hlt, ha₁, ha₂, hW'⟩ := h
  exact ⟨hS', by omega, by omega, by omega, by rw [← ha]; omega⟩

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

end Cslib.Circuits.Boolean.AffineDisperser
