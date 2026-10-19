/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Complexity.Classes.PP
public import Complexity.Computability.Complexity.Classes.Space.Savitch
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.TapeLemmas
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Inclusions between complexity classes

The inclusions between the standard classes that papers cite in their preliminaries
[Arora and Barak, Chapters 2, 4 and 7][AroraBarak09], [Sipser, Chapters 8 and 10][Sipser2013]:

* `P ⊆ BPP` (`Cslib.Complexity.P_subset_BPP`): a decider ignores its random string.
* `NP ⊆ PP` (`Cslib.Complexity.NP_subset_PP`): accept on half of the random strings outright, and
  on the other half run the verifier, so the majority accepts exactly when some certificate does.
* `PP` is closed under complement (`Cslib.Complexity.compl_mem_PP`): with two more random bits,
  accept on a quarter of the random strings and one more, and on half of them reject what the
  verifier accepts; the majority accepts exactly when the verifier accepts at most half of its
  random strings.
* `NP ⊆ PSPACE` (`Cslib.Complexity.NP_subset_PSPACE`): a nondeterministic machine visits at most
  one new cell per step on each work tape (`Turing.MultiTapeNTM.RunsInTime.runsInSpace`), so `NP`
  is within `NPSPACE`, which is `PSPACE` by Savitch's theorem
  (`Cslib.Complexity.NPSPACE_subset_PSPACE`).
* `PSPACE ⊆ EXP` (`Cslib.Complexity.PSPACE_subset_EXP`): Savitch's decider runs within time
  exponential in a polynomial (`Cslib.Reachability.computableTidilyInO_savitch`).

With `Cslib.Complexity.P_subset_NP`, these give the chain `P ⊆ NP ⊆ PSPACE ⊆ EXP`. The other
inclusions of the chains are elsewhere: `P ⊆ PSPACE` (`Cslib.Complexity.P_subset_PSPACE`),
`NPSPACE = PSPACE` (`Cslib.Complexity.NPSPACE_eq_PSPACE`), `RP ⊆ NP`
(`Cslib.Complexity.RP_subset_NP`), `BPP ⊆ PP` (`Cslib.Complexity.BPP_subset_PP`), `BPP ⊆ Σ₂ ∩ Π₂`
(`Cslib.Complexity.BPP_subset_SigmaP_two_inter_PiP_two`), `L ⊆ NL ⊆ P`
(`Cslib.Complexity.L_subset_NL`, `Cslib.Complexity.NL_subset_P`), `P ⊆ EXP` and its strictness
(`Cslib.Complexity.P_subset_EXP`, `Cslib.Complexity.P_ssubset_EXP`).

## Main results

* `Cslib.Complexity.P_subset_BPP`, `Cslib.Complexity.NP_subset_PP`.
* `Cslib.Complexity.compl_mem_PP`, `Cslib.Complexity.PP_eq_preimage_compl_PP`.
* `Turing.MultiTapeNTM.RunsInTime.runsInSpace`: space is at most time.
* `Cslib.Complexity.NP_subset_NPSPACE`, `Cslib.Complexity.NP_subset_PSPACE`.
* `Cslib.Complexity.PSPACE_subset_EXP`, `Cslib.Complexity.NP_subset_EXP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [J. Gill, *Computational complexity of probabilistic Turing machines*][Gill1977]
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol} {ntm : MultiTapeNTM k Symbol State}

/-- **Space is at most time.** Under a time bound `t`, every computation path visits at most
`k * (t + 1)` work-tape cells: within `t` steps each head visits at most `t + 1` cells, and from
step `t` on the path stays at a halted configuration. -/
theorem RunsInTime.runsInSpace {t : ℕ} (h : ntm.RunsInTime input t) :
    ntm.RunsInSpace input (k * (t + 1)) := by
  intro p
  rcases le_or_gt p.time t with hle | hlt
  · exact (RunPath.space_le_mul_time_add_one p.toRunPath).trans
      (Nat.mul_le_mul_left k (Nat.add_le_add_right hle 1))
  -- the first `t` steps have halted, and the path stays there
  have ht : t < p.length + 1 := by unfold ComputationPath.time RunPath.time at hlt; omega
  let q : ntm.ComputationPath input :=
    ⟨p.toRunPath.take ⟨t, ht⟩, by rw [RelSeries.head_take]; exact p.head_eq⟩
  have hq : q.time = t := rfl
  have hhalt : (p.toRunPath ⟨t, ht⟩).Halted := by
    have hlast : q.last = p.toRunPath ⟨t, ht⟩ := RelSeries.last_take _ _
    exact hlast ▸ h q hq.ge
  have hsub : ∀ c ∈ p.toRunPath, c ∈ q.toRunPath := by
    rintro _ ⟨j, rfl⟩
    rcases le_or_gt j.val t with hj | hj
    · exact ⟨⟨j, Nat.lt_succ_of_le hj⟩, rfl⟩
    · refine ⟨Fin.last _, ?_⟩
      have hj' := RunPath.last_eq_of_halted (p.toRunPath.take j) ⟨t, Nat.lt_succ_of_lt hj⟩ hhalt
      rw [RelSeries.last_take] at hj'
      change p.toRunPath ⟨t, ht⟩ = p.toRunPath j
      exact hj'.symm
  exact (RunPath.space_le_of_subset hsub).trans
    ((RunPath.space_le_mul_time_add_one q.toRunPath).trans_eq (by rw [← hq]; rfl))

end Turing.MultiTapeNTM

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Filter

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-! ### Probabilistic classes -/

/-- **`P ⊆ BPP`**: a decider is a bounded-error verifier ignoring its random string, of length
`0`. -/
theorem P_subset_BPP : P enc ⊆ BPP enc := by
  rintro A ⟨f, hf, hA⟩
  refine ⟨0, fun x => f x.1, hf.comp (.fst enc encBits), fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · simp [(hA a).mp ha]
  · have : f a = false := by simpa [hA a] using ha
    simp [this]

/-- Counting the words of length `n + 1` by their first bit. -/
private theorem card_filter_ofFn_succ (n : ℕ) (P : List Bool → Prop) [DecidablePred P] :
    (Finset.univ.filter fun r : Fin (n + 1) → Bool => P (List.ofFn r)).card =
      (Finset.univ.filter fun w : Fin n → Bool => P (false :: List.ofFn w)).card +
        (Finset.univ.filter fun w : Fin n → Bool => P (true :: List.ofFn w)).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Bool).sum_comp, Fintype.sum_prod_type,
    Fintype.sum_bool, add_comm]
  simp [List.ofFn_succ, Fin.consEquiv]

/-- **`NP ⊆ PP`** [Gill][Gill1977]: on random strings `b :: w`, accept when `b = false` and run
the verifier on `w` when `b = true`. The majority accepts exactly when the verifier accepts some
certificate. -/
theorem NP_subset_PP : NP enc ⊆ PP enc := by
  rintro A ⟨p, V, hV, hA⟩
  let V' (x : α × List Bool) : Bool := !(x.2.headD false) || V (x.1, x.2.tail)
  have hV' : ComputableTidilyInPolyTime V' (encPair enc encBits) encBool :=
    ComputableTidilyInPolyTime.bool_or.comp
      ((ComputableTidilyInPolyTime.bool_not.comp
        ((ComputableTidilyInPolyTime.headD (encA := encBool) false).comp (.snd _ _))).prod
        (hV.comp ((ComputableTidilyInPolyTime.fst _ _).prod
          (ComputableTidilyInPolyTime.bitsTail.comp (.snd _ _)))))
  refine ⟨p + 1, V', hV', fun a => ?_⟩
  have hcount (m : ℕ) : acceptCount V' a (m + 1) = 2 ^ m + acceptCount V a m := by
    rw [acceptCount, card_filter_ofFn_succ m fun l => V' (a, l) = true]
    simp [V', acceptCount]
  have heval : (p + 1).eval (enc a).length = p.eval (enc a).length + 1 := by simp
  rw [heval, hcount, hA a, ← acceptCount_pos_iff, pow_succ]
  omega

/-- **`PP` is closed under complement** [Gill][Gill1977]. On random strings `b₁ :: b₂ :: w`,
accept when `b₁ = b₂ = false` and on `b₁ = false, b₂ = true` only for `w` all zeros, and reject
what the verifier accepts on `w` when `b₁ = true`. With `acc` accepted and `rej` rejected strings
of length `m`, this accepts `2 ^ m + 1 + 2 * rej` of the `4 * 2 ^ m` strings, more than half
exactly when `2 * acc ≤ 2 ^ m`. -/
theorem compl_mem_PP (hA : A ∈ PP enc) : Aᶜ ∈ PP enc := by
  obtain ⟨p, V, hV, hA⟩ := hA
  let V' (x : α × List Bool) : Bool :=
    if x.2.headD false then !V (x.1, x.2.tail.tail)
    else !(x.2.tail.headD false) || !(x.2.tail.tail.any fun b => b)
  have hV' : ComputableTidilyInPolyTime V' (encPair enc encBits) encBool := by
    have hw : ComputableTidilyInPolyTime (fun x : α × List Bool => x.2.tail.tail)
        (encPair enc encBits) encBits :=
      ComputableTidilyInPolyTime.bitsTail.comp
        (ComputableTidilyInPolyTime.bitsTail.comp (.snd _ _))
    exact ComputableTidilyInPolyTime.cond
      ((ComputableTidilyInPolyTime.headD (encA := encBool) false).comp (.snd _ _))
      (ComputableTidilyInPolyTime.bool_not.comp
        (hV.comp ((ComputableTidilyInPolyTime.fst _ _).prod hw)))
      (ComputableTidilyInPolyTime.bool_or.comp
        ((ComputableTidilyInPolyTime.bool_not.comp
          ((ComputableTidilyInPolyTime.headD (encA := encBool) false).comp
            (ComputableTidilyInPolyTime.bitsTail.comp (.snd _ _)))).prod
          (ComputableTidilyInPolyTime.bool_not.comp
            (ComputableTidilyInPolyTime.bitsAnyWithInput (test := fun _ b => b) hw
              (.snd _ _)))))
  refine ⟨p + 2, V', hV', fun a => ?_⟩
  -- exactly one word of length `m` is all zeros
  have hzero (m : ℕ) : (Finset.univ.filter fun w : Fin m → Bool =>
      ((List.ofFn w).any fun b => b) = false).card = 1 := by
    refine Finset.card_eq_one.mpr ⟨fun _ => false, Finset.ext fun w => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.any_eq_false, List.mem_ofFn,
      forall_exists_index, forall_apply_eq_imp_iff, Finset.mem_singleton, Bool.not_eq_true]
    exact ⟨fun h => funext h, fun h i => by rw [h]⟩
  have hcount (m : ℕ) : acceptCount V' a (m + 1 + 1) = 2 ^ m + 1 +
      2 * (Finset.univ.filter fun w : Fin m → Bool => V (a, List.ofFn w) = false).card := by
    rw [acceptCount, card_filter_ofFn_succ (m + 1) fun l => V' (a, l) = true,
      card_filter_ofFn_succ m fun l => V' (a, false :: l) = true,
      card_filter_ofFn_succ m fun l => V' (a, true :: l) = true]
    simp only [V', List.headD_cons, List.tail_cons, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      Bool.true_or, Bool.not_true, Bool.false_or, Finset.filter_true, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Bool.not_eq_true', hzero]
    ring
  have heval : (p + 2).eval (enc a).length = p.eval (enc a).length + 1 + 1 := by simp
  have hsum := acceptCount_add_card_filter_eq_false (V := V) (a := a) (n := p.eval (enc a).length)
  rw [heval, hcount, Set.mem_compl_iff, hA a, pow_succ, pow_succ]
  omega

/-- `PP` equals its preimage under complement. -/
theorem PP_eq_preimage_compl_PP (enc : α ↪ List Bool) : PP enc = compl ⁻¹' PP enc := by
  ext A
  refine ⟨compl_mem_PP, fun hA => ?_⟩
  simpa using compl_mem_PP hA

end Cslib.Complexity
