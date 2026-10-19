/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Complexity.Classes.PH
public import Complexity.Computability.Complexity.Classes.PP
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Complexity.Classes.Space.Savitch
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
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

/-! ### Space -/

/-- **`NP ⊆ NPSPACE`**: a nondeterministic machine deciding a problem in polynomial time visits at
most polynomially many work-tape cells. -/
theorem NP_subset_NPSPACE : NP enc ⊆ NPSPACE enc := by
  intro A hA
  obtain ⟨t, ht, k, State, hfinite, ntm, hdec⟩ := decidableInPolyTime_of_mem_NP hA
  exact ⟨k, State, hfinite, ntm, fun a => k * (t a + 1), (PolyBounded.const k).mul
    (ht.add (.const 1)), fun a => ⟨(hdec a).1.runsInSpace, (hdec a).2⟩⟩

/-- **`NP ⊆ PSPACE`** [Arora and Barak, Section 4.2][AroraBarak09]: `NP ⊆ NPSPACE`, and
`NPSPACE = PSPACE` by Savitch's theorem. -/
theorem NP_subset_PSPACE : NP enc ⊆ PSPACE enc :=
  NP_subset_NPSPACE.trans NPSPACE_subset_PSPACE

/-- A polynomial plus `2` to a polynomial times a polynomial is eventually below `2 ^ n ^ K`. -/
private theorem exists_eventually_le_two_pow_pow {P Q R : ℕ → ℕ} (hP : PolynomiallyBounded P)
    (hQ : PolynomiallyBounded Q) (hR : PolynomiallyBounded R) :
    ∃ K, ∀ᶠ n in atTop, P n + 2 ^ Q n * R n ≤ 2 ^ n ^ K := by
  obtain ⟨K, hK⟩ : PolynomiallyBounded fun n => Q n + n + 1 := by fun_prop
  refine ⟨K, ?_⟩
  filter_upwards [hP.eventually_lt_two_pow, hR.eventually_lt_two_pow, hK] with n h₁ h₂ h₃
  have h₄ : 1 ≤ 2 ^ Q n := Nat.one_le_two_pow
  calc P n + 2 ^ Q n * R n ≤ 2 ^ n * 2 ^ Q n + 2 ^ Q n * 2 ^ n :=
        Nat.add_le_add (h₁.le.trans (Nat.le_mul_of_pos_right _ h₄))
          (Nat.mul_le_mul_left _ h₂.le)
    _ = 2 ^ (Q n + n + 1) := by ring
    _ ≤ 2 ^ n ^ K := Nat.pow_le_pow_right (by norm_num) h₃

/-- **`PSPACE ⊆ EXP`** [Arora and Barak, Theorem 4.2][AroraBarak09],
[Sipser, Section 8.2][Sipser2013]: a problem in `PSPACE` is decided by a nondeterministic machine
within polynomial space (`Cslib.Complexity.PSPACE_subset_NPSPACE`), and Savitch's decider for it
runs within time exponential in a polynomial: its codes have polynomial width `w`, and it runs
`2 ^ ((w + 2) * (w + 1))` rounds of polynomial cost
(`Cslib.Reachability.computableTidilyInO_savitch`). -/
theorem PSPACE_subset_EXP : PSPACE enc ⊆ EXP enc := by
  intro A hA
  obtain ⟨k, State, hfinite, ntm, s, hs, hAn⟩ := PSPACE_subset_NPSPACE hA
  obtain ⟨c, d, hcd⟩ := hs.exists_le
  -- the inputs and the edge test of Savitch's decider are polynomial-time
  have hwidth := MultiTapeNTM.computableTidilyInPolyTime_codeWidth (ntm := ntm) (enc := enc) c d
  have hcodes : ComputableTidilyInPolyTime
      (fun a => 2 * ntm.codeWidth c d (enc a) + 2) enc encUnary :=
    ComputableTidilyInPolyTime.unary_add.comp ((ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.const 2).prod hwidth)).prod (ComputableTidilyInPolyTime.const 2))
  have hedge : ComputableTidilyInPolyTime
      (fun q : Unit × List Bool × List Bool => (fun _ => ntm.codeEdge) q.1 q.2.1 q.2.2)
      (encPair (encFinite Unit) (encPair encBits encBits)) encBool :=
    ntm.computableTidilyInPolyTime_codeEdge ((ComputableTidilyInPolyTime.fst _ _).comp (.snd _ _))
      ((ComputableTidilyInPolyTime.snd _ _).comp (.snd _ _))
  have hin : ComputableTidilyInPolyTime
      (fun a => ((), 2 * ntm.codeWidth c d (enc a) + 2, 2 * ntm.codeWidth c d (enc a) + 2,
        MultiTapeNTM.viewCode (ntm.codeWidth c d (enc a)) (ntm.initView (enc a)),
        MultiTapeNTM.acceptCode (ntm.codeWidth c d (enc a)))) enc
      (Cslib.Reachability.encArgs (encFinite Unit)) :=
    (ComputableTidilyInPolyTime.const ()).prod (hcodes.prod (hcodes.prod
      ((MultiTapeNTM.computableTidilyInPolyTime_viewCode_initView hwidth (.encode enc)).prod
        (MultiTapeNTM.computableTidilyInPolyTime_acceptCode hwidth))))
  obtain ⟨te, se, hte, -, he⟩ := hedge
  obtain ⟨ti, si, hti, -, hi⟩ := hin
  have hedgeO : ComputableTidilyInO _ _ encBool te se :=
    ⟨1, he.mono (fun _ => by omega) fun _ => by omega, fun _ => by simp⟩
  have hinO : ComputableTidilyInO _ enc (Cslib.Reachability.encArgs (encFinite Unit)) ti
      fun a => ti a + si a :=
    ⟨1, hi.mono (fun _ => by omega) fun _ => by dsimp only; omega, fun a => by
      have := hi.length_le a
      dsimp only
      omega⟩
  have h := Cslib.Reachability.computableTidilyInO_savitch (edge := fun _ => ntm.codeEdge)
    (par := fun _ => ()) hedgeO hinO
    (fun _ => MultiTapeNTM.length_viewCode (Nat.le_add_right _ _)) fun _ => List.length_replicate ..
  -- polynomial bounds on the width, the inputs and the edge test
  obtain ⟨cW, dW, hW⟩ := hwidth.polyBounded_length.exists_le
  obtain ⟨cT, dT, hT⟩ := hti.exists_le
  obtain ⟨cE, dE, hE⟩ := hte.exists_le
  set L := (encFinite Unit ()).length
  have hedgeMax (w : ℕ) : Cslib.Reachability.edgeMax te () w ≤ cE * (2 * L + 3 * w + 3) ^ dE :=
    listMax_le fun u hu => listMax_le fun v hv => by
      refine (hE _).trans (Nat.mul_le_mul_left cE (Nat.pow_le_pow_left ?_ dE))
      simp only [length_encPair, encBits_apply, Cslib.BitString.mem_enumList.mp hu,
        Cslib.BitString.mem_enumList.mp hv]
      omega
  set B : ℕ → ℕ := fun n => 2 * (cW * (n + 1) ^ dW) + 2
  obtain ⟨K, hK⟩ := exists_eventually_le_two_pow_pow (P := fun n => cT * (n + 1) ^ dT)
    (Q := fun n => (B n + 2) * (B n + 1))
    (R := fun n => ((B n + 1) * (B n + B n + 1) + L + 1) ^ 2 + cE * (2 * L + 3 * B n + 3) ^ dE)
    (by fun_prop) (by simp only [B]; fun_prop) (by simp only [B]; fun_prop)
  have hmem := setOf_mem_DTIME_of_computableTidilyInO h
    (t := fun n => cT * (n + 1) ^ dT + 2 ^ ((B n + 2) * (B n + 1)) *
      (((B n + 1) * (B n + B n + 1) + L + 1) ^ 2 + cE * (2 * L + 3 * B n + 3) ^ dE))
    fun a => by
      have hw : 2 * ntm.codeWidth c d (enc a) + 2 ≤ B (enc a).length := by
        have := hW a
        simp only [encUnary_apply, List.length_replicate] at this
        simp only [B]
        omega
      gcongr
      · exact hT a
      · exact (hedgeMax _).trans (Nat.mul_le_mul_left cE (Nat.pow_le_pow_left (by omega) dE))
  have hA' : A = {a | ntm.savitchDecide c d (enc a) = true} := Set.ext fun a =>
    (hAn a).2.trans (MultiTapeNTM.savitchDecide_eq_true_iff (hAn a).1 (hcd a)).symm
  rw [hA']
  exact mem_EXP_iff.mpr ⟨K, DTIME_mono_of_eventually_le hK hmem⟩

/-- **`NP ⊆ EXP`**, through `PSPACE`. -/
theorem NP_subset_EXP : NP enc ⊆ EXP enc :=
  NP_subset_PSPACE.trans PSPACE_subset_EXP

/-! ### Closure properties of `PSPACE` -/

/-- A polynomial-time function is tidily computable within polynomial bounds. -/
private theorem exists_computableTidilyInO_of_polyTime {β γ : Type} {encIn : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {f : β → γ} (h : ComputableTidilyInPolyTime f encIn encOut) :
    ∃ T S, PolyBounded (fun b => (encIn b).length) T ∧ PolyBounded (fun b => (encIn b).length) S ∧
      ComputableTidilyInO f encIn encOut T S :=
  let ⟨t, s, ht, hs, hf⟩ := h
  ⟨t, fun b => t b + s b, ht, ht.add hs, ⟨1, hf.mono (fun _ => by omega)
    fun _ => by dsimp only; omega, fun b => by have := hf.length_le b; dsimp only; omega⟩⟩

/-- **`PSPACE` in the quantitative calculus**: a problem is in `PSPACE` exactly when a Boolean
function deciding it is tidily computable within some time and within space polynomial in the
length of the encoded instance. -/
theorem mem_PSPACE_iff_computableTidilyInO : A ∈ PSPACE enc ↔ ∃ (f : α → Bool) (T S : α → ℕ),
    ComputableTidilyInO f enc encBool T S ∧ PolyBounded (fun a => (enc a).length) S ∧
      ∀ a, a ∈ A ↔ f a = true := by
  constructor
  · rintro ⟨f, ⟨t, s, hs, hf⟩, hA⟩
    obtain ⟨c, hc⟩ := ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace hf
    exact ⟨f, fun a => 2 * t a + 3 * s a + c, s, .of_bounds hc (c + 1) (fun a => by nlinarith)
      (fun a => by nlinarith) fun a => by
        simp only [encBool_apply, List.length_singleton]
        exact Nat.mul_pos (Nat.succ_pos c) (Nat.succ_pos (s a)),
      hs, hA⟩
  · rintro ⟨f, T, S, ⟨c, hc, -⟩, hS, hA⟩
    exact ⟨f, ⟨_, _, (PolyBounded.const c).mul (hS.add (.const 1)), hc.computableInTimeAndSpace⟩,
      hA⟩

/-- **`PSPACE` is closed under complement**: negate the answer. -/
theorem compl_mem_PSPACE (hA : A ∈ PSPACE enc) : Aᶜ ∈ PSPACE enc := by
  obtain ⟨f, T, S, hf, hS, hA⟩ := mem_PSPACE_iff_computableTidilyInO.mp hA
  have hnot := (ComputableTidilyInDegree.of_finite (encIn := encBool) (encMid := encBool)
    Bool.not).inO_one.comp_linear hf
  refine mem_PSPACE_iff_computableTidilyInO.mpr ⟨_, T, S, hnot, hS, fun a => ?_⟩
  simp [hA a]

/-- **`PSPACE` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_PSPACE {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ PSPACE encB) : A ∈ PSPACE enc := by
  obtain ⟨g, hg, hAB⟩ := h
  obtain ⟨f, T, S, hf, hS, hB⟩ := mem_PSPACE_iff_computableTidilyInO.mp hB
  obtain ⟨Tg, Sg, -, hSg, hgO⟩ := exists_computableTidilyInO_of_polyTime hg
  exact mem_PSPACE_iff_computableTidilyInO.mpr ⟨f ∘ g, _, _, hf.comp hgO,
    hSg.add (hS.comp hg.polyBounded_length), fun a => (hAB a).trans (hB (g a))⟩

/-- The edges of the graph on words of width `n + 1` whose reachability within two steps from the
all-zero word to the all-one word is a bounded existential over `f`: an edge from the all-zero word
to `true :: w` when `f (x, w)`, and from every word starting with `true` to the all-one word. -/
private def existsEdge {β : Type} (f : β × List Bool → Bool) (x : β) (u v : List Bool) : Bool :=
  if !(u.any fun b => b) && v.headD false then f (x, v.tail)
  else u.headD false && !(v.any fun b => !b)

/-- Savitch's algorithm at depth `1` on the edges of `existsEdge` decides the bounded
existential. -/
private theorem savitch_existsEdge {β : Type} (f : β × List Bool → Bool) (x : β) (n : ℕ) :
    Cslib.Reachability.savitch (existsEdge f x) (n + 1) 1 (List.replicate (n + 1) false)
      (List.replicate (n + 1) true) = true ↔ ∃ w : List Bool, w.length = n ∧ f (x, w) = true := by
  rw [Cslib.Reachability.savitch_eq]
  simp only [Cslib.Reachability.reach, List.any_eq_true, Cslib.BitString.mem_enumList,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨m, hm, h₁ | h₁, h₂ | h₂⟩
    · subst h₁
      exact absurd h₂ (by simp [List.replicate_succ])
    · subst h₁
      refine ⟨List.replicate n true, List.length_replicate .., ?_⟩
      simpa [existsEdge, List.replicate_succ] using h₂
    · subst h₂
      refine ⟨List.replicate n true, List.length_replicate .., ?_⟩
      simpa [existsEdge, List.replicate_succ] using h₁
    · obtain ⟨b, w, rfl⟩ := List.exists_cons_of_length_eq_add_one hm
      refine ⟨w, by simpa using hm, ?_⟩
      cases b <;> simp_all [existsEdge, List.replicate_succ]
  · rintro ⟨w, hw, hf⟩
    refine ⟨true :: w, by simp [hw], Or.inr ?_, Or.inr ?_⟩
    · simp [existsEdge, List.replicate_succ, hf]
    · simp [existsEdge, List.replicate_succ]

/-- **`PSPACE` is closed under polynomially bounded existential quantification**: if `B ⊆ β × List
Bool` is in `PSPACE` and `ℓ` is polynomial-time, then so is the set of the `x` for which some word
`w` of length `ℓ x` has `(x, w) ∈ B`. The candidates are enumerated in place: this is reachability
within two steps between two words of width `ℓ x + 1` (`existsEdge`), which Savitch's algorithm
decides at depth `1`, reusing the space of the decider of `B` for every candidate
(`Cslib.Reachability.computableTidilyInO_savitch`). -/
theorem setOf_exists_mem_PSPACE {β : Type} {encB : β ↪ List Bool} {B : Set (β × List Bool)}
    {ℓ : β → ℕ} (hB : B ∈ PSPACE (encPair encB encBits))
    (hℓ : ComputableTidilyInPolyTime ℓ encB encUnary) :
    {x | ∃ w : List Bool, w.length = ℓ x ∧ (x, w) ∈ B} ∈ PSPACE encB := by
  obtain ⟨f, T, S, hf, hS, hB⟩ := mem_PSPACE_iff_computableTidilyInO.mp hB
  set encQ := encPair encB (encPair encBits encBits)
  -- the edge test: polynomial-time tests around one call of the decider of `B`
  have hg : ComputableTidilyInPolyTime (fun q : β × List Bool × List Bool => (q.1, q.2.2.tail))
      encQ (encPair encB encBits) :=
    (ComputableTidilyInPolyTime.fst _ _).prod
      (ComputableTidilyInPolyTime.bitsTail.comp
        ((ComputableTidilyInPolyTime.snd _ _).comp (.snd _ _)))
  have hc : ComputableTidilyInPolyTime
      (fun q : β × List Bool × List Bool => !(q.2.1.any fun b => b) && q.2.2.headD false)
      encQ encBool :=
    ComputableTidilyInPolyTime.bool_and.comp
      ((ComputableTidilyInPolyTime.bool_not.comp
        (ComputableTidilyInPolyTime.bitsAnyWithInput (test := fun _ b => b)
          ((ComputableTidilyInPolyTime.fst _ _).comp (.snd _ _)) (.snd _ _))).prod
        ((ComputableTidilyInPolyTime.headD (encA := encBool) false).comp
          ((ComputableTidilyInPolyTime.snd _ _).comp (.snd _ _))))
  have he : ComputableTidilyInPolyTime
      (fun q : β × List Bool × List Bool => q.2.1.headD false && !(q.2.2.any fun b => !b))
      encQ encBool :=
    ComputableTidilyInPolyTime.bool_and.comp
      (((ComputableTidilyInPolyTime.headD (encA := encBool) false).comp
        ((ComputableTidilyInPolyTime.fst _ _).comp (.snd _ _))).prod
        (ComputableTidilyInPolyTime.bool_not.comp
          (ComputableTidilyInPolyTime.bitsAnyWithInput (test := fun _ b => !b)
            ((ComputableTidilyInPolyTime.snd _ _).comp (.snd _ _))
            (ComputableTidilyInPolyTime.bool_not.comp (.snd _ _)))))
  obtain ⟨Tg, Sg, -, hSg, hgO⟩ := exists_computableTidilyInO_of_polyTime hg
  obtain ⟨Tc, Sc, -, hSc, hcO⟩ := exists_computableTidilyInO_of_polyTime hc
  obtain ⟨Te, Se, -, hSe, heO⟩ := exists_computableTidilyInO_of_polyTime he
  have hedge := hcO.ite (hf.comp hgO) heO
  -- the arguments of Savitch's algorithm
  have hin : ComputableTidilyInPolyTime
      (fun x => (x, ℓ x + 1, 1, List.replicate (ℓ x + 1) false, List.replicate (ℓ x + 1) true))
      encB (Cslib.Reachability.encArgs encB) := by
    have hw : ComputableTidilyInPolyTime (fun x => ℓ x + 1) encB encUnary :=
      ComputableTidilyInPolyTime.unary_add.comp (hℓ.prod (.const 1))
    exact ComputableTidilyInPolyTime.id'.prod (hw.prod ((ComputableTidilyInPolyTime.const 1).prod
      (((ComputableTidilyInPolyTime.bitsReplicate false).comp hw).prod
        ((ComputableTidilyInPolyTime.bitsReplicate true).comp hw))))
  obtain ⟨Ti, Si, -, hSi, hinO⟩ := exists_computableTidilyInO_of_polyTime hin
  have h := Cslib.Reachability.computableTidilyInO_savitch (edge := existsEdge f) (par := id)
    hedge hinO (fun _ => List.length_replicate ..) fun _ => List.length_replicate ..
  -- the space is polynomial
  have hSedge : PolyBounded (fun q => (encQ q).length) fun q =>
      Sc q + if !(q.2.1.any fun b => b) && q.2.2.headD false then Sg q + S (q.1, q.2.2.tail)
        else Se q :=
    (hSc.add (hSg.add (hS.comp hg.polyBounded_length) |>.add hSe)).mono fun q => by
      split_ifs <;> omega
  obtain ⟨cE, dE, hcE⟩ := hSedge.exists_le
  have hℓ' : PolyBounded (fun x => (encB x).length) ℓ :=
    hℓ.polyBounded_length.mono fun x => by simp [encUnary_apply]
  have hG : PolyBounded (fun x => (encB x).length)
      fun x => 2 * (encB x).length + 3 * ℓ x + 6 :=
    (((PolyBounded.const 2).mul .self).add ((PolyBounded.const 3).mul hℓ')).add (.const 6)
  have hpow : PolyBounded (fun x => (encB x).length)
      fun x => cE * (2 * (encB x).length + 3 * ℓ x + 6) ^ dE :=
    PolyBounded.comp (size' := id) (v := fun n => cE * n ^ dE)
      (PolyBounded.of_polynomiallyBounded (bound := fun n => cE * n ^ dE) id (by fun_prop)) hG
  refine mem_PSPACE_iff_computableTidilyInO.mpr ⟨_, _, _, h, ?_, fun x => ?_⟩
  · refine (((hSi.add ((PolyBounded.const 2).mul (hℓ'.add (.const 3)))).add .self).add
      hpow).mono fun x => ?_
    have hmax : Cslib.Reachability.edgeMax (fun q : β × List Bool × List Bool =>
        Sc q + if (!(q.2.1.any fun b => b) && q.2.2.headD false) = true then
          Sg q + S (q.1, q.2.2.tail) else Se q) x (ℓ x + 1) ≤
        cE * (2 * (encB x).length + 3 * ℓ x + 6) ^ dE :=
      listMax_le fun u hu => listMax_le fun v hv => by
        refine (hcE _).trans (Nat.mul_le_mul_left cE (Nat.pow_le_pow_left ?_ dE))
        simp only [encQ, length_encPair, encBits_apply, Cslib.BitString.mem_enumList.mp hu,
          Cslib.BitString.mem_enumList.mp hv]
        omega
    change Si x + (1 + 1) * (1 + (ℓ x + 1) + 1) + (encB x).length +
        Cslib.Reachability.edgeMax (fun q : β × List Bool × List Bool =>
          Sc q + if (!(q.2.1.any fun b => b) && q.2.2.headD false) = true then
            Sg q + S (q.1, q.2.2.tail) else Se q) x (ℓ x + 1) ≤
      Si x + 2 * (ℓ x + 3) + (encB x).length + cE * (2 * (encB x).length + 3 * ℓ x + 6) ^ dE
    omega
  · simp only [Set.mem_ofPred_eq, hB, id]
    exact (savitch_existsEdge f x (ℓ x)).symm

end Cslib.Complexity
