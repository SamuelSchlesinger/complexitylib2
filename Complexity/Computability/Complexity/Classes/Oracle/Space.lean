/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle.Closure
public import Complexity.Computability.Complexity.Classes.Space
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
import Complexity.Computability.Complexity.Classes.Oracle.Simulation
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Polynomial time relative to an oracle in polynomial space

Relative to an oracle language decided within polynomial space, polynomial time and
nondeterministic polynomial time are within polynomial space [Arora and Barak, Theorem
3.7][AroraBarak09]: `NP^A ⊆ NPSPACE = PSPACE` for `A ∈ PSPACE`.

A computation in polynomial time relative to `A` is the clocked run, with every coin fixed to
`false`, of a finite oracle machine (`Cslib.Probability.IsOraclePPTOn.exists_fin_run_pure_false`).
The run is simulated instruction by instruction, answering each query with the decider of `A` on
the request, which is no longer than the clock
(`Turing.MultiTapePTM.exists_computableTidilyInO_run`).
So the space is polynomial, while the time charges the decider of `A` once per instruction
(`Cslib.Complexity.ComputableInPolyTimeWithOracle.exists_computableTidilyInO`,
`Cslib.Complexity.PWithOracle_subset_PSPACE`).

For `NP` relative to `A`, the certificates of the required length are tried one after another, in
binary order, keeping only the current certificate and whether some certificate was accepted
(`Cslib.Complexity.mem_PSPACE_of_isVerifier`, `Cslib.Complexity.NPWithOracle_subset_PSPACE`). This
deterministic search replaces the passage through `NPSPACE` and Savitch's theorem.

## Main results

* `Cslib.Complexity.exists_computableTidilyInO_of_mem_PSPACE`,
  `Cslib.Complexity.mem_PSPACE_of_computableTidilyInO`: `PSPACE` in terms of tidy computability
  within explicit bounds.
* `Cslib.Complexity.mem_PSPACE_of_isVerifier`: certificate search within polynomial space.
* `Cslib.Complexity.ComputableInPolyTimeWithOracle.exists_computableTidilyInO`: polynomial time
  relative to an oracle in `PSPACE` is within polynomial space.
* `Cslib.Complexity.PWithOracle_subset_PSPACE`, `Cslib.Complexity.NPWithOracle_subset_PSPACE`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool}

/-! ### `PSPACE` through tidy computability -/

/-- A problem in `PSPACE` has a tidy decider within explicit bounds, the space polynomial in the
length of the encoded instance. -/
theorem exists_computableTidilyInO_of_mem_PSPACE {L : Set α} (hL : L ∈ PSPACE enc) :
    ∃ T S, PolyBounded (fun a => (enc a).length) S ∧
      ∃ f : α → Bool, ComputableTidilyInO f enc encBool T S ∧ ∀ a, a ∈ L ↔ f a = true := by
  obtain ⟨f, ⟨t, s, hs, hf⟩, hL⟩ := hL
  obtain ⟨c, hc⟩ := hf.exists_computableTidilyInTimeAndSpace
  refine ⟨fun a => 2 * t a + 3 * s a + c, fun a => c * (s a + 1),
    (PolyBounded.const c).mul (hs.add (.const 1)), f,
    .of_bounds hc 1 (fun a => by omega) (fun a => by omega) (fun a => ?_), hL⟩
  rw [encBool_apply, List.length_singleton]
  have := Nat.mul_le_mul_left c (Nat.le_add_left 1 (s a))
  nlinarith

/-- A tidy decider within polynomial space puts a problem in `PSPACE`. -/
theorem mem_PSPACE_of_computableTidilyInO {L : Set α} {f : α → Bool} {T S : α → ℕ}
    (hf : ComputableTidilyInO f enc encBool T S) (hS : PolyBounded (fun a => (enc a).length) S)
    (hL : ∀ a, a ∈ L ↔ f a = true) : L ∈ PSPACE enc :=
  let ⟨c, hc, _⟩ := hf
  ⟨f, ⟨_, _, (PolyBounded.const c).mul (hS.add (.const 1)), hc.computableInTimeAndSpace⟩, hL⟩

/-! ### Certificate search -/

/-- Binary increment, least significant bit first, discarding the final carry. -/
private def incr : List Bool → List Bool
  | [] => []
  | false :: w => true :: w
  | true :: w => false :: incr w

/-- The value of a word in binary, least significant bit first. -/
private def val : List Bool → ℕ
  | [] => 0
  | b :: w => b.toNat + 2 * val w

private theorem length_incr : ∀ w, (incr w).length = w.length
  | [] => rfl
  | false :: _ => rfl
  | true :: w => by simp [incr, length_incr w]

private theorem val_lt : ∀ w, val w < 2 ^ w.length
  | [] => by simp [val]
  | b :: w => by
    have := val_lt w
    cases b <;> simp [val, pow_succ] <;> omega

private theorem val_incr : ∀ w, val w + 1 < 2 ^ w.length → val (incr w) = val w + 1
  | [] => by simp [val]
  | false :: w => fun _ => by simp [incr, val]; omega
  | true :: w => fun h => by
    simp only [val, List.length_cons, pow_succ, Bool.toNat_true, incr, Bool.toNat_false] at h ⊢
    rw [val_incr w (by omega)]
    omega

private theorem val_injective : ∀ {w w' : List Bool}, w.length = w'.length → val w = val w' →
    w = w'
  | [], [], _, _ => rfl
  | b :: w, b' :: w', hl, hv => by
    simp only [val] at hv
    have hb : b = b' := by
      cases b <;> cases b' <;> first | rfl | (simp at hv; omega)
    subst hb
    exact congrArg _ (val_injective (by simpa using hl) (by omega))

private theorem val_replicate_false : ∀ m, val (List.replicate m false) = 0
  | 0 => rfl
  | m + 1 => by simp [List.replicate_succ, val, val_replicate_false m]

private theorem iterate_incr (m : ℕ) : ∀ j < 2 ^ m,
    val (incr^[j] (List.replicate m false)) = j ∧ (incr^[j] (List.replicate m false)).length = m
  | 0, _ => ⟨val_replicate_false m, List.length_replicate⟩
  | j + 1, hj => by
    obtain ⟨hv, hl⟩ := iterate_incr m j (by omega)
    rw [Function.iterate_succ_apply', length_incr, val_incr _ (by rw [hv, hl]; omega), hv]
    exact ⟨rfl, hl⟩

private theorem iterate_incr_val (u : List Bool) :
    incr^[val u] (List.replicate u.length false) = u :=
  let h := iterate_incr u.length (val u) (val_lt u)
  val_injective h.2 h.1

/-- Increment by a two-state transducer, the state being the carry. -/
private def incrT : Transducer Bool Bool where
  q₀ := true
  step c b := (c && b, [b ^^ c])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private theorem incrT_run_false (w : List Bool) : incrT.run false w = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [Transducer.run_cons]
    change [b ^^ false] ++ incrT.run (false && b) w = b :: w
    rw [Bool.false_and, ih, Bool.xor_false]
    rfl

private theorem incrT_run (w : List Bool) : incrT.run true w = incr w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [Transducer.run_cons]
    change [b ^^ true] ++ incrT.run (true && b) w = incr (b :: w)
    cases b
    · rw [Bool.true_and, incrT_run_false]
      rfl
    · rw [Bool.true_and, ih]
      rfl

private theorem incr_pt : ComputableTidilyInPolyTime incr encBits encBits :=
  .of_linear (incrT.computableTidilyInLinearTimeAndSpace fun w => by
    rw [show incrT.q₀ = true from rfl, incrT_run]; rfl)

/-- A round of the search: test a certificate, record the verdict, move to the next. -/
private def searchStep (V : α × List Bool → Bool) (x : α × List Bool × Bool) :
    α × List Bool × Bool :=
  (x.1, incr x.2.1, x.2.2 || V (x.1, x.2.1))

private theorem iterate_searchStep (V : α × List Bool → Bool) (a : α) (m : ℕ) : ∀ i,
    (searchStep V)^[i] (a, List.replicate m false, false) =
      (a, incr^[i] (List.replicate m false),
        decide (∃ j < i, V (a, incr^[j] (List.replicate m false)) = true))
  | 0 => by simp
  | i + 1 => by
    rw [Function.iterate_succ_apply', iterate_searchStep V a m i]
    simp only [searchStep, Function.iterate_succ_apply', Prod.mk.injEq, true_and]
    rw [Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    constructor
    · rintro (⟨j, hj, h⟩ | h)
      · exact ⟨j, by omega, h⟩
      · exact ⟨i, by omega, h⟩
    · rintro ⟨j, hj, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact Or.inl ⟨j, hj, h⟩
      · exact Or.inr h

private theorem search_spec (V : α × List Bool → Bool) (a : α) (m : ℕ) :
    ((searchStep V)^[2 ^ m] (a, List.replicate m false, false)).2.2 = true ↔
      ∃ u : List Bool, u.length = m ∧ V (a, u) = true := by
  rw [iterate_searchStep, decide_eq_true_iff]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨_, (iterate_incr m j hj).2, h⟩
  · rintro ⟨u, rfl, h⟩
    exact ⟨val u, val_lt u, by rw [iterate_incr_val]; exact h⟩


/-- **Certificate search in polynomial space.** A problem with a verifier decidable within
polynomial space and certificates of polynomial length is in `PSPACE`: the certificates of the
required length are tried one after another, keeping only the current one. -/
theorem mem_PSPACE_of_isVerifier {p : Polynomial ℕ} {V : α × List Bool → Bool} {L : Set α}
    {T S : α × List Bool → ℕ} (hV : ComputableTidilyInO V (encPair enc encBits) encBool T S)
    (hS : PolyBounded (fun x => (encPair enc encBits x).length) S) (hL : IsVerifier enc p V L) :
    L ∈ PSPACE enc := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · exact P_subset_PSPACE ⟨fun _ => false, ComputableTidilyInPolyTime.const false,
      fun a => isEmptyElim a⟩
  let _ : Inhabited α := Classical.inhabited_of_nonempty hα
  obtain ⟨cS, dS, hS⟩ := hS.exists_le
  set encS : α × List Bool × Bool ↪ List Bool := encPair enc (encPair encBits encBool)
  -- a round of the search
  have hstep : ∃ e, ComputableTidilyInO (searchStep V) encS encS
      (fun x => ((encS x).length + 1) ^ e + T (x.1, x.2.1))
      (fun x => ((encS x).length + 1) ^ e + S (x.1, x.2.1)) := by
    have hproj : ComputableTidilyInPolyTime (fun x : α × List Bool × Bool => (x.1, x.2.1)) encS
        (encPair enc encBits) := by fun_prop
    have hfst : ComputableTidilyInPolyTime (fun x : α × List Bool × Bool => x.1) encS enc := by
      fun_prop
    have hinc : ComputableTidilyInPolyTime (fun x : α × List Bool × Bool => incr x.2.1) encS
        encBits := incr_pt.comp (by fun_prop)
    have hacc : ComputableTidilyInPolyTime (fun x : α × List Bool × Bool => x.2.2) encS
        encBool := by fun_prop
    have hor : ComputableTidilyInPolyTime (fun q : Bool × Bool => q.1 || q.2)
        (encPair encBool encBool) encBool := ComputableTidilyInPolyTime.of_finite _
    obtain ⟨d₁, _, h₁⟩ := hproj.exists_degree
    obtain ⟨d₂, _, h₂⟩ := hfst.exists_degree
    obtain ⟨d₃, _, h₃⟩ := hinc.exists_degree
    obtain ⟨d₄, _, h₄⟩ := hacc.exists_degree
    obtain ⟨d₅, _, h₅⟩ := hor.exists_degree
    have h := h₂.inO.prod (h₃.inO.prod (h₅.inO.comp (h₄.inO.prod (hV.comp h₁.inO))))
    refine ⟨d₁ + d₂ + d₃ + d₄ + d₅, (h.mono (5 ^ d₅ + 5) (fun x => ?_) fun x => ?_).of_enc_eq
      fun x => rfl⟩
    all_goals
      simp only [Function.comp_apply, length_encPair, encBool_apply, List.length_singleton]
      generalize (encS x).length = N
      have hN : 1 ≤ N + 1 := by omega
      have hpow (d : ℕ) (hd : d ≤ d₁ + d₂ + d₃ + d₄ + d₅) :
          (N + 1) ^ d ≤ (N + 1) ^ (d₁ + d₂ + d₃ + d₄ + d₅) := Nat.pow_le_pow_right hN hd
      have h5 : (2 * 1 + 1 + 1 + 1) ^ d₅ ≤ 5 ^ d₅ := le_rfl
      have h₁' := hpow d₁ (by omega)
      have h₂' := hpow d₂ (by omega)
      have h₃' := hpow d₃ (by omega)
      have h₄' := hpow d₄ (by omega)
      have h5' : 1 ≤ 5 ^ d₅ := Nat.one_le_pow _ _ (by omega)
      generalize (N + 1) ^ (d₁ + d₂ + d₃ + d₄ + d₅) = M at *
      nlinarith
  obtain ⟨e, hstep⟩ := hstep
  -- the number of certificates, in binary, and the start
  set m : α → ℕ := fun a => p.eval (enc a).length with hm_def
  have hm : ComputableTidilyInPolyTime m enc encUnary :=
    (ComputableTidilyInPolyTime.unary_eval p).comp (by fun_prop)
  have hn : ComputableTidilyInPolyTime (fun a => 2 ^ m a) enc encNat :=
    ((ComputableTidilyInDegree.two_pow_length encUnary).computableTidilyInPolyTime.comp
      hm).of_enc_eq fun a => by simp [encUnary_apply]
  have hinit : ComputableTidilyInPolyTime (fun a => (a, List.replicate (m a) false, false)) enc
      encS :=
    ComputableTidilyInPolyTime.id'.prod ((ComputableTidilyInPolyTime.listToBits.comp
      (ComputableTidilyInPolyTime.replicate hm (ComputableTidilyInPolyTime.const false
        (encMid := encBool)))).prod (ComputableTidilyInPolyTime.const false))
  have hout : ComputableTidilyInPolyTime (fun x : α × List Bool × Bool => x.2.2) encS encBool := by
    fun_prop
  obtain ⟨dn, _, hn⟩ := hn.exists_degree
  obtain ⟨di, _, hinit⟩ := hinit.exists_degree
  obtain ⟨do', _, hout⟩ := hout.exists_degree
  -- the states of the search
  set B : α → ℕ := fun a => 2 * (enc a).length + 2 * m a + 3 with hB
  have hiter (a : α) (i : ℕ) :
      (searchStep V)^[i] (a, List.replicate (m a) false, false) =
        (a, incr^[i] (List.replicate (m a) false),
          decide (∃ j < i, V (a, incr^[j] (List.replicate (m a) false)) = true)) :=
    iterate_searchStep V a (m a) i
  have hlen (a : α) (i : ℕ) : (incr^[i] (List.replicate (m a) false)).length = m a := by
    induction i with
    | zero => exact List.length_replicate
    | succ i ih => rw [Function.iterate_succ_apply', length_incr, ih]
  have hstate (a : α) (i : ℕ) :
      (encS ((searchStep V)^[i] (a, List.replicate (m a) false, false))).length = B a := by
    rw [hiter]
    simp only [encS, length_encPair, encBits_apply, hlen, encBool_apply, List.length_singleton, hB]
    omega
  have hit := ComputableTidilyInO.iterate hn.inO hinit.inO hstep
    (R := fun a => (B a + 1) ^ e + wordMax (fun u => T (a, u)) (m a))
    (Q := fun a => (B a + 1) ^ e + cS * (2 * (enc a).length + 1 + m a + 1) ^ dS) (B := B)
    (fun a i _ => by
      rw [hstate]
      refine Nat.add_le_add_left ?_ _
      rw [hiter]
      exact le_wordMax (fun u => T (a, u)) (hlen a i).le)
    (fun a i _ => by
      rw [hstate]
      refine Nat.add_le_add_left
        ((hS _).trans (Nat.mul_le_mul_left cS (Nat.pow_le_pow_left ?_ dS))) _
      rw [hiter]
      simp only [length_encPair, encBits_apply, hlen]
      omega)
    (fun a i _ => (hstate a i).le)
  have h := hout.inO.comp hit
  refine mem_PSPACE_of_computableTidilyInO (h.mono_le (T' := fun a => _ + (B a + 1) ^ do')
    (S' := fun a => ((enc a).length + 1) ^ dn + ((enc a).length + 1) ^ di +
      ((B a + 1) ^ e + cS * (2 * (enc a).length + 1 + m a + 1) ^ dS) + B a + (m a + 1) +
        (B a + 1) ^ do') (fun a => by simp only [hstate]; rfl)
    (fun a => by
      simp only [hstate, encNat_two_pow, List.length_append,
        List.length_replicate, List.length_singleton]
      rfl)) ?_ fun a => ?_
  · exact PolyBounded.mono (PolyBounded.of_polynomiallyBounded (fun a => (enc a).length)
      (bound := fun L => (L + 1) ^ dn + (L + 1) ^ di +
        ((2 * L + 2 * p.eval L + 3 + 1) ^ e + cS * (2 * L + 1 + p.eval L + 1) ^ dS) +
        (2 * L + 2 * p.eval L + 3) + (p.eval L + 1) + (2 * L + 2 * p.eval L + 3 + 1) ^ do')
      (by fun_prop)) fun a => le_rfl
  · rw [hL a]
    exact (search_spec V a (m a)).symm

/-! ### Oracles in polynomial space -/

open Classical in
/-- **Oracle polynomial time within polynomial space.** Relative to an oracle language in
`PSPACE`, a function computable in polynomial time relative to it is tidily computable within
space polynomial in the length of the encoded input. -/
theorem ComputableInPolyTimeWithOracle.exists_computableTidilyInO {A : Set (List Bool)}
    {f : α → β} {output : β ↪ List Bool} (hA : A ∈ PSPACE encBits)
    (hf : ComputableInPolyTimeWithOracle A f enc output) :
    ∃ T S, PolyBounded (fun a => (enc a).length) S ∧ ComputableTidilyInO f enc output T S := by
  obtain ⟨TA, SA, hSA, g, hg, hgA⟩ := exists_computableTidilyInO_of_mem_PSPACE hA
  have hg' : g = fun w => decide (w ∈ A) := funext fun w =>
    Bool.eq_iff_iff.mpr ⟨fun h => decide_eq_true ((hgA w).mpr h),
      fun h => (hgA w).mp (of_decide_eq_true h)⟩
  subst hg'
  obtain ⟨program, hcert, hprogram⟩ := hf
  obtain ⟨k, m, machine, c, d, hrun⟩ := hcert.exists_fin_run_pure_false
  obtain ⟨T, S, hS, h⟩ := machine.exists_computableTidilyInO_run (input := enc) hg
    (by simpa [encBits] using hSA) c d
  refine ⟨T, S, hS, h.of_enc_eq fun a => ?_⟩
  rw [← hprogram a, ← hrun a (languageOracle A)]
  rfl

/-- **`P` relative to an oracle in `PSPACE` is within `PSPACE`.** -/
theorem PWithOracle_subset_PSPACE {A : Set (List Bool)} (hA : A ∈ PSPACE encBits) :
    PWithOracle A enc ⊆ PSPACE enc := fun _ ⟨_, hf, hL⟩ =>
  let ⟨_, _, hS, h⟩ := hf.exists_computableTidilyInO hA
  mem_PSPACE_of_computableTidilyInO h hS hL

/-- **`NP` relative to an oracle in `PSPACE` is within `PSPACE`** [Arora and Barak, Theorem
3.7][AroraBarak09]: the verifier runs within polynomial space, and its certificates are searched
one after another. -/
theorem NPWithOracle_subset_PSPACE {A : Set (List Bool)} (hA : A ∈ PSPACE encBits) :
    NPWithOracle A enc ⊆ PSPACE enc := fun _ ⟨_, _, hV, hL⟩ =>
  let ⟨_, _, hS, h⟩ := hV.exists_computableTidilyInO hA
  mem_PSPACE_of_isVerifier h hS hL

end Cslib.Complexity
