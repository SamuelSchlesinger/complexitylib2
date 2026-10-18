/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Machine
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Decode
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Run
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# A decidable problem outside P

The diagonal function `Cslib.Complexity.diagonal` reads a description of a machine framed at the
start of its input `x` (`Turing.MultiTapeTM.Universal.decodeDesc`), runs the described machine on
the whole of `x`, symbol by symbol under the fixed coding `false ↦ 0`, `true ↦ 1`, for
`2 ^ x.length` steps with the universal function, and negates the verdict: it returns `false`
exactly when the described machine has halted with output `[true]` by then.

No machine computing a Boolean function in polynomial time decides the diagonal problem
[Arora and Barak, Theorem 3.1][AroraBarak09]. Its description, padded to a length where the machine
halts within the exponential clock, is an input on which the diagonal returns the negation of the
machine's answer (`Cslib.Complexity.diagonal_not_mem_P`).

## Main definitions

* `Cslib.Complexity.diagonal`: the diagonal function.

## Main results

* `Cslib.Complexity.diagonal_not_mem_P`: the diagonal problem is not in `P`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]

The padded diagonal argument follows the original Complexitylib's `Classes/Hierarchy` and
`UTM/Diagonal` (Samuel Schlesinger), here on the native universal interpreter of Christian
Reitwiessner.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- The fixed coding of Boolean symbols by numbers: `false ↦ 0` and `true ↦ 1`. -/
def boolSym : Bool ↪ ℕ := ⟨Bool.toNat, fun a b h => by cases a <;> cases b <;> simp_all⟩

/-- **The diagonal function.** Run the machine described at the start of `x` on `x` for
`2 ^ x.length` steps, and return `false` exactly when it has halted with output `[true]`. -/
def diagonal (x : List Bool) : Bool :=
  let r := universal (decodeDesc (unframe x), x.map boolSym, 2 ^ x.length)
  !(r.2 && decide (r.1 = [boolSym true]))

/-! ### The symbols of the input -/

/-- The code of a bit list with every `true` doubled: `false ↦ [false]`, `true ↦ [true, true]`. -/
def doubled (b : Bool) : List Bool := if b then [true, true] else [false]

/-- Bit lists with every `true` doubled. -/
def encDoubled : List Bool ↪ List Bool :=
  ⟨fun x => x.flatMap doubled, fun x y h => by
    induction x generalizing y with
    | nil => cases y with
      | nil => rfl
      | cons b y => cases b <;> simp [doubled] at h
    | cons a x ih => cases y with
      | nil => cases a <;> simp [doubled] at h
      | cons b y =>
        cases a <;> cases b <;> simp only [doubled, List.flatMap_cons, Bool.false_eq_true,
          ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq, true_and,
          reduceCtorEq, false_and] at h ⊢ <;> exact ih _ h⟩

/-- Doubles every `true`. -/
def doubleT : Transducer Bool Unit where
  q₀ := ()
  step _ b := ((), doubled b)
  final _ := []
  length_step_le _ b := by cases b <;> simp [doubled]
  length_final_le _ := by simp

/-- Reads a doubled word as the framed unary symbols `0` for `false` and `1` for `true`. -/
def symbolsT : Transducer Bool Bool where
  q₀ := false
  step
    | false, false => (false, [false])
    | false, true => (true, [true, true])
    | true, _ => (false, [false])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> simp
  length_final_le _ := by simp

theorem doubleT_run (x : List Bool) : doubleT.run () x = encDoubled x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    rw [Transducer.run_cons, ih]
    rfl

theorem symbolsT_run (x : List Bool) :
    symbolsT.run false (encDoubled x) = encList encUnary (x.map boolSym) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    cases b
    · change (false :: symbolsT.run false (encDoubled x)) = _
      rw [ih]
      rfl
    · change (true :: true :: false :: symbolsT.run false (encDoubled x)) = _
      rw [ih]
      rfl

/-- The input as symbols, in linear time and space. -/
theorem computableTidilyInDegree_map_boolSym :
    ComputableTidilyInDegree (fun x : List Bool => x.map boolSym) encBits (encList encUnary) 1 1 :=
  (ComputableTidilyInDegree.of_linear (encIn := encDoubled)
    (symbolsT.computableTidilyInLinearTimeAndSpace fun x => (symbolsT_run x).symm)).comp
    (ComputableTidilyInDegree.of_linear (encIn := encBits) (encMid := encDoubled) (f := id)
      (doubleT.computableTidilyInLinearTimeAndSpace fun x => (doubleT_run x).symm))

/-- On its padded description, the diagonal negates the answer of a machine that halts within the
exponential clock. -/
theorem diagonal_desc {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)
    (tm : MultiTapeTM k Bool State) (pad : List Bool) {b : Bool}
    (hhalt : (tm.runFrom (tm.initCfg (frame (eDesc (desc eS boolSym tm)) ++ pad))
      (2 ^ (frame (eDesc (desc eS boolSym tm)) ++ pad).length)).Halted)
    (hout : (tm.runFrom (tm.initCfg (frame (eDesc (desc eS boolSym tm)) ++ pad))
      (2 ^ (frame (eDesc (desc eS boolSym tm)) ++ pad).length)).output = [b]) :
    diagonal (frame (eDesc (desc eS boolSym tm)) ++ pad) = !b := by
  rw [diagonal, decodeDesc_unframe_frame_append, universal_desc, hout]
  simp only [List.map_cons, List.map_nil, Cfg.Halted] at hhalt ⊢
  rw [hhalt]
  cases b <;> simp [boolSym]

/-- **The diagonal problem is not in `P`** [Arora and Barak, Theorem 3.1][AroraBarak09]. -/
theorem diagonal_not_mem_P : {x | diagonal x = true} ∉ P encBits := by
  rintro ⟨f, ⟨t, s, ht, -, k, State, hfinite, tm, htm⟩, hf⟩
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  -- a padding beyond which the machine halts within the exponential clock
  obtain ⟨c, d, hle⟩ := ht.exists_le
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (PolynomiallyBounded.eventually_lt_two_pow (f := fun n => c * (n + 1) ^ d) (by fun_prop))
  set x := frame (eDesc (desc eS boolSym tm)) ++ List.replicate N false with hx
  have hlen : N ≤ x.length := by simp [x]
  have htime : t x ≤ 2 ^ x.length := (hle x).trans (hN _ hlen).le
  obtain ⟨hhalt, hout⟩ := ComputesTidilyInTimeAndSpace.runFrom_initCfg (htm x)
  have heq := MultiTapeTM.runFrom_eq_of_halt tm _ htime hhalt
  have hhalt' : (tm.runFrom (tm.initCfg x) (2 ^ x.length)).Halted :=
    (congrArg Cfg.Halted heq).mpr hhalt
  have hout' : (tm.runFrom (tm.initCfg x) (2 ^ x.length)).output = [f x] :=
    (congrArg Cfg.output heq).trans hout
  have hdiag := diagonal_desc eS tm _ hhalt' hout'
  have hfx : f x = diagonal x := by
    cases h : diagonal x
    · cases hfx : f x
      · rfl
      · exact absurd ((hf x).mpr hfx) (by simp [h])
    · exact (hf x).mp h
  rw [← hfx] at hdiag
  cases hb : f x <;> simp [hb] at hdiag

/-! ### The resources of the diagonal -/

/-- A polynomially bounded function is bounded by a constant multiple of `2 ^ n`. -/
theorem exists_le_mul_two_pow {p : ℕ → ℕ} (hp : PolynomiallyBounded p) :
    ∃ C, ∀ n, p n ≤ C * 2 ^ n := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hp.eventually_lt_two_pow
  refine ⟨∑ m ∈ Finset.range N, p m + 1, fun n => ?_⟩
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rcases le_or_gt N n with hn | hn
  · exact (hN n hn).le.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  · have := Finset.single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hn)
    exact this.trans ((Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ hpow))

/-- **The resources of the universal run**, for a description of length, an input of encoded
length and a final number of digits of the clock at most `B`, and a clock `J ≥ 1`: time
`O(B ^ 5 * J ^ 3)` and space `O(B ^ 2 * J)`. -/
theorem universal_bounds_le {D N J B L : ℕ} (hD : D ≤ B) (hN : N ≤ B) (hL : L ≤ B) (hJ : 1 ≤ J) :
    (J + 1) * (stepBound D N J + runBound D N J + (L + 1) ^ 2) ≤ 100000 * (B + 1) ^ 5 * J ^ 3 ∧
      runBound D N J ≤ 200 * (B + 1) ^ 2 * J := by
  set M := B + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have hDM : D + 1 ≤ M := by omega
  have hNM : N + 1 ≤ M := by omega
  have hMJ : M ≤ M * J := Nat.le_mul_of_pos_right _ hJ
  have hM2 : M ≤ M ^ 2 := Nat.le_self_pow two_ne_zero _
  have hM2J : M ^ 2 ≤ M ^ 2 * J := Nat.le_mul_of_pos_right _ hJ
  have htape : tapeBound D J ≤ 36 * M * J := by
    unfold tapeBound
    nlinarith
  have hcfg : cfgBound D N J ≤ 80 * M ^ 2 * J := by
    unfold cfgBound
    have : D * (2 * tapeBound D J + 1) ≤ M * (72 * M * J + 1) :=
      Nat.mul_le_mul (by omega) (by linarith)
    nlinarith
  have hctx : ctxBound D N J ≤ 89 * M ^ 2 * J := by
    unfold ctxBound
    nlinarith
  have hrun : runBound D N J ≤ 200 * M ^ 2 * J := by
    unfold runBound
    have : J * (2 * D + 1) ≤ J * (2 * M) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  refine ⟨?_, hrun⟩
  have hstep : stepBound D N J ≤ 40500 * M ^ 5 * J ^ 2 := by
    unfold stepBound
    have h₁ : 2 * D + N + 2 ≤ 5 * M := by omega
    have h₂ : (ctxBound D N J + 1) ^ 2 ≤ (90 * M ^ 2 * J) ^ 2 :=
      Nat.pow_le_pow_left (by nlinarith) 2
    calc (2 * D + N + 2) * (ctxBound D N J + 1) ^ 2 ≤ (5 * M) * (90 * M ^ 2 * J) ^ 2 :=
          Nat.mul_le_mul h₁ h₂
      _ = 40500 * M ^ 5 * J ^ 2 := by ring
  have hM5 : M ^ 2 * J ≤ M ^ 5 * J ^ 2 :=
    Nat.mul_le_mul (Nat.pow_le_pow_right hM1 (by omega)) (Nat.le_self_pow two_ne_zero _)
  have hL2 : (L + 1) ^ 2 ≤ M ^ 5 * J ^ 2 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (hM2J.trans hM5)
  have hsum : stepBound D N J + runBound D N J + (L + 1) ^ 2 ≤ 40701 * M ^ 5 * J ^ 2 := by
    nlinarith
  calc (J + 1) * (stepBound D N J + runBound D N J + (L + 1) ^ 2)
      ≤ (2 * J) * (40701 * M ^ 5 * J ^ 2) := Nat.mul_le_mul (by omega) hsum
    _ ≤ 100000 * M ^ 5 * J ^ 3 := by ring_nf; omega

/-- The output test of the diagonal: not halted with output `[true]`. -/
def verdict (r : List ℕ × Bool) : Bool := !(r.2 && decide (r.1 = [boolSym true]))

/-- The test is within time quadratic and space linear in the encoded result. -/
theorem computableTidilyInO_verdict :
    ComputableTidilyInO verdict eOut encBool (fun r => ((eOut r).length + 1) ^ 2)
      fun r => (eOut r).length := by
  have heq := (ComputableTidilyInO.eq (encList encUnary)).comp
    ((ComputableTidilyInO.fst (encList encUnary) encBool).prod
      (ComputableTidilyInO.const (encMid := encList encUnary) [boolSym true]))
  have hfin := (ComputableTidilyInDegree.of_finite (encIn := encPair encBool encBool)
    (encMid := encBool) fun q : Bool × Bool => !(q.1 && q.2)).inO_one
  refine (hfin.comp ((ComputableTidilyInO.snd (encList encUnary) encBool).prod heq)).mono 64
    (fun r => ?_) fun r => ?_
  all_goals
    have h₁ := length_le_encPair_left (encList encUnary) encBool r
    have h₂ : (encList encUnary [boolSym true]).length = 3 := rfl
    simp only [Function.comp_apply, length_encPair, encBool_apply, List.length_singleton,
      h₂] at h₁ ⊢
  · nlinarith
  · omega

/-- The numeric core of the resources of the diagonal: for an input of length `n`, a decoded
description of encoded length `D`, encoded symbols of length `N`, a clock `J ≥ 1` and a result of
encoded length `E`, everything is within `K * M ^ 5 * J ^ 3` steps and `K * M ^ 5 * J` cells. -/
theorem diagonal_bounds_aux {n A D N J L I E cD cO M K : ℕ} (hJ : 1 ≤ J)
    (hD : D ≤ cD * (A + 1)) (hN : N ≤ 3 * n) (hL : L = n + 1) (hI : I = 2 * D + 1 + (2 * N + 1 + L))
    (hM : M = cD * (A + 1) + A + 4 * n + 2) (hK : K = 100100 + 44100 * (cO + 1) ^ 2)
    (hE : E ≤ cO * (A + (n + n) + (runBound D N J + I) + 1)) :
    A + (n + n) + ((J + 1) * (stepBound D N J + runBound D N J + (L + 1) ^ 2) + (I + 1) ^ 2) +
        (E + 1) ^ 2 ≤ K * (M ^ 5 * J ^ 3) ∧
      A + (n + n) + (runBound D N J + I) + E ≤ K * (M ^ 5 * J) := by
  subst hL hI
  have hM1 : 1 ≤ M := by omega
  obtain ⟨hU₁, hU₂⟩ := universal_bounds_le (D := D) (N := N) (J := J) (B := M - 1) (L := n + 1)
    (by omega) (by omega) (by omega) hJ
  rw [Nat.sub_add_cancel hM1] at hU₁ hU₂
  have hM2 : M ≤ M ^ 2 := Nat.le_self_pow two_ne_zero _
  have hMM2 : M ≤ M ^ 2 * J := hM2.trans (Nat.le_mul_of_pos_right _ hJ)
  have hM25 : M ^ 2 ≤ M ^ 5 := Nat.pow_le_pow_right hM1 (by omega)
  have hJ3 : J ≤ J ^ 3 := Nat.le_self_pow (by omega) _
  -- the space of the universal run, and the encoded result
  have hS : A + (n + n) + (runBound D N J + (2 * D + 1 + (2 * N + 1 + (n + 1)))) ≤
      209 * (M ^ 2 * J) := by
    have : A + (n + n) + (2 * D + 1 + (2 * N + 1 + (n + 1))) ≤ 9 * M := by omega
    nlinarith
  have hE' : E + 1 ≤ 210 * (cO + 1) * (M ^ 2 * J) := by
    have h₁ : E ≤ cO * (209 * (M ^ 2 * J) + 1) := hE.trans (Nat.mul_le_mul_left _ (by omega))
    have h₂ : 1 ≤ M ^ 2 * J := le_trans hM1 hMM2
    nlinarith
  have hM2J : M ^ 2 * J ≤ M ^ 5 * J := Nat.mul_le_mul_right _ hM25
  have hM5J : M ^ 5 * J ≤ M ^ 5 * J ^ 3 := Nat.mul_le_mul_left _ hJ3
  constructor
  · have hO2 : (E + 1) ^ 2 ≤ 44100 * (cO + 1) ^ 2 * (M ^ 5 * J ^ 3) := by
      calc (E + 1) ^ 2 ≤ (210 * (cO + 1) * (M ^ 2 * J)) ^ 2 := Nat.pow_le_pow_left hE' 2
        _ = 44100 * (cO + 1) ^ 2 * (M ^ 4 * J ^ 2) := by ring
        _ ≤ 44100 * (cO + 1) ^ 2 * (M ^ 5 * J ^ 3) := Nat.mul_le_mul_left _
            (Nat.mul_le_mul (Nat.pow_le_pow_right hM1 (by omega))
              (Nat.pow_le_pow_right hJ (by omega)))
    have hIn2 : (2 * D + 1 + (2 * N + 1 + (n + 1)) + 1) ^ 2 ≤ 49 * (M ^ 5 * J ^ 3) := by
      have h₁ : 2 * D + 1 + (2 * N + 1 + (n + 1)) + 1 ≤ 7 * M := by omega
      have h₂ : M ^ 2 ≤ M ^ 5 * J ^ 3 :=
        hM25.trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos hJ))
      calc _ ≤ (7 * M) ^ 2 := Nat.pow_le_pow_left h₁ 2
        _ = 49 * M ^ 2 := by ring
        _ ≤ 49 * (M ^ 5 * J ^ 3) := Nat.mul_le_mul_left _ h₂
    have hA : A + (n + n) ≤ M ^ 5 * J ^ 3 := by
      have h₁ : A + (n + n) ≤ M := by omega
      have h₂ : M ≤ M ^ 5 * J ^ 3 :=
        (hM2.trans hM25).trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos hJ))
      omega
    have hU₁' : (J + 1) * (stepBound D N J + runBound D N J + (n + 1 + 1) ^ 2) ≤
        100000 * (M ^ 5 * J ^ 3) := hU₁.trans (le_of_eq (by ring))
    rw [hK]
    generalize M ^ 5 * J ^ 3 = X at hA hU₁' hIn2 hO2 ⊢
    linarith
  · have hY : (cO + 1) * (M ^ 2 * J) ≤ (cO + 1) ^ 2 * (M ^ 5 * J) :=
      Nat.mul_le_mul (Nat.le_self_pow two_ne_zero _) hM2J
    rw [hK]
    generalize M ^ 2 * J = Z at hS hE' hM2J hY ⊢
    generalize M ^ 5 * J = W at hM2J hY ⊢
    linarith

/-- **The diagonal is decidable in exponential time**, within time `O(2 ^ (4 * n))` and space
`O(2 ^ (2 * n))` on inputs of length `n`, charging decoding, the symbols, the clock, the universal
run and the test. -/
theorem computableTidilyInO_diagonal :
    ComputableTidilyInO diagonal encBits encBool (fun x => 2 ^ (4 * x.length))
      fun x => 2 ^ (2 * x.length) := by
  obtain ⟨dd, ed, hdec⟩ := exists_computableTidilyInDegree_decodeDesc
  have hu : ComputableTidilyInDegree unframe encBits encBits 1 1 :=
    .of_linear (.of_unframe fun _ => rfl)
  have hdesc := (hdec.comp hu).inO
  have hsym := computableTidilyInDegree_map_boolSym.inO_one
  have hclock := (ComputableTidilyInDegree.two_pow_length encBits).inO_one
  have hpre := hdesc.prod (hsym.prod hclock)
  have hU := computableTidilyInO_universal.comp hpre
  have h := computableTidilyInO_verdict.comp hU
  -- the sizes of the decoded description and of the result
  obtain ⟨cD, hcD⟩ := hdesc.length_le
  obtain ⟨cO, hcO⟩ := hU.length_le
  -- one power of two absorbs every polynomial factor
  obtain ⟨C, hC⟩ := exists_le_mul_two_pow
    (p := fun n => (cD * ((n + 1) ^ max 1 (1 * dd) + 1) + (n + 1) ^ max 1 (1 * dd) + 4 * n + 2) ^ 5)
    (by fun_prop)
  set K := 100100 + 44100 * (cO + 1) ^ 2 with hK
  have hbounds (x : List Bool) := by
    have hL : (encNat (2 ^ x.length)).length = x.length + 1 := by
      rw [encNat_two_pow, List.length_append, List.length_replicate, List.length_singleton]
    have hN : (encList encUnary (x.map boolSym)).length ≤ 3 * x.length :=
      (length_encList_le encUnary _ (b := 1) fun s hs => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
        cases b
        · exact Nat.zero_le _
        · exact le_rfl).trans (by rw [List.length_map]; omega)
    have hE := hcO x
    simp only [Function.comp_apply, encBits, Function.Embedding.refl_apply] at hE
    exact diagonal_bounds_aux
      (I := (eIn (decodeDesc (unframe x), x.map boolSym, 2 ^ x.length)).length) Nat.one_le_two_pow
      (hcD x) hN hL (by rw [length_encPair, length_encPair]; rfl) rfl hK hE
  refine h.mono (K * C) (fun x => ?_) fun x => ?_
  · obtain ⟨h₁, -⟩ := hbounds x
    simp only [Function.comp_apply, encBits, Function.Embedding.refl_apply] at h₁ ⊢
    have hJ4 : 2 ^ (4 * x.length) = 2 ^ x.length * (2 ^ x.length) ^ 3 := by
      rw [← pow_succ', ← pow_mul]; ring_nf
    have := hC x.length
    calc _ ≤ K * (_ ^ 5 * (2 ^ x.length) ^ 3) := h₁
      _ ≤ K * (C * 2 ^ x.length * (2 ^ x.length) ^ 3) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ this)
      _ ≤ K * C * (2 ^ (4 * x.length) + 1) := by rw [hJ4]; nlinarith
  · obtain ⟨-, h₂⟩ := hbounds x
    simp only [Function.comp_apply, encBits, Function.Embedding.refl_apply] at h₂ ⊢
    have hJ2 : 2 ^ (2 * x.length) = 2 ^ x.length * 2 ^ x.length := by rw [two_mul, pow_add]
    have := hC x.length
    calc _ ≤ K * (_ ^ 5 * 2 ^ x.length) := h₂
      _ ≤ K * (C * 2 ^ x.length * 2 ^ x.length) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ this)
      _ ≤ K * C * (2 ^ (2 * x.length) + 1) := by rw [hJ2]; nlinarith

end Cslib.Complexity
