/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.CircuitCounting
public import Complexity.Computability.Circuit.Boolean.Iteration.InputTime
public import Complexity.Computability.Circuit.Boolean.Iteration.Remainder
public import Mathlib.Data.Nat.ModEq
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The modular-counter permutation: exponential lower bounds, typical powers, and remainders

On `2 k` bits split into a `k`-bit modulus `a` and a `k`-bit state `b`, `ModulusCounter.power T`
advances `b` to `(b + T) % a` whenever `0 < a` and `b < a`, and fixes all other states (`advance`).
For `T = 1`, this defines a permutation `counterStep k = ModulusCounter.power 1` computed by a
native De Morgan circuit of linear size at most `50 * k + 20 ≤ 50 * (k + 1)`
(`counterStep_circuit`, `ModulusCounter.exists_linear_circuit`).

Every active modulus `1 ≤ a ≤ 2 ^ k - 1` divides `ModulusCounter.period k = lcm(1, …, 2 ^ k - 1)`,
and distinct exponents below `ModulusCounter.period k` give distinct Boolean functions
(`ModulusCounter.powers_injective`). By Chebyshev's lower bound on `lcmUpto (2 ^ k - 1)` and the
ordered-syntax circuit count from `CircuitCounting.lean`, for every `k ≥ 64`:
* some exponent `T < ModulusCounter.period k` requires more than `lowerBudget k =
  2 ^ k / (1024 * (k + 1))` gates (`exists_hard_counter_power`, `counter_power_lower_bound`),
  matching the `2 ^ Θ(n)` fixed-power upper bound up to the constant factor in the exponent;
* at most a `2 ^ (-2 ^ (k - 1))` fraction of exponents below `ModulusCounter.period k` have
  circuits of size at most `lowerBudget k` (`almost_every_counter_power`,
  `almost_all_counter_powers_hard`);
* computing `ModulusCounter.power T` is equivalent up to `O(k)` gates to computing the fixed-integer
  remainder `x ↦ T % x` on `k`-bit moduli (`ModulusCounter.remainder_of_power`,
  `ModulusCounter.power_of_remainder`, `counter_powers_compute_remainders`), and variable-time
  iteration of `counterStep k` is equivalent up to `O(k)` gates to `m`-bit division remainder
  (`variable_time_counter_iff_remainder`);
* any exponent `T < 2 ^ m` has a power circuit of size at most `110 * (m + 1) * (k + 1)` via
  streaming remainders (`ModulusCounter.short_power_circuit`), so every hard power requires an
  exponent of binary length `m = Ω(2 ^ k / k ^ 2)`
  (`ModulusCounter.hard_power_requires_long_exponent`,
  `ModulusCounter.hard_power_exponent_capacity`).

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.advance`: advance `b` by `T` modulo `a` when
  `0 < a` and `b < a`.
* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.power`: `T`-step modular counter map on
  `BitString (k + k)`.
* `Cslib.Circuits.Boolean.Iteration.counterStep`: single-step modular counter permutation.
* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.period`: `Nat.lcmUpto (2 ^ k - 1)`.
* `Cslib.Circuits.Boolean.Iteration.easyCounterPowers`: exponents below `period k` computable with
  at most `q` gates.
* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.remainder`: fixed-integer remainder on `k`-bit
  words.

## Main results

* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.powers_injective`: powers below `period k` are
  pairwise distinct.
* `Cslib.Circuits.Boolean.Iteration.counterStep_circuit`: `counterStep k` has a circuit of size at
  most `50 * k + 20`.
* `Cslib.Circuits.Boolean.Iteration.counter_power_lower_bound`: for `k ≥ 64`, `counterStep k` has a
  power requiring more than `2 ^ k / (1024 * (k + 1))` gates.
* `Cslib.Circuits.Boolean.Iteration.almost_all_counter_powers_hard`: all but a
  `2 ^ (-2 ^ (k - 1))` fraction of powers below `period k` require more than `lowerBudget k` gates.
* `Cslib.Circuits.Boolean.Iteration.counter_powers_compute_remainders`,
  `Cslib.Circuits.Boolean.Iteration.variable_time_counter_iff_remainder`: equivalence between
  modular-counter powers and integer remainders.
* `Cslib.Circuits.Boolean.Iteration.counter_power_lower_bound_of_exp_length`: hard powers require
  exponentially many exponent bits.

## References

* Adapted from `lean/Proofs/{ModulusCounter,CounterCircuit,LowerBound,TypicalPowers,
  CounterRemainders,ExponentLength}.lean` in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open Cslib.Circuits Cslib.Circuits.Boolean

namespace ModulusCounter

/-! ### Modular counter semantics and period -/

/-- Advance `b` by `T` modulo `a` when `0 < a` and `b < a`; inactive pairs are fixed. -/
def advance (a b T : ℕ) : ℕ := if 0 < a ∧ b < a then (b + T) % a else b

@[simp] theorem advance_zero (a b : ℕ) : advance a b 0 = b := by
  by_cases h : 0 < a ∧ b < a
  · simp [advance, h, Nat.mod_eq_of_lt h.2]
  · simp [advance, h]

theorem advance_lt {a b U T : ℕ} (ha : a < U) (hb : b < U) : advance a b T < U := by
  unfold advance
  split_ifs with h
  · exact (Nat.mod_lt _ h.1).trans ha
  · exact hb

theorem advance_add (a b S T : ℕ) :
    advance a (advance a b S) T = advance a b (S + T) := by
  by_cases h : 0 < a ∧ b < a
  · simp only [advance, h, and_self, ite_true, Nat.mod_lt _ h.1]
    rw [Nat.mod_add_mod, Nat.add_assoc]
  · simp [advance, h]

variable {k : ℕ}

/-- The `k`-bit modulus word in the first `k` coordinates. -/
def leftWord (x : BitString (k + k)) : BitVec k := word fun i => x (Fin.castAdd k i)

/-- The `k`-bit counter state word in the last `k` coordinates. -/
def rightWord (x : BitString (k + k)) : BitVec k := word fun i => x (Fin.natAdd k i)

/-- Pack a `k`-bit modulus word and a `k`-bit counter state word into `BitString (k + k)`. -/
def pack (a b : BitVec k) : BitString (k + k) :=
  Fin.append (fun i : Fin k => a.getLsbD i.val) (fun i : Fin k => b.getLsbD i.val)

@[simp] theorem leftWord_pack (a b : BitVec k) : leftWord (pack a b) = a := by
  simp only [leftWord, pack, Fin.append_left, word_getLsbD]

@[simp] theorem rightWord_pack (a b : BitVec k) : rightWord (pack a b) = b := by
  simp only [rightWord, pack, Fin.append_right, word_getLsbD]

@[simp] theorem pack_words (x : BitString (k + k)) : pack (leftWord x) (rightWord x) = x := by
  funext bit
  induction bit using Fin.addCases with
  | left i => simp only [pack, leftWord, Fin.append_left, getLsbD_word]
  | right i => simp only [pack, rightWord, Fin.append_right, getLsbD_word]

/-- The `T`-step modular counter map on `BitString (k + k)`. -/
def power (T : ℕ) (x : BitString (k + k)) : BitString (k + k) :=
  pack (leftWord x) (BitVec.ofNat k (advance (leftWord x).toNat (rightWord x).toNat T))

@[simp] theorem power_zero (x : BitString (k + k)) : power 0 x = x := by
  simp [power]

theorem power_add (S T : ℕ) (x : BitString (k + k)) :
    power T (power S x) = power (S + T) x := by
  simp only [power, leftWord_pack, rightWord_pack, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (advance_lt (BitVec.isLt _) (BitVec.isLt _)), advance_add]

theorem iterate_power (T : ℕ) : (power (k := k) 1)^[T] = power T := by
  funext x
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Function.iterate_succ_apply', ih, power_add]

/-- The order `lcm(1, …, 2 ^ k - 1)` common to every active `k`-bit modular counter. -/
def period (k : ℕ) : ℕ := Nat.lcmUpto (2 ^ k - 1)

theorem modulus_dvd_period {a : ℕ} (ha : 0 < a) (haU : a < 2 ^ k) : a ∣ period k := by
  change a ∣ (Finset.Icc 1 (2 ^ k - 1)).lcm id
  apply Finset.dvd_lcm
  simpa only [Finset.mem_Icc] using (show 1 ≤ a ∧ a ≤ 2 ^ k - 1 by omega)

theorem power_period (x : BitString (k + k)) : power (period k) x = x := by
  unfold power advance
  split_ifs with h
  · have hd := modulus_dvd_period h.1 (BitVec.isLt (leftWord x))
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.add_zero,
      Nat.mod_mod, Nat.mod_eq_of_lt h.2]
    simp
  · simp

theorem power_bijective : Function.Bijective (power (k := k) 1) := by
  have hpos : 0 < period k := Nat.lcmUpto_pos _
  constructor
  · intro x y he
    have h := congrArg (power (period k - 1)) he
    simpa only [power_add, show 1 + (period k - 1) = period k by omega, power_period] using h
  · intro y
    exact ⟨power (period k - 1) y, by
      rw [power_add, Nat.sub_add_cancel hpos, power_period]⟩

/-- Different residues modulo `period k` give different Boolean functions. -/
theorem powers_injective :
    Function.Injective (fun T : Fin (period k) => power (k := k) T.val) := by
  intro S T he
  have hmod (a : ℕ) (ha : 0 < a) (haU : a < 2 ^ k) : S.val % a = T.val % a := by
    have hx := congrArg (fun f => (rightWord (f
      (pack (BitVec.ofNat k a) (BitVec.ofNat k 0)))).toNat) he
    have hslt := (Nat.mod_lt S.val ha).trans haU
    have htlt := (Nat.mod_lt T.val ha).trans haU
    simpa [power, advance, Nat.mod_eq_of_lt haU, ha, Nat.mod_eq_of_lt hslt,
      Nat.mod_eq_of_lt htlt] using hx
  have helper (S T : ℕ) (hST : S ≤ T)
      (hmod : ∀ a, 0 < a → a < 2 ^ k → S % a = T % a) : period k ∣ T - S := by
    change (Finset.Icc 1 (2 ^ k - 1)).lcm id ∣ T - S
    apply Finset.lcm_dvd
    intro a ha
    have ha' : 1 ≤ a ∧ a ≤ 2 ^ k - 1 := Finset.mem_Icc.mp ha
    have hm : Nat.ModEq a S T := hmod a (by omega) (by have := Nat.one_le_two_pow (n := k); omega)
    exact (Nat.modEq_iff_dvd' hST).mp hm
  apply Fin.ext
  rcases le_total S.val T.val with h | h
  · have hd := helper S.val T.val h hmod
    have hz := Nat.eq_zero_of_dvd_of_lt hd (by have := T.isLt; omega)
    omega
  · have hd := helper T.val S.val h (fun a ha hU => (hmod a ha hU).symm)
    have hz := Nat.eq_zero_of_dvd_of_lt hd (by have := S.isLt; omega)
    omega

/-! ### Linear-size step circuit -/

/-- Next counter word after one step: increment `b` modulo `a` when `b < a`. -/
def stepValue (a b : BitVec k) : BitVec k :=
  if b.ult a then if b + 1 = a then 0 else b + 1 else b

theorem stepValue_spec (a b : BitVec k) :
    stepValue a b = BitVec.ofNat k (advance a.toNat b.toNat 1) := by
  by_cases h : b.toNat < a.toNat
  · have ha : 0 < a.toNat := by omega
    have hs : b.toNat + 1 < 2 ^ k := by have := a.isLt; omega
    have hn : 1 < 2 ^ k := by have := a.isLt; omega
    have hsum : (b + 1).toNat = b.toNat + 1 := by
      simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hs]
    have he : b + 1 = a ↔ b.toNat + 1 = a.toNat := by
      rw [← BitVec.toNat_inj, hsum]
    simp only [stepValue, BitVec.ult, decide_eq_true_eq, h, ite_true, he, advance,
      ha, and_self]
    split_ifs with heq
    · apply BitVec.eq_of_toNat_eq
      simp [heq]
    · have hlt : b.toNat + 1 < a.toNat := by omega
      apply BitVec.eq_of_toNat_eq
      simp only [hsum, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hs]
  · simp only [stepValue, BitVec.ult, decide_eq_true_eq, h, ite_false, advance,
      and_false]
    simp

/-- Equality of two available `k`-bit words costs at most `6 * k + 1` gates. -/
theorem synthesis_word_eq {n : ℕ} (s : Set (BooleanFunction n)) (a b : BitString n → BitVec k)
    (ha : ∀ i : Fin k, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin k, (fun x => (b x).getLsbD i.val) ∈ s) :
    Synthesis interpretation s {fun x => decide (a x = b x)} (6 * k + 1) := by
  have h := synthesis_bits_eq s (fun x i => (a x).getLsbD i.val)
    (fun x i => (b x).getLsbD i.val)
    (by rintro _ ⟨i, rfl⟩; exact ha i) (by rintro _ ⟨i, rfl⟩; exact hb i)
  have heq (x : BitString n) :
      ((fun i : Fin k => (a x).getLsbD i.val) = fun i : Fin k => (b x).getLsbD i.val) ↔
        a x = b x :=
    ⟨fun h => BitVec.eq_of_getLsbD_eq fun i hi => congrFun h ⟨i, hi⟩,
      fun h => funext fun i => congrArg (fun v => v.getLsbD i.val) h⟩
  simpa only [heq] using h

/-- Synthesizing `stepValue (a x) (b x)` from available words and constants costs at most
`50 * k + 18` gates. -/
theorem synthesis_stepValue {n : ℕ} (src : Set (BooleanFunction n))
    (a b : BitString n → BitVec k)
    (ha : ∀ i : Fin k, (fun x => (a x).getLsbD i.val) ∈ src)
    (hb : ∀ i : Fin k, (fun x => (b x).getLsbD i.val) ∈ src)
    (hc : ∀ v : Bool, (fun _ : BitString n => v) ∈ src) :
    Synthesis interpretation src (wordWires fun x => stepValue (a x) (b x))
      (50 * k + 18) := by
  let inc := fun x => b x + 1
  have hadd := Synthesis.word_add (s := src) b (fun _ => (1 : BitVec k)) hb (fun _ => hc _)
  let src1 := src ∪ wordWires inc
  have hi (i : Fin k) : (fun x => (inc x).getLsbD i.val) ∈ src1 := Or.inr ⟨i, rfl⟩
  let equal := fun x => decide (inc x = a x)
  let active := fun x => (b x).ult (a x)
  have heq := synthesis_word_eq src1 inc a hi (fun i => Or.inl (ha i))
  have hlt := Synthesis.word_ult (s := src1) b a (fun i => Or.inl (hb i)) (fun i => Or.inl (ha i))
  let src2 := src1 ∪ ({equal} ∪ {active})
  let next := fun x => if equal x then (0 : BitVec k) else inc x
  have hm := Synthesis.word_mux (s := src2) (fun _ => (0 : BitVec k)) inc equal
    (Or.inr (Or.inl rfl)) (fun _ => Or.inl (Or.inl (hc _))) (fun i => Or.inl (hi i))
  let src3 := src2 ∪ wordWires next
  have hm' := Synthesis.word_mux (s := src3) next b active
    (Or.inl (Or.inr (Or.inr rfl))) (fun i => Or.inr ⟨i, rfl⟩)
    (fun i => Or.inl (Or.inl (Or.inl (hb i))))
  have hout := hadd.trans ((heq.union hlt).trans (hm.trans hm'))
  refine hout.mono Set.Subset.rfl ?_ (by omega)
  rintro _ ⟨i, rfl⟩
  refine ⟨i, ?_⟩
  funext x
  simp only [stepValue, active, next, equal, inc, decide_eq_true_eq]

/-- The single-step modular counter `power 1` has a De Morgan circuit of size at most
`50 * k + 20`. -/
theorem exists_linear_circuit (k : ℕ) :
    ∃ c : Circuit signature (k + k) (k + k),
      c.Computes interpretation (power (k := k) 1) ∧ c.size ≤ 50 * k + 20 := by
  let a := fun x : BitString (k + k) => leftWord x
  let b := fun x : BitString (k + k) => rightWord x
  let constants : Set (BooleanFunction (k + k)) := {fun _ => false, fun _ => true}
  let src := inputs (k + k) ∪ constants
  have hc (v : Bool) : (fun _ : BitString (k + k) => v) ∈ src := by
    cases v <;> simp [src, constants]
  have ha (i : Fin k) : (fun x => (a x).getLsbD i.val) ∈ src := by
    simpa only [a, leftWord, getLsbD_word] using
      (show (fun x : BitString (k + k) => x (Fin.castAdd k i)) ∈ src from Or.inl ⟨_, rfl⟩)
  have hb (i : Fin k) : (fun x => (b x).getLsbD i.val) ∈ src := by
    simpa only [b, rightWord, getLsbD_word] using
      (show (fun x : BitString (k + k) => x (Fin.natAdd k i)) ∈ src from Or.inl ⟨_, rfl⟩)
  have hconst : Synthesis interpretation (inputs (k + k)) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  have hstep := synthesis_stepValue src a b ha hb hc
  have hout := hconst.trans hstep
  have hall := (Synthesis.of_subset (I := interpretation)
    (s := inputs (k + k)) (t := inputs (k + k)) Set.Subset.rfl).union hout
  have hs : Synthesis interpretation (inputs (k + k))
      (wires (power (k := k) 1)) (50 * k + 20) := by
    apply hall.mono Set.Subset.rfl ?_ (by omega)
    rintro _ ⟨bit, rfl⟩
    induction bit using Fin.addCases with
    | left i =>
      left
      exact ⟨Fin.castAdd k i, by
        funext x
        simp only [power, pack, Fin.append_left, leftWord, getLsbD_word]⟩
    | right i =>
      right
      refine ⟨i, ?_⟩
      funext x
      simp only [power, pack, Fin.append_right]
      rw [← stepValue_spec]
  exact hs.exists_circuit_outputs

/-! ### Fixed-integer remainders and equivalence with counter powers -/

/-- Fixed-integer remainder `x ↦ T % x` on `k`-bit words, with `0` on modulus `0`. -/
def remainder (T : ℕ) (x : BitString k) : BitString k :=
  fun i => (BitVec.ofNat k (if (word x).toNat = 0 then 0 else T % (word x).toNat)).getLsbD i.val

theorem remainder_word (T : ℕ) (x : BitString k) :
    word (remainder T x) =
      BitVec.ofNat k (if (word x).toNat = 0 then 0 else T % (word x).toNat) := word_getLsbD _

/-- Add a precomputed residue `r = T % a` to `b` modulo `a` using `(k + 1)`-bit intermediate words
to avoid overflow. -/
def addResidue (a b r : BitVec k) : BitVec k :=
  let sum := b.setWidth (k + 1) + r.setWidth (k + 1)
  if b.ult a then
    (if sum.ult (a.setWidth (k + 1)) then sum else sum - a.setWidth (k + 1)).setWidth k
  else b

theorem addResidue_spec (a b r : BitVec k) (T : ℕ)
    (hr : 0 < a.toNat → r.toNat = T % a.toNat) :
    addResidue a b r = BitVec.ofNat k (advance a.toNat b.toNat T) := by
  have hwide (v : BitVec k) : (v.setWidth (k + 1)).toNat = v.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt
      (v.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ k)))]
  by_cases h : b.toNat < a.toNat
  · have ha : 0 < a.toNat := by omega
    have hrlt : r.toNat < a.toNat := by rw [hr ha]; exact Nat.mod_lt _ ha
    have hfit : b.toNat + r.toNat < 2 ^ (k + 1) := by
      rw [pow_succ]
      have := a.isLt
      omega
    have hsum : (b.setWidth (k + 1) + r.setWidth (k + 1)).toNat = b.toNat + r.toNat := by
      rw [BitVec.toNat_add, hwide, hwide, Nat.mod_eq_of_lt hfit]
    have hmod : (b.toNat + r.toNat) % a.toNat = (b.toNat + T) % a.toNat := by
      rw [hr ha, Nat.add_mod_mod]
    unfold addResidue
    simp only [BitVec.ult, h, decide_true, ite_true, hsum, hwide, decide_eq_true_eq]
    split_ifs with hs
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, hsum]
      simp only [advance, ha, h, and_self, ↓reduceIte, BitVec.toNat_ofNat, ← hmod,
        Nat.mod_eq_of_lt hs]
    · have hle : a.setWidth (k + 1) ≤ b.setWidth (k + 1) + r.setWidth (k + 1) := by
        change (a.setWidth (k + 1)).toNat ≤ _
        rw [hwide, hsum]
        omega
      have hsmall : b.toNat + r.toNat - a.toNat < a.toNat := by omega
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_sub_of_le hle, hsum, hwide]
      simp only [advance, ha, h, and_self, ↓reduceIte, BitVec.toNat_ofNat, ← hmod,
        Nat.mod_eq_sub_mod (show a.toNat ≤ b.toNat + r.toNat by omega), Nat.mod_eq_of_lt hsmall]
  · simp [addResidue, BitVec.ult, h, advance]

/-- Synthesizing `addResidue` from available words costs at most `100 * (k + 1)` gates. -/
theorem synthesis_addResidue {n : ℕ} (s : Set (BooleanFunction n)) (a b r : BitString n → BitVec k)
    (ha : wordWires a ⊆ s) (hb : wordWires b ⊆ s) (hr : wordWires r ⊆ s) :
    Synthesis interpretation s
      (wordWires fun x => addResidue (a x) (b x) (r x)) (100 * (k + 1)) := by
  let s0 := s ∪ {fun _ : BitString n => false}
  have hz : (fun _ : BitString n => false) ∈ s0 := Or.inr rfl
  have hw (v : BitString n → BitVec k) (hv : wordWires v ⊆ s) :=
    wordWires_setWidth_subset (v := k + 1) (s := s0) (fun _ h => Or.inl (hv h)) hz
  let sum := fun x => (b x).setWidth (k + 1) + (r x).setWidth (k + 1)
  let aw := fun x => (a x).setWidth (k + 1)
  have hadd := Synthesis.word_add (s := s0) _ _
    (fun i => hw b hb ⟨i, rfl⟩) (fun i => hw r hr ⟨i, rfl⟩)
  let s1 := s0 ∪ wordWires sum
  have hsum (i : Fin (k + 1)) : (fun x => (sum x).getLsbD i.val) ∈ s1 := Or.inr ⟨i, rfl⟩
  have haw (i : Fin (k + 1)) : (fun x => (aw x).getLsbD i.val) ∈ s1 :=
    Or.inl (hw a ha ⟨i, rfl⟩)
  have hsub := Synthesis.word_sub (s := s1) sum aw hsum haw
  have hlt := Synthesis.word_ult (s := s1) sum aw hsum haw
  let s2 := s1 ∪ (wordWires (fun x => sum x - aw x) ∪ {fun x => (sum x).ult (aw x)})
  let reduced := fun x => if (sum x).ult (aw x) then sum x else sum x - aw x
  have hred := Synthesis.word_mux (s := s2) sum (fun x => sum x - aw x)
    (fun x => (sum x).ult (aw x)) (Or.inr (Or.inr rfl))
    (fun i => Or.inl (hsum i)) (fun i => Or.inr (Or.inl ⟨i, rfl⟩))
  let s3 := s2 ∪ wordWires reduced
  have hre := wordWires_setWidth_subset (v := k) (s := s3) (value := reduced)
    (fun _ h => Or.inr h) (Or.inl (Or.inl (Or.inl hz)))
  have hactive := Synthesis.word_ult (s := s3) b a
    (fun i => Or.inl (Or.inl (Or.inl (Or.inl (hb ⟨i, rfl⟩)))))
    (fun i => Or.inl (Or.inl (Or.inl (Or.inl (ha ⟨i, rfl⟩)))))
  have hout := Synthesis.word_mux (s := s3 ∪ {fun x => (b x).ult (a x)})
    (fun x => (reduced x).setWidth k) b (fun x => (b x).ult (a x)) (Or.inr rfl)
    (fun i => Or.inl (hre ⟨i, rfl⟩))
    (fun i => Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hb ⟨i, rfl⟩))))))
  exact ((Synthesis.const (s := s) false).trans
    (hadd.trans ((hsub.union hlt).trans (hred.trans (hactive.trans hout))))).mono
      Set.Subset.rfl Set.Subset.rfl (by omega)

/-- A circuit for `power T` yields a circuit for `remainder T` with at most one extra gate. -/
theorem remainder_of_power (T : ℕ) (c : Circuit signature (k + k) (k + k))
    (hc : c.Computes interpretation (power T)) :
    ∃ out : Circuit signature k k,
      out.Computes interpretation (remainder T) ∧ out.size ≤ c.size + 1 := by
  let s := inputs k ∪ {fun _ : BitString k => false}
  let init := fun x : BitString k => pack (word x) (0 : BitVec k)
  have hi (i : Fin (k + k)) : (fun x => init x i) ∈ s := by
    induction i using Fin.addCases with
    | left i => simpa only [init, pack, Fin.append_left, getLsbD_word] using
        (show (fun x : BitString k => x i) ∈ s from Or.inl ⟨i, rfl⟩)
    | right i =>
      right
      funext x
      simp only [init, pack, Fin.append_right]
      simp
  have h := (Synthesis.const (s := inputs k) false).trans
    (Synthesis.circuit (I := interpretation) (s := s) c (fun i x => init x i) hi)
  have hout : wires (remainder (k := k) T) ⊆
      wires (fun x => c.eval interpretation (init x)) := by
    rintro _ ⟨i, rfl⟩
    refine ⟨Fin.natAdd k i, ?_⟩
    funext x
    change c.eval interpretation (init x) (Fin.natAdd k i) = remainder T x i
    rw [hc (init x)]
    dsimp only [power, init]
    rw [leftWord_pack, rightWord_pack]
    rw [show (0 : BitVec k).toNat = 0 by simp]
    simp only [pack, Fin.append_right]
    by_cases hz : (word x).toNat = 0
    · simp only [advance, remainder, hz, lt_self_iff_false, and_self, ite_false, ite_true]
    · simp only [advance, remainder, hz, Nat.pos_of_ne_zero hz, and_self, ite_true, ite_false,
        Nat.zero_add]
  obtain ⟨out, ho, hs⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
  exact ⟨out, ho, by nlinarith⟩

/-- A circuit for `remainder T` yields a circuit for `power T` with at most `100 * (k + 1)` extra
gates. -/
theorem power_of_remainder (T : ℕ) (c : Circuit signature k k)
    (hc : c.Computes interpretation (remainder T)) :
    ∃ out : Circuit signature (k + k) (k + k),
      out.Computes interpretation (power T) ∧ out.size ≤ c.size + 100 * (k + 1) := by
  let a := fun x : BitString (k + k) => leftWord x
  let b := fun x : BitString (k + k) => rightWord x
  let init := fun x : BitString (k + k) => fun i : Fin k => x (Fin.castAdd k i)
  let r := fun x => word (c.eval interpretation (init x))
  let s := inputs (k + k) ∪ wires (fun x => c.eval interpretation (init x))
  have ha : wordWires a ⊆ s := by
    rintro _ ⟨i, rfl⟩
    simpa only [a, leftWord, getLsbD_word] using
      (show (fun x : BitString (k + k) => x (Fin.castAdd k i)) ∈ s from Or.inl ⟨_, rfl⟩)
  have hb : wordWires b ⊆ s := by
    rintro _ ⟨i, rfl⟩
    simpa only [b, rightWord, getLsbD_word] using
      (show (fun x : BitString (k + k) => x (Fin.natAdd k i)) ∈ s from Or.inl ⟨_, rfl⟩)
  have hr : wordWires r ⊆ s := by
    rintro _ ⟨i, rfl⟩
    simpa only [r, getLsbD_word] using
      (show (fun x => c.eval interpretation (init x) i) ∈ s from Or.inr ⟨i, rfl⟩)
  have hs := synthesis_addResidue s a b r ha hb hr
  have hcirc := Synthesis.circuit (I := interpretation)
    (s := inputs (k + k)) c (fun i x => init x i) (fun i => ⟨Fin.castAdd k i, rfl⟩)
  have h : Synthesis interpretation (inputs (k + k))
      (s ∪ wordWires (fun x => addResidue (a x) (b x) (r x))) (c.size + 100 * (k + 1)) := by
    simpa only [s, wires, Set.union_assoc, Nat.zero_add] using
      (Synthesis.of_subset (I := interpretation)
        (s := inputs (k + k)) (t := inputs (k + k)) Set.Subset.rfl).union (hcirc.comp hs)
  have hspec (x : BitString (k + k)) : addResidue (a x) (b x) (r x) =
      BitVec.ofNat k (advance (a x).toNat (b x).toNat T) := by
    apply addResidue_spec
    intro ha
    change (word (c.eval interpretation (init x))).toNat = _
    rw [hc (init x), remainder_word]
    simp only [show word (init x) = a x from rfl,
      Nat.ne_of_gt ha, ite_false, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ((Nat.mod_lt _ ha).trans (a x).isLt)]
  have hout : wires (power (k := k) T) ⊆
      s ∪ wordWires (fun x => addResidue (a x) (b x) (r x)) := by
    rintro _ ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i =>
      left
      simpa only [power, pack, Fin.append_left] using ha ⟨i, rfl⟩
    | right i =>
      right
      refine ⟨i, ?_⟩
      funext x
      simp only [hspec, power, pack, Fin.append_right, a, b]
  obtain ⟨out, ho, hsize⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
  exact ⟨out, ho, by simpa only [Nat.zero_add] using hsize⟩

/-! ### Short-exponent upper bounds and exponent-length lower bounds -/

/-- Hardwiring `m` numerator bits into `bounded_modulus_remainder` and masking modulus zero gives a
circuit for `remainder T` of size linear in `m * (k + 1)`. -/
theorem short_remainder_circuit (k m T : ℕ) (hT : T < 2 ^ m) :
    ∃ out : Circuit signature k k,
      out.Computes interpretation (remainder T) ∧
      out.size ≤ m * (51 * (k + 1) + 4) + 10 * (k + 1) := by
  obtain ⟨rem, hrem, hsize⟩ := bounded_modulus_remainder m k
  let constants : Set (BooleanFunction k) := {fun _ => false, fun _ => true}
  let s := inputs k ∪ constants
  have hc (b : Bool) : (fun _ : BitString k => b) ∈ s := by cases b <;> simp [s, constants]
  let bits := fun i : Fin m => (BitVec.ofNat m T).getLsbD i.val
  let init := fun x : BitString k => Fin.append bits x
  let r := fun x => word (rem.eval interpretation (init x))
  have hi (i : Fin (m + k)) : (fun x => init x i) ∈ s := by
    induction i using Fin.addCases with
    | left i => simpa only [init, Fin.append_left] using hc (bits i)
    | right i => simpa only [init, Fin.append_right] using
        (show (fun x : BitString k => x i) ∈ s from Or.inl ⟨i, rfl⟩)
  have hr := Synthesis.circuit (I := interpretation) (s := s) rem (fun i x => init x i) hi
  have hz := Synthesis.word_eq_const (s := s) (fun x : BitString k => word x)
    (fun i => by simpa only [getLsbD_word] using
      (show (fun x : BitString k => x i) ∈ s from Or.inl ⟨i, rfl⟩)) 0
  let s1 := s ∪ (wires (fun x => rem.eval interpretation (init x)) ∪
    {fun x => decide (word x = (0 : BitVec k))})
  have hm := Synthesis.word_mux (s := s1) (fun _ => (0 : BitVec k)) r
    (fun x => decide (word x = (0 : BitVec k))) (Or.inr (Or.inr rfl))
    (fun _ => Or.inl (hc _)) (fun i => by
      simpa only [r, getLsbD_word] using
        (show (fun x => rem.eval interpretation (init x) i) ∈ s1 from
          Or.inr (Or.inl ⟨i, rfl⟩)))
  have hconst : Synthesis interpretation (inputs k) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  have h := hconst.trans ((hr.union hz).trans hm)
  have hval (x : BitString k) :
      (if decide (word x = (0 : BitVec k)) then (0 : BitVec k) else r x) =
        word (remainder T x) := by
    rw [remainder_word]
    have hzero : word x = (0 : BitVec k) ↔ (word x).toNat = 0 := by
      rw [← BitVec.toNat_inj]
      simp
    simp only [decide_eq_true_eq, hzero]
    split_ifs with h0
    · simp
    · have hp : 0 < (word x).toNat := Nat.pos_of_ne_zero h0
      have hspec := hrem (init x)
      simp only [init, Fin.append_right, Fin.append_left, bits, word_getLsbD,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hT] at hspec
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((Nat.mod_lt _ hp).trans (word x).isLt)]
      exact hspec hp
  have hout : wires (remainder (k := k) T) ⊆
      wordWires (fun x => if decide (word x = (0 : BitVec k)) then 0 else r x) := by
    rintro _ ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    funext x
    simp only [hval, getLsbD_word]
  obtain ⟨out, ho, hs⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
  exact ⟨out, ho, by nlinarith⟩

/-- A fixed exponent `T < 2 ^ m` gives a circuit for `power T` of size at most
`110 * (m + 1) * (k + 1)`. -/
theorem short_power_circuit (k m T : ℕ) (hT : T < 2 ^ m) :
    ∃ out : Circuit signature (k + k) (k + k),
      out.Computes interpretation (power T) ∧
      out.size ≤ 110 * (m + 1) * (k + 1) := by
  obtain ⟨rem, hr, hs⟩ := short_remainder_circuit k m T hT
  obtain ⟨out, ho, hb⟩ := power_of_remainder T rem hr
  refine ⟨out, ho, ?_⟩
  have hm : 4 * m ≤ 4 * m * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

/-- Any exponent whose counter power requires more than `lowerBudget k` gates needs
`lowerBudget k < 110 * (m + 1) * (k + 1)`. -/
theorem hard_power_requires_long_exponent (k m T : ℕ) (hT : T < 2 ^ m)
    (hard : ∀ c : Circuit signature (k + k) (k + k),
      c.Computes interpretation (power T) → lowerBudget k < c.size) :
    lowerBudget k < 110 * (m + 1) * (k + 1) := by
  obtain ⟨out, ho, hs⟩ := short_power_circuit k m T hT
  exact (hard out ho).trans_le hs

/-- Explicit exponential lower bound on the binary length `m` of any hard exponent `T < 2 ^ m`. -/
theorem hard_power_exponent_capacity (k m T : ℕ) (hT : T < 2 ^ m)
    (hard : ∀ c : Circuit signature (k + k) (k + k),
      c.Computes interpretation (power T) → lowerBudget k < c.size) :
    2 ^ k < 112640 * (m + 1) * (k + 1) ^ 2 := by
  have h := hard_power_requires_long_exponent k m T hT hard
  change 2 ^ k / (1024 * (k + 1)) < _ at h
  have hn := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 1024 * (k + 1))).mp h
  nlinarith

end ModulusCounter

/-! ### Top-level counter definitions, lower bounds, and typical powers -/

variable {k : ℕ}

/-- The `k`-bit modulus word of a `2 k`-bit counter state. -/
abbrev modulusWord (x : BitString (k + k)) : BitVec k := ModulusCounter.leftWord x

/-- The `k`-bit counter value word of a `2 k`-bit counter state. -/
abbrev stateWord (x : BitString (k + k)) : BitVec k := ModulusCounter.rightWord x

/-- The modulus as a natural number. -/
def counterModulus (x : BitString (k + k)) : ℕ := (modulusWord x).toNat

/-- Single-step modular counter transition on natural numbers. -/
def counterStepValue (a b : ℕ) : ℕ := ModulusCounter.advance a b 1

/-- Single-step modular counter permutation on `BitString (k + k)`. -/
def counterStep (k : ℕ) : BitString (k + k) → BitString (k + k) :=
  ModulusCounter.power (k := k) 1

/-- Next counter word after one step. -/
abbrev nextCounterWord (a b : BitVec k) : BitVec k := ModulusCounter.stepValue a b

/-- Coordinate bits of `nextCounterWord (modulusWord x) (stateWord x)`. -/
def counterNextBits (x : BitString (k + k)) : BitString k :=
  fun i => (nextCounterWord (modulusWord x) (stateWord x)).getLsbD i.val

theorem counterModulus_eq_of_eq {x y : BitString (k + k)}
    (h : (fun i => x (Fin.castAdd k i)) = fun i => y (Fin.castAdd k i)) :
    counterModulus x = counterModulus y :=
  congrArg (fun z => (word z).toNat) h

theorem counterStep_preserve_modulus (x : BitString (k + k)) :
    counterModulus (counterStep k x) = counterModulus x := by
  simp [counterModulus, counterStep, modulusWord, ModulusCounter.power]

theorem counterStepValue_iterate (a b T : ℕ) :
    (counterStepValue a)^[T] b = ModulusCounter.advance a b T := by
  induction T generalizing b with
  | zero => simp [ModulusCounter.advance_zero]
  | succ T ih =>
    rw [Function.iterate_succ_apply, ih, counterStepValue, ModulusCounter.advance_add,
      Nat.add_comm 1 T]

theorem counterStep_iterate_toNat (T : ℕ) (x : BitString (k + k)) :
    (stateWord ((counterStep k)^[T] x)).toNat =
      ModulusCounter.advance (modulusWord x).toNat (stateWord x).toNat T := by
  rw [counterStep, ModulusCounter.iterate_power]
  simp only [stateWord, modulusWord, ModulusCounter.power, ModulusCounter.rightWord_pack,
    BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (ModulusCounter.advance_lt (BitVec.isLt _) (BitVec.isLt _))

/-- Two functions are distinct on a domain `S` if they disagree on at least one point of `S`. -/
def DistinctOn {α β : Type*} (S : Set α) (f g : α → β) : Prop :=
  ∃ x ∈ S, f x ≠ g x

/-- Distinct exponents below `ModulusCounter.period k` produce distinct counter powers. -/
theorem counter_power_DistinctOn {S T : ℕ} (hS : S < ModulusCounter.period k)
    (hT : T < ModulusCounter.period k) (hne : S ≠ T) :
    DistinctOn Set.univ ((counterStep k)^[S]) ((counterStep k)^[T]) := by
  classical
  by_contra h
  simp only [DistinctOn, Set.mem_univ, true_and, not_exists, not_not] at h
  have heq : ModulusCounter.power (k := k) S = ModulusCounter.power (k := k) T := by
    rw [← ModulusCounter.iterate_power S, ← ModulusCounter.iterate_power T]
    exact funext h
  exact hne (Fin.val_eq_of_eq (ModulusCounter.powers_injective
    (a₁ := ⟨S, hS⟩) (a₂ := ⟨T, hT⟩) heq))

alias counter_powers_injective := ModulusCounter.powers_injective

theorem counter_family_card (k : ℕ) :
    (Finset.univ.image (fun T : Fin (ModulusCounter.period k) =>
      ModulusCounter.power (k := k) T.val)).card = ModulusCounter.period k := by
  rw [Finset.card_image_of_injective _ ModulusCounter.powers_injective, Finset.card_univ,
    Fintype.card_fin]

alias synthesis_nextCounterWord := ModulusCounter.synthesis_stepValue

/-- The single-step modular counter `counterStep k` has a De Morgan circuit of size at most
`50 * k + 20`. -/
theorem counterStep_circuit (k : ℕ) :
    ∃ c : Circuit signature (k + k) (k + k),
      c.Computes interpretation (counterStep k) ∧ c.size ≤ 50 * k + 20 :=
  ModulusCounter.exists_linear_circuit k

/-- The De Morgan description budget for `lowerBudget k` gates is strictly smaller than
`ModulusCounter.period k` for `k ≥ 64`. -/
theorem description_budget_lt_period (k : ℕ) (hk : 64 ≤ k) :
    signature.orderedBudget (k + k) (k + k) (lowerBudget k) < ModulusCounter.period k := by
  let q := lowerBudget k
  let E := 3 * q + (k + 2) * (2 * q + (k + k) + 1)
  have hb : signature.orderedBudget (k + k) (k + k) q ≤ 2 ^ E :=
    boolean_orderedBudget_le_pow _ _ _ _ (lowerBudget_wire_bound k hk)
  have he : E + k < 2 ^ k - 1 := lowerBudget_description_exponent k hk
  have hp : 2 ^ (E + k) < 2 ^ (2 ^ k - 1) := Nat.pow_lt_pow_right (by decide) he
  have hl := Chebyshev.two_pow_le_mul_lcmUpto (2 ^ k - 1)
  have hN : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [Nat.sub_add_cancel hN] at hl
  have hh := (Nat.mul_le_mul_right (2 ^ k) hb).trans_lt
    (by rw [← pow_add]; exact hp)
  have hh' := hh.trans_le hl
  change _ < 2 ^ k * ModulusCounter.period k at hh'
  nlinarith

/-- For every `k ≥ 64`, some exponent `T < ModulusCounter.period k` requires more than
`lowerBudget k` gates. -/
theorem exists_hard_counter_power (k : ℕ) (hk : 64 ≤ k) :
    ∃ T < ModulusCounter.period k,
      ∀ out : Circuit signature (k + k) (k + k),
        out.Computes interpretation (ModulusCounter.power (k := k) T) →
          lowerBudget k < out.size := by
  classical
  let family := Finset.univ.image (fun T : Fin (ModulusCounter.period k) =>
    ModulusCounter.power (k := k) T.val)
  have hcard : family.card = ModulusCounter.period k := counter_family_card k
  obtain ⟨target, ht, hh⟩ := Circuit.exists_hard_in_family (G := lowerBudget k)
    interpretation family (by rw [hcard]; exact description_budget_lt_period k hk)
  obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp ht
  refine ⟨T.val, T.isLt, fun out hcomp => ?_⟩
  by_contra hn
  exact hh out (by omega) hcomp

alias exists_hard_counter_power_below := exists_hard_counter_power

/-- **Matching exponential lower bound.** For every `k ≥ 64`, there is a bijective circuit `c` on
`2 k` bits of size at most `50 * (k + 1)` with a power `c^[T]` (`T < ModulusCounter.period k`)
requiring more than `2 ^ k / (1024 * (k + 1))` gates. -/
theorem matching_lower_bound (k : ℕ) (hk : 64 ≤ k) :
    ∃ c : Circuit signature (k + k) (k + k),
      c.size ≤ 50 * (k + 1) ∧ Function.Bijective (c.eval interpretation) ∧
      ∃ T < ModulusCounter.period k,
        ∀ out : Circuit signature (k + k) (k + k),
          out.Computes interpretation (c.eval interpretation)^[T] →
            2 ^ k / (1024 * (k + 1)) < out.size := by
  obtain ⟨c, hc, hs⟩ := ModulusCounter.exists_linear_circuit k
  obtain ⟨T, hT, hh⟩ := exists_hard_counter_power k hk
  have he : c.eval interpretation = ModulusCounter.power (k := k) 1 := funext hc
  refine ⟨c, by omega, he ▸ ModulusCounter.power_bijective, T, hT, ?_⟩
  intro out hout
  rw [he, ModulusCounter.iterate_power] at hout
  exact hh out hout

alias counter_power_lower_bound := matching_lower_bound

/-- Exponents below `ModulusCounter.period k` whose power has a circuit of size at most `q`. -/
noncomputable def easyCounterPowers (k q : ℕ) : Finset (Fin (ModulusCounter.period k)) := by
  classical
  exact Finset.univ.filter fun T => ModulusCounter.power (k := k) T.val ∈
    Circuit.functionsAtMost interpretation (k + k) (k + k) q

alias badExponents := easyCounterPowers

/-- Exponents below `ModulusCounter.period k` whose power requires more than `q` gates. -/
noncomputable def hardCounterPowers (k q : ℕ) : Finset (Fin (ModulusCounter.period k)) := by
  classical
  exact Finset.univ \ easyCounterPowers k q

alias goodExponents := hardCounterPowers

theorem mem_easyCounterPowers (k q : ℕ) (T : Fin (ModulusCounter.period k)) :
    T ∈ easyCounterPowers k q ↔
      ∃ c : Circuit signature (k + k) (k + k),
        c.size ≤ q ∧ c.Computes interpretation (ModulusCounter.power T.val) := by
  classical
  simp only [easyCounterPowers, Finset.mem_filter, Finset.mem_univ, true_and,
    Circuit.mem_functionsAtMost_iff]

theorem easyCounterPowers_card_le (k q : ℕ) :
    (easyCounterPowers k q).card ≤ signature.orderedBudget (k + k) (k + k) q := by
  classical
  have hsub : (easyCounterPowers k q).image (fun T => ModulusCounter.power (k := k) T.val) ⊆
      Circuit.functionsAtMost interpretation (k + k) (k + k) q := by
    intro target ht
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_filter.mp hT).2
  calc
    _ = ((easyCounterPowers k q).image (fun T => ModulusCounter.power (k := k) T.val)).card :=
      (Finset.card_image_of_injective _ ModulusCounter.powers_injective).symm
    _ ≤ _ := (Finset.card_le_card hsub).trans
      (Circuit.card_functionsAtMost_le interpretation)

alias badExponents_card_le := easyCounterPowers_card_le

theorem goodExponents_card_ge (k q : ℕ) :
    ModulusCounter.period k - signature.orderedBudget (k + k) (k + k) q ≤
      (goodExponents k q).card := by
  have hcard : (easyCounterPowers k q).card + (goodExponents k q).card =
      ModulusCounter.period k := by
    classical
    have hsub : easyCounterPowers k q ⊆ Finset.univ := Finset.subset_univ _
    rw [goodExponents, hardCounterPowers, add_comm, Finset.card_sdiff_add_card_eq_card hsub,
      Finset.card_univ, Fintype.card_fin]
  have hle := easyCounterPowers_card_le k q
  omega

/-- The description budget at `lowerBudget k` leaves an additive margin of `2 ^ (k - 1)` in the
binary exponent. -/
theorem lowerBudget_description_margin (k : ℕ) (hk : 64 ≤ k) :
    let q := lowerBudget k
    3 * q + (k + 2) * (2 * q + (k + k) + 1) + k + 2 ^ (k - 1) ≤ 2 ^ k - 1 := by
  dsimp only
  have hq : lowerBudget k * (1024 * (k + 1)) ≤ 2 ^ k := Nat.div_mul_le_self _ _
  have hs := square_le_exponential k hk
  have hpoly : (k + 2) * (k + k + 1) + k + 2 ≤ 4 * (k + 2) ^ 2 := by nlinarith
  have hcoef : (2 * (k + 2) + 3) * 128 ≤ 1024 * (k + 1) := by omega
  have hq' := Nat.mul_le_mul_right (lowerBudget k) hcoef
  have htotal : 128 * (3 * lowerBudget k +
      (k + 2) * (2 * lowerBudget k + (k + k) + 1) + k + 2) ≤ 5 * 2 ^ k := by
    nlinarith
  have hhalf : 2 ^ (k - 1) * 2 = 2 ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hN : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-- **Almost every counter power is hard.** At most a `2 ^ (-2 ^ (k - 1))` fraction of exponents
below `ModulusCounter.period k` have circuits of size at most `lowerBudget k`. -/
theorem almost_every_counter_power (k : ℕ) (hk : 64 ≤ k) :
    (easyCounterPowers k (lowerBudget k)).card * 2 ^ (2 ^ (k - 1)) ≤
      ModulusCounter.period k := by
  let E := 3 * lowerBudget k + (k + 2) * (2 * lowerBudget k + (k + k) + 1)
  have heasy : (easyCounterPowers k (lowerBudget k)).card ≤ 2 ^ E :=
    (easyCounterPowers_card_le k _).trans
      (boolean_orderedBudget_le_pow _ _ _ _ (lowerBudget_wire_bound k hk))
  have he : E + 2 ^ (k - 1) + k ≤ 2 ^ k - 1 := by
    have := lowerBudget_description_margin k hk
    dsimp only at this
    dsimp [E]
    omega
  have hl := Chebyshev.two_pow_le_mul_lcmUpto (2 ^ k - 1)
  rw [Nat.sub_add_cancel (Nat.one_le_two_pow (n := k))] at hl
  have hscaled : ((easyCounterPowers k (lowerBudget k)).card * 2 ^ (2 ^ (k - 1))) * 2 ^ k ≤
      ModulusCounter.period k * 2 ^ k := by
    calc
      _ ≤ (2 ^ E * 2 ^ (2 ^ (k - 1))) * 2 ^ k := by gcongr
      _ = 2 ^ (E + 2 ^ (k - 1) + k) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (2 ^ k - 1) := Nat.pow_le_pow_right (by decide) he
      _ ≤ _ := by simpa only [ModulusCounter.period, Nat.mul_comm] using hl
  exact Nat.le_of_mul_le_mul_right hscaled (by positivity)

alias almost_all_counter_powers_hard := almost_every_counter_power

/-- For `k ≥ 64`, more than half of the exponents below `ModulusCounter.period k` lie in
`goodExponents k (lowerBudget k)`. -/
theorem counter_powers_average_complexity (k : ℕ) (hk : 64 ≤ k) :
    ModulusCounter.period k < 2 * (goodExponents k (lowerBudget k)).card := by
  have hcard : (easyCounterPowers k (lowerBudget k)).card +
      (goodExponents k (lowerBudget k)).card = ModulusCounter.period k := by
    classical
    have hsub : easyCounterPowers k (lowerBudget k) ⊆ Finset.univ := Finset.subset_univ _
    rw [goodExponents, hardCounterPowers, add_comm, Finset.card_sdiff_add_card_eq_card hsub,
      Finset.card_univ, Fintype.card_fin]
  have halmost := almost_every_counter_power k hk
  have hpow : 2 < 2 ^ (2 ^ (k - 1)) := by
    have hk1 : 1 < 2 ^ (k - 1) := Nat.one_lt_two_pow (by omega)
    exact (show 2 = 2 ^ 1 by rfl) ▸ Nat.pow_lt_pow_right (by decide) hk1
  have hpos : 0 < ModulusCounter.period k := Nat.lcmUpto_pos _
  by_contra! hle
  have heasy_ge : ModulusCounter.period k ≤ 2 * (easyCounterPowers k (lowerBudget k)).card := by
    omega
  have h1 : 0 < (easyCounterPowers k (lowerBudget k)).card := by omega
  have h2 : 2 * (easyCounterPowers k (lowerBudget k)).card <
      (easyCounterPowers k (lowerBudget k)).card * 2 ^ (2 ^ (k - 1)) := by
    calc
      2 * (easyCounterPowers k (lowerBudget k)).card =
          (easyCounterPowers k (lowerBudget k)).card * 2 := Nat.mul_comm _ _
      _ < (easyCounterPowers k (lowerBudget k)).card * 2 ^ (2 ^ (k - 1)) :=
        Nat.mul_lt_mul_of_pos_left hpow h1
  omega

/-! ### Remainder helpers and variable-time equivalence -/

/-- Pack a `k`-bit modulus `x` with initial counter state `0`. -/
def counterInput (x : BitString k) : BitString (k + k) :=
  ModulusCounter.pack (word x) 0

/-- Extract the `k`-bit counter state from a `2 k`-bit state. -/
def counterOutput (y : BitString (k + k)) : BitString k :=
  fun i => y (Fin.natAdd k i)

/-- Fixed-integer remainder `x ↦ T % x` on `k`-bit strings (with `0` on modulus `0`). -/
abbrev counterRemainder (T : ℕ) (x : BitString k) : BitString k :=
  ModulusCounter.remainder T x

@[simp] theorem counterInput_modulus_toNat (x : BitString k) :
    (modulusWord (counterInput x)).toNat = (word x).toNat := by
  simp [counterInput, modulusWord]

@[simp] theorem counterInput_state_toNat (x : BitString k) :
    (stateWord (counterInput x)).toNat = 0 := by
  simp [counterInput, stateWord]

theorem counterRemainder_spec (T : ℕ) (x : BitString k) :
    counterOutput ((counterStep k)^[T] (counterInput x)) = counterRemainder T x := by
  rw [counterStep, ModulusCounter.iterate_power]
  funext i
  dsimp only [counterOutput, counterInput, ModulusCounter.power]
  rw [ModulusCounter.leftWord_pack, ModulusCounter.rightWord_pack]
  simp only [ModulusCounter.pack, Fin.append_right]
  by_cases hz : (word x).toNat = 0
  · simp [ModulusCounter.advance, counterRemainder, ModulusCounter.remainder, hz]
  · simp [ModulusCounter.advance, counterRemainder, ModulusCounter.remainder, hz,
      Nat.pos_of_ne_zero hz]

/-- Computing `ModulusCounter.power T` and computing `ModulusCounter.remainder T` are equivalent up
to linear additive overhead. -/
theorem counter_powers_compute_remainders (k T : ℕ) :
    (∀ c : Circuit signature (k + k) (k + k),
      c.Computes interpretation (ModulusCounter.power T) →
      ∃ out : Circuit signature k k,
        out.Computes interpretation (ModulusCounter.remainder T) ∧ out.size ≤ c.size + 1) ∧
    (∀ c : Circuit signature k k,
      c.Computes interpretation (ModulusCounter.remainder T) →
      ∃ out : Circuit signature (k + k) (k + k),
        out.Computes interpretation (ModulusCounter.power T) ∧
          out.size ≤ c.size + 100 * (k + 1)) :=
  ⟨ModulusCounter.remainder_of_power T, ModulusCounter.power_of_remainder T⟩

/-- Two-input remainder function on `m` numerator bits followed by `k` modulus bits, returning `0`
when the modulus is `0`. -/
def inputTimeRemainder (m k : ℕ) (x : BitString (m + k)) : BitString k :=
  ModulusCounter.remainder
    (word fun j : Fin m => x (Fin.castAdd k j)).toNat
    (fun i : Fin k => x (Fin.natAdd m i))

/-- Variable-time iteration of `counterStep k` for an `m`-bit input time is equivalent up to
`O(k)` gates to computing the `m`-bit remainder `inputTimeRemainder m k`. -/
theorem variable_time_counter_iff_remainder (m k : ℕ) :
    (∀ c : Circuit signature ((k + k) + m) (k + k),
      c.Computes interpretation (inputTimeIterate (counterStep k) m) →
      ∃ out : Circuit signature (m + k) k,
        out.Computes interpretation (inputTimeRemainder m k) ∧ out.size ≤ c.size + 1) ∧
    (∀ c : Circuit signature (m + k) k,
      c.Computes interpretation (inputTimeRemainder m k) →
      ∃ out : Circuit signature ((k + k) + m) (k + k),
        out.Computes interpretation (inputTimeIterate (counterStep k) m) ∧
          out.size ≤ c.size + 100 * (k + 1)) := by
  constructor
  · intro c hc
    let s := inputs (m + k) ∪ {fun _ : BitString (m + k) => false}
    let init := fun x : BitString (m + k) =>
      Fin.append (counterInput fun i : Fin k => x (Fin.natAdd m i))
        (fun j : Fin m => x (Fin.castAdd k j))
    have hi (i : Fin ((k + k) + m)) : (fun x => init x i) ∈ s := by
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i =>
          simpa only [init, Fin.append_left, counterInput, ModulusCounter.pack, getLsbD_word] using
            (show (fun x : BitString (m + k) => x (Fin.natAdd m i)) ∈ s from Or.inl ⟨_, rfl⟩)
        | right i =>
          right
          funext x
          simp only [init, Fin.append_left, counterInput, ModulusCounter.pack, Fin.append_right]
          simp
      | right j =>
        simpa only [init, Fin.append_right] using
          (show (fun x : BitString (m + k) => x (Fin.castAdd k j)) ∈ s from Or.inl ⟨_, rfl⟩)
    have h := (Synthesis.const (s := inputs (m + k)) false).trans
      (Synthesis.circuit (I := interpretation) (s := s) c (fun i x => init x i) hi)
    have hout : wires (inputTimeRemainder m k) ⊆
        wires (fun x => c.eval interpretation (init x)) := by
      rintro _ ⟨i, rfl⟩
      refine ⟨Fin.natAdd k i, ?_⟩
      funext x
      change c.eval interpretation (init x) (Fin.natAdd k i) =
        inputTimeRemainder m k x i
      rw [hc (init x)]
      simp only [inputTimeIterate, init, Fin.append_right, Fin.append_left]
      exact congrFun (counterRemainder_spec
        (word fun j : Fin m => x (Fin.castAdd k j)).toNat
        (fun i : Fin k => x (Fin.natAdd m i))) i
    obtain ⟨out, ho, hs⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
    exact ⟨out, ho, by omega⟩
  · intro c hc
    let a := fun x : BitString ((k + k) + m) =>
      ModulusCounter.leftWord fun i => x (Fin.castAdd m i)
    let b := fun x : BitString ((k + k) + m) =>
      ModulusCounter.rightWord fun i => x (Fin.castAdd m i)
    let init := fun x : BitString ((k + k) + m) =>
      Fin.append (fun j : Fin m => x (Fin.natAdd (k + k) j))
        (fun i : Fin k => x (Fin.castAdd m (Fin.castAdd k i)))
    let r := fun x => word (c.eval interpretation (init x))
    let s := inputs ((k + k) + m) ∪ wires (fun x => c.eval interpretation (init x))
    have ha : wordWires a ⊆ s := by
      rintro _ ⟨i, rfl⟩
      simpa only [a, ModulusCounter.leftWord, getLsbD_word] using
        (show (fun x : BitString ((k + k) + m) => x (Fin.castAdd m (Fin.castAdd k i))) ∈ s from
          Or.inl ⟨_, rfl⟩)
    have hb : wordWires b ⊆ s := by
      rintro _ ⟨i, rfl⟩
      simpa only [b, ModulusCounter.rightWord, getLsbD_word] using
        (show (fun x : BitString ((k + k) + m) => x (Fin.castAdd m (Fin.natAdd k i))) ∈ s from
          Or.inl ⟨_, rfl⟩)
    have hr : wordWires r ⊆ s := by
      rintro _ ⟨i, rfl⟩
      simpa only [r, getLsbD_word] using
        (show (fun x => c.eval interpretation (init x) i) ∈ s from Or.inr ⟨i, rfl⟩)
    have hs := ModulusCounter.synthesis_addResidue s a b r ha hb hr
    have hhi (i : Fin (m + k)) : (fun x => init x i) ∈ inputs ((k + k) + m) := by
      induction i using Fin.addCases with
      | left j =>
        exact ⟨Fin.natAdd (k + k) j, funext fun x => by simp [init]⟩
      | right i =>
        exact ⟨Fin.castAdd m (Fin.castAdd k i), funext fun x => by simp [init]⟩
    have hcirc := Synthesis.circuit (I := interpretation)
      (s := inputs ((k + k) + m)) c (fun i x => init x i) hhi
    have h : Synthesis interpretation (inputs ((k + k) + m))
        (s ∪ wordWires (fun x => ModulusCounter.addResidue (a x) (b x) (r x)))
        (c.size + 100 * (k + 1)) := by
      simpa only [s, wires, Set.union_assoc, Nat.zero_add] using
        (Synthesis.of_subset (I := interpretation)
          (s := inputs ((k + k) + m)) (t := inputs ((k + k) + m)) Set.Subset.rfl).union
          (hcirc.comp hs)
    have hspec (x : BitString ((k + k) + m)) :
        ModulusCounter.addResidue (a x) (b x) (r x) =
          BitVec.ofNat k (ModulusCounter.advance (a x).toNat (b x).toNat
            (word fun j : Fin m => x (Fin.natAdd (k + k) j)).toNat) := by
      apply ModulusCounter.addResidue_spec
      intro hpos
      change (word (c.eval interpretation (init x))).toNat = _
      rw [hc (init x), inputTimeRemainder, ModulusCounter.remainder_word]
      have hinit_m : (fun j : Fin m => init x (Fin.castAdd k j)) =
          fun j : Fin m => x (Fin.natAdd (k + k) j) := by
        funext j; simp [init]
      have hinit_k : word (fun i : Fin k => init x (Fin.natAdd m i)) = a x := by
        congr 1; funext i; simp [init]
      rw [hinit_m, hinit_k]
      simp only [Nat.ne_of_gt hpos, ite_false, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt ((Nat.mod_lt _ hpos).trans (a x).isLt)]
    have hout : wires (inputTimeIterate (counterStep k) m) ⊆
        s ∪ wordWires (fun x => ModulusCounter.addResidue (a x) (b x) (r x)) := by
      rintro _ ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left i =>
        left
        simpa only [inputTimeIterate, counterStep, ModulusCounter.iterate_power,
          ModulusCounter.power, ModulusCounter.pack, Fin.append_left] using ha ⟨i, rfl⟩
      | right i =>
        right
        refine ⟨i, ?_⟩
        funext x
        simp only [hspec, inputTimeIterate, counterStep, ModulusCounter.iterate_power,
          ModulusCounter.power, ModulusCounter.pack, Fin.append_right, a, b]
    obtain ⟨out, ho, hsize⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
    exact ⟨out, ho, by simpa only [Nat.zero_add] using hsize⟩

/-- All powers `ModulusCounter.power T` for `T < M` with `M ≤ ModulusCounter.period k` are
pairwise distinct. -/
theorem distinct_counter_powers_up_to {M : ℕ} (hM : M ≤ ModulusCounter.period k) :
    Function.Injective (fun T : Fin M => ModulusCounter.power (k := k) T.val) := by
  intro S T h
  have heq := ModulusCounter.powers_injective
    (a₁ := ⟨S.val, Nat.lt_of_lt_of_le S.isLt hM⟩)
    (a₂ := ⟨T.val, Nat.lt_of_lt_of_le T.isLt hM⟩) h
  exact Fin.ext (congrArg (fun a : Fin (ModulusCounter.period k) => a.val) heq)

/-- If `signature.orderedBudget (k + k) (k + k) q < M` and `M ≤ ModulusCounter.period k`, some
exponent `T < M` requires more than `q` gates. -/
theorem exists_hard_counter_power_up_to {M q : ℕ} (hM : M ≤ ModulusCounter.period k)
    (large : signature.orderedBudget (k + k) (k + k) q < M) :
    ∃ T < M, ∀ out : Circuit signature (k + k) (k + k),
      out.Computes interpretation (ModulusCounter.power (k := k) T) → q < out.size := by
  classical
  let family := Finset.univ.image (fun T : Fin M => ModulusCounter.power (k := k) T.val)
  have hcard : family.card = M := by
    rw [Finset.card_image_of_injective _ (distinct_counter_powers_up_to hM), Finset.card_univ,
      Fintype.card_fin]
  obtain ⟨target, ht, hh⟩ := Circuit.exists_hard_in_family (G := q)
    interpretation family (by rw [hcard]; exact large)
  obtain ⟨T, _, rfl⟩ := Finset.mem_image.mp ht
  refine ⟨T.val, T.isLt, fun out hcomp => ?_⟩
  by_contra hn
  exact hh out (by omega) hcomp

alias counter_power_lower_bound_of_exp_length := ModulusCounter.hard_power_exponent_capacity

alias subexponential_horizon_barrier := ModulusCounter.short_power_circuit

end Cslib.Circuits.Boolean.Iteration
