/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.AffineDisperser.Program
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Tactic.PolyTime
import Mathlib.Data.List.GetD

/-!
# The explicit affine disperser in polynomial time

The program `Cslib.AffineDisperser.explicitDisperserProgram` computes the explicit affine
disperser (`Cslib.AffineDisperser.explicitDisperserProgram_eq`); this file certifies it in the
polynomial-time calculus of tidy multi-tape machines, with input bits in `encBits` and natural
numbers in unary. All runtime sizes are polynomial in the input length `N`:

* the parameters (`⌊log₂ N⌋`, the primes in `(L, 4 L]` by trial division, the greedy choice and
  the field degree `n ≤ N + 1`) are unary arithmetic on numbers at most `N + 1`;
* each irreducible polynomial is found by exhaustive search over the codes below
  `2 ^ (4 L + 1) ≤ 2 (N + 1) ^ 2` (`Cslib.AffineDisperser.codeBound_le`), each tested by trial
  division with remainders computed by repeated multiplication by `X`;
* the multiplication table has `n ^ 3` entries, each a product over the prime factors of `n`;
* a field multiplication sums at most `n ^ 2` table entries, uniformly in the table
  (`Cslib.AffineDisperser.computableTidilyInPolyTime_fieldMul`); the `r` powers take at most
  `2 r` multiplications each, the elementary symmetric polynomial `r t` more, and the trace reads
  the diagonals of the table.

Every loop is certified with a bound on its intermediate states, so the certificate charges the
whole computation, including every field operation
(`Cslib.AffineDisperser.computableTidilyInPolyTime_explicitDisperser`). The exponent of the
polynomial is not computed.

## Main definitions

* `Cslib.AffineDisperser.selectStep`: one step of the greedy choice of primes, as a fold.
* `Cslib.AffineDisperser.encTable`: the encoding of multiplication tables.

## Main results

* `Cslib.AffineDisperser.computableTidilyInPolyTime_leastIrreducibleCode`: the search for the
  irreducible polynomials.
* `Cslib.AffineDisperser.computableTidilyInPolyTime_explicitTable`: the multiplication table.
* `Cslib.AffineDisperser.computableTidilyInPolyTime_traceSymCoords`: `traceSym 1 r t` in
  coordinates, uniformly in the multiplication table.
* `Cslib.AffineDisperser.computableTidilyInPolyTime_explicitDisperser`: the explicit disperser is
  computable in polynomial time.
* `Cslib.AffineDisperser.setOf_explicitDisperser_mem_P`: it decides a problem in `P`.

## References

* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.AffineDisperser

open Turing.MultiTapeTM ComputableTidilyInPolyTime Explicit

/-! ### Binary polynomials -/

/-- Multiplication by `X` modulo a binary polynomial, on coefficient lists. -/
@[fun_prop]
theorem computableTidilyInPolyTime_mulXMod :
    ComputableTidilyInPolyTime (fun p : List Bool × List Bool => mulXMod p.1 p.2)
      (encPair encBits encBits) encBits := by
  unfold mulXMod
  fun_prop

theorem length_mulXMod_le (g r : List Bool) : (mulXMod g r).length ≤ g.length - 1 :=
  List.length_take_le _ _

/-- The remainder modulo a binary polynomial, by a left fold over the coefficients whose state, the
current power of `X` and the partial remainder, never exceeds the degree of the modulus. -/
@[fun_prop]
theorem computableTidilyInPolyTime_modBits :
    ComputableTidilyInPolyTime (fun p : List Bool × List Bool => modBits p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hstep : ComputableTidilyInPolyTime
      (fun q : (List Bool × (List Bool × List Bool)) × Bool => modStep q.1.1 q.1.2 q.2)
      (encPair (encPair encBits (encPair encBits encBits)) encBool)
      (encPair encBits encBits) := by
    unfold modStep
    fun_prop
  have hinit : ComputableTidilyInPolyTime (fun p : List Bool × List Bool =>
      ((true :: List.replicate (p.1.length - 2) false).take (p.1.length - 1),
        List.replicate (p.1.length - 1) false))
      (encPair encBits encBits) (encPair encBits encBits) := by
    fun_prop
  have h := (foldlWith_spec (encA := encBool) (encL := encBits) (par := Prod.fst)
    (list := Prod.snd) (step := modStep) (fst encBits encBits) (snd encBits encBits) hinit hstep
    (fun p _ state => state.1.length ≤ p.1.length - 1 ∧ state.2.length ≤ p.1.length - 1)
    (fun p => by simp) (fun p consumed state value _ h => by
      refine ⟨length_mulXMod_le _ _, ?_⟩
      simp only [modStep]
      split_ifs
      · simp only [List.length_zipWith]
        omega
      · exact h.2)
    (size := fun p => 3 * p.1.length + 1) (.of_forall_le 3 1 fun p => by simp; omega)
    (fun p consumed state _ h => by simp [encPair_apply]; omega)).1
  exact (snd encBits encBits).comp h

/-- The binary digits of a unary natural. -/
theorem computableTidilyInPolyTime_bits_unary :
    ComputableTidilyInPolyTime Nat.bits encUnary encBits :=
  natBits.comp unary_to_binary

/-- The irreducibility test by trial division, on a unary code. -/
@[fun_prop]
theorem computableTidilyInPolyTime_isIrreducibleCode :
    ComputableTidilyInPolyTime isIrreducibleCode encUnary encBool := by
  unfold isIrreducibleCode
  have := computableTidilyInPolyTime_bits_unary
  fun_prop

/-- The exhaustive search for the least irreducible code below a unary bound. -/
@[fun_prop]
theorem computableTidilyInPolyTime_leastIrreducibleCode :
    ComputableTidilyInPolyTime (fun q : ℕ × ℕ => leastIrreducibleCode q.1 q.2)
      (encPair encUnary encUnary) encUnary := by
  unfold leastIrreducibleCode
  fun_prop

/-- The remainders of the powers of `X`. -/
@[fun_prop]
theorem computableTidilyInPolyTime_powerTable :
    ComputableTidilyInPolyTime powerTable encBits (encList encBits) := by
  unfold powerTable
  fun_prop


/-! ### Lists of unary naturals -/

/-- Take a unary number of elements of a framed list, by reversing and dropping. -/
theorem computableTidilyInPolyTime_take {α : Type} (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : List α × ℕ => p.1.take p.2)
      (encPair (encList enc) encUnary) (encList enc) := by
  have hrev := (listReverse enc).comp (fst (encList enc) encUnary)
  have hcount : ComputableTidilyInPolyTime (fun p : List α × ℕ => p.1.length - p.2)
      (encPair (encList enc) encUnary) encUnary :=
    unary_sub.comp (((length_list enc).comp (fst _ _)).prod (snd _ _))
  have h := (listReverse enc).comp ((dropUnary (encA := enc) (encL := encList enc)).comp
    (hrev.prod hcount))
  simpa only [Function.comp_def, ← List.reverse_take, List.reverse_reverse] using h

/-- The product of a computed list of positive unary naturals, when the product is polynomially
bounded: every partial product is at most the whole product. -/
theorem computableTidilyInPolyTime_prod_of_le {α : Type} {input : α ↪ List Bool} {list : α → List ℕ}
    (hlist : ComputableTidilyInPolyTime list input (encList encUnary))
    (hpos : ∀ a, ∀ p ∈ list a, 0 < p) {B : α → ℕ}
    (hB : PolyBounded (fun a => (input a).length) B) (hle : ∀ a, (list a).prod ≤ B a) :
    ComputableTidilyInPolyTime (fun a => (list a).prod) input encUnary := by
  have h := foldl' (encA := encUnary) (encL := encList encUnary) (step := fun s p => s * p)
    hlist (const 1) unary_mul hB (fun a i _ => by
      rw [encUnary_apply, List.length_replicate, ← List.prod_eq_foldl]
      refine le_trans ?_ (hle a)
      rw [← List.prod_take_mul_prod_drop (list a) i]
      exact Nat.le_mul_of_pos_right _
        (List.prod_pos fun p hp => hpos a p (List.mem_of_mem_drop hp)))
  simpa only [← List.prod_eq_foldl] using h

/-- Look up a computed index in a computed list of lists, with a fixed default; the element
encoding is that of the list. Restricting to lists of lists keeps this rule away from raw bit
strings, which have their own lookup rule. -/
@[fun_prop]
theorem computableTidilyInPolyTime_getD_list {α γ : Type} {input : α ↪ List Bool}
    {enc : List γ ↪ List Bool} {L : α → List (List γ)} {i : α → ℕ}
    (hL : ComputableTidilyInPolyTime L input (encList enc))
    (hi : ComputableTidilyInPolyTime i input encUnary) (d : List γ) :
    ComputableTidilyInPolyTime (fun a => (L a).getD (i a) d) input enc :=
  (listGetD (encA := enc) (encL := encList enc) d).comp (hL.prod hi)

/-! ### The parameters -/

/-- Primality by trial division. -/
theorem decide_prime_eq (p : ℕ) : decide p.Prime =
    (decide (2 ≤ p) && (List.range p).all fun m => decide (m < 2) || decide (p % m ≠ 0)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.prime_def_lt']
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, ne_eq, Nat.dvd_iff_mod_eq_zero]
  refine and_congr_right fun _ => ⟨fun h m hm => ?_, fun h m h2 hm => ?_⟩
  · by_cases h2 : m < 2
    · exact Or.inl h2
    · exact Or.inr (h m (by omega) hm)
  · exact (h m hm).resolve_left (by omega)

/-- Primality of a unary natural, by trial division. -/
@[fun_prop]
theorem computableTidilyInPolyTime_decide_prime :
    ComputableTidilyInPolyTime (fun p : ℕ => decide p.Prime) encUnary encBool := by
  simp_rw [decide_prime_eq]
  fun_prop

/-- The primes in `(a, b]`, from unary bounds. -/
@[fun_prop]
theorem computableTidilyInPolyTime_primesIoc :
    ComputableTidilyInPolyTime (fun q : ℕ × ℕ => primesIoc q.1 q.2)
      (encPair encUnary encUnary) (encList encUnary) := by
  simp_rw [primesIoc, List.range'_eq_map_range]
  fun_prop

/-- One step of the greedy choice of primes: the remaining budget and the primes chosen. -/
def selectStep (state : ℕ × List ℕ) (p : ℕ) : ℕ × List ℕ :=
  if p ≤ state.1 then (state.1 / p, state.2 ++ [p]) else state

theorem foldl_selectStep (T : ℕ) (ps chosen : List ℕ) :
    (ps.foldl selectStep (T, chosen)).2 = chosen ++ selectBelow T ps := by
  induction ps generalizing T chosen with
  | nil => simp [selectBelow]
  | cons p ps ih =>
    rw [List.foldl_cons, selectStep, selectBelow]
    split_ifs
    · rw [ih, List.append_assoc, List.singleton_append]
    · exact ih T chosen

/-- The greedy choice of primes below a unary budget. -/
@[fun_prop]
theorem computableTidilyInPolyTime_selectBelow :
    ComputableTidilyInPolyTime (fun q : ℕ × List ℕ => selectBelow q.1 q.2)
      (encPair encUnary (encList encUnary)) (encList encUnary) := by
  have hstep : ComputableTidilyInPolyTime
      (fun q : (ℕ × List ℕ) × ℕ => selectStep q.1 q.2)
      (encPair (encPair encUnary (encList encUnary)) encUnary)
      (encPair encUnary (encList encUnary)) := by
    unfold selectStep
    fun_prop
  have h := (foldl_spec (encA := encUnary) (encL := encList encUnary)
    (list := fun q : ℕ × List ℕ => q.2) (init := fun q => (q.1, []))
    (snd encUnary (encList encUnary)) (by fun_prop) hstep
    (fun q consumed state => state.1 ≤ q.1 ∧ state.2.Sublist consumed)
    (fun q => by simp) (fun q consumed state value _ h => by
      simp only [selectStep]
      split_ifs
      · exact ⟨(Nat.div_le_self _ _).trans h.1, h.2.append (List.Sublist.refl _)⟩
      · exact ⟨h.1, h.2.trans (List.sublist_append_left _ _)⟩)
    (size := fun q => (encPair encUnary (encList encUnary) q).length) .self
    (fun q consumed state hprefix h => by
      have hsub := ((h.2.trans hprefix.sublist).map fun a => 2 * (encUnary a).length + 1)
      have := hsub.sum_le_sum (fun _ _ => Nat.zero_le _)
      simp only [length_encPair, length_encList, encUnary_apply, List.length_replicate] at this ⊢
      omega)).1
  simpa only [Function.comp_def, foldl_selectStep, List.nil_append] using
    (snd encUnary (encList encUnary)).comp h

/-- The prime bound `L = ⌊⌊log₂ N⌋ / 3⌋` of unary `N`. -/
@[fun_prop]
theorem computableTidilyInPolyTime_primeBound :
    ComputableTidilyInPolyTime primeBound encUnary encUnary := by
  unfold primeBound
  fun_prop

/-- The primes of the field degree on `N` bits, `N` in unary. -/
@[fun_prop]
theorem computableTidilyInPolyTime_degreePrimes :
    ComputableTidilyInPolyTime degreePrimes encUnary (encList encUnary) := by
  unfold degreePrimes
  fun_prop

theorem selectBelow_zero {ps : List ℕ} (hps : ∀ p ∈ ps, 0 < p) : selectBelow 0 ps = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [selectBelow, ite_eq_right_iff.2 (by have := hps p List.mem_cons_self; omega)]
    exact ih fun q hq => hps q (List.mem_cons_of_mem _ hq)

theorem prod_degreePrimes_le (N : ℕ) : (degreePrimes N).prod ≤ N + 1 := by
  rcases Nat.eq_zero_or_pos (N / (Nat.log 2 N + 1) ^ 2) with hT | hT
  · rw [degreePrimes, hT, selectBelow_zero fun p hp => (mem_primesIoc.1 hp).2.2.pos]
    simp
  · exact (prod_selectBelow_le hT _).trans ((Nat.div_le_self _ _).trans (Nat.le_succ N))

/-- The field degree on `N` bits, `N` in unary: a product of at most `N + 1`. -/
@[fun_prop]
theorem computableTidilyInPolyTime_fieldDegree :
    ComputableTidilyInPolyTime fieldDegree encUnary encUnary := by
  have h := computableTidilyInPolyTime_prod_of_le computableTidilyInPolyTime_degreePrimes
    (fun N p hp => (prime_of_mem_degreePrimes hp).2.2.pos) (B := fun N => N + 1)
    (.of_forall_le 1 1 fun N => by simp) prod_degreePrimes_le
  simpa only [← fieldDegree_eq_prod] using h

/-- The number of blocks on `N` bits, `N` in unary. -/
@[fun_prop]
theorem computableTidilyInPolyTime_numBlocks :
    ComputableTidilyInPolyTime numBlocks encUnary encUnary := by
  unfold numBlocks
  fun_prop

/-- The degree of the elementary symmetric polynomial on `N` bits, `N` in unary. -/
@[fun_prop]
theorem computableTidilyInPolyTime_symDegree :
    ComputableTidilyInPolyTime symDegree encUnary encUnary := by
  unfold symDegree
  fun_prop

/-- The search range is polynomial: `2 ^ (4 L + 1) ≤ 2 (N + 1) ^ 2`, as `4 L ≤ 2 ⌊log₂ N⌋`. -/
theorem codeBound_le (N : ℕ) : codeBound N ≤ 2 * (N + 1) * (N + 1) := by
  have hlog : 2 ^ Nat.log 2 N ≤ N + 1 := by
    rcases eq_or_ne N 0 with rfl | hN
    · simp
    · exact (Nat.pow_log_le_self 2 hN).trans (Nat.le_succ N)
  calc codeBound N = 2 * 2 ^ (4 * primeBound N) := by rw [codeBound, pow_succ, mul_comm]
    _ ≤ 2 * 2 ^ (2 * Nat.log 2 N) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos (by unfold primeBound; omega))
    _ = 2 * (2 ^ Nat.log 2 N * 2 ^ Nat.log 2 N) := by rw [← pow_add, ← two_mul]
    _ ≤ 2 * ((N + 1) * (N + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hlog hlog)
    _ = 2 * (N + 1) * (N + 1) := by ring

/-- The search range `2 ^ (4 L + 1)` on `N` bits, in unary, from `N` in unary. -/
@[fun_prop]
theorem computableTidilyInPolyTime_codeBound :
    ComputableTidilyInPolyTime codeBound encUnary encUnary := by
  have hvalue : ComputableTidilyInPolyTime codeBound encUnary encNat := by
    unfold codeBound
    have := binary_two_pow
    fun_prop
  exact binary_to_unary_bounded hvalue (bound := fun N => 2 * (N + 1) * (N + 1)) (by fun_prop)
    codeBound_le

/-! ### The multiplication table -/

/-- The tables of remainders of powers of `X` on `N` bits, `N` in unary: the search for each
irreducible polynomial ranges over the `2 ^ (4 L + 1) ≤ 2 (N + 1) ^ 2` codes below `codeBound N`. -/
@[fun_prop]
theorem computableTidilyInPolyTime_explicitPowerTables :
    ComputableTidilyInPolyTime explicitPowerTables encUnary (encList (encList encBits)) := by
  unfold explicitPowerTables
  have := computableTidilyInPolyTime_bits_unary
  fun_prop

/-- The mixed-radix digits in the radix of the field degree on `N` bits; every partial product of
the radix is at most `N + 1`. -/
theorem computableTidilyInPolyTime_mixedDigit_degreePrimes :
    ComputableTidilyInPolyTime (fun q : (ℕ × ℕ) × ℕ => mixedDigit (degreePrimes q.1.1) q.1.2 q.2)
      (encPair (encPair encUnary encUnary) encUnary) encUnary := by
  have htake : ComputableTidilyInPolyTime (fun q : (ℕ × ℕ) × ℕ => (degreePrimes q.1.1).take q.2)
      (encPair (encPair encUnary encUnary) encUnary) (encList encUnary) :=
    (computableTidilyInPolyTime_take encUnary).comp ((computableTidilyInPolyTime_degreePrimes.comp
      ((fst encUnary encUnary).comp (fst _ _))).prod (snd _ _))
  have hprod := computableTidilyInPolyTime_prod_of_le htake
    (fun q p hp => (prime_of_mem_degreePrimes (List.mem_of_mem_take hp)).2.2.pos)
    (B := fun q => q.1.1 + 1) (.of_forall_le 1 1 fun q => by simp [encPair_apply]; omega)
    (fun q => by
      refine le_trans ?_ (prod_degreePrimes_le q.1.1)
      rw [← List.prod_take_mul_prod_drop (degreePrimes q.1.1) q.2]
      exact Nat.le_mul_of_pos_right _ (List.prod_pos fun p hp =>
        (prime_of_mem_degreePrimes (List.mem_of_mem_drop hp)).2.2.pos))
  unfold mixedDigit
  fun_prop

/-- Mixed-radix digits in the radix of the field degree, as a composition rule. -/
@[fun_prop]
theorem computableTidilyInPolyTime_mixedDigit_degreePrimes' {α : Type} {input : α ↪ List Bool}
    {N u i : α → ℕ} (hN : ComputableTidilyInPolyTime N input encUnary)
    (hu : ComputableTidilyInPolyTime u input encUnary)
    (hi : ComputableTidilyInPolyTime i input encUnary) :
    ComputableTidilyInPolyTime (fun a => mixedDigit (degreePrimes (N a)) (u a) (i a)) input
      encUnary :=
  computableTidilyInPolyTime_mixedDigit_degreePrimes.comp ((hN.prod hu).prod hi)


/-- Coordinates of the products of monomials of the explicit field on `N` bits, `N` in unary. -/
theorem computableTidilyInPolyTime_monomialBit_explicit : ComputableTidilyInPolyTime
    (fun q : ((ℕ × ℕ) × ℕ) × ℕ =>
      monomialBit (degreePrimes q.1.1.1) (explicitPowerTables q.1.1.1) q.1.1.2 q.1.2 q.2)
    (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encBool := by
  unfold monomialBit
  fun_prop

/-- Coordinates of the products of monomials of the explicit field, as a composition rule. -/
@[fun_prop]
theorem computableTidilyInPolyTime_monomialBit_explicit' {α : Type} {input : α ↪ List Bool}
    {N u w v : α → ℕ} (hN : ComputableTidilyInPolyTime N input encUnary)
    (hu : ComputableTidilyInPolyTime u input encUnary)
    (hw : ComputableTidilyInPolyTime w input encUnary)
    (hv : ComputableTidilyInPolyTime v input encUnary) :
    ComputableTidilyInPolyTime
      (fun a => monomialBit (degreePrimes (N a)) (explicitPowerTables (N a)) (u a) (w a) (v a))
      input encBool :=
  computableTidilyInPolyTime_monomialBit_explicit.comp (((hN.prod hu).prod hw).prod hv)

/-- The multiplication table of the explicit field on `N` bits, `N` in unary: its `n ^ 3`
entries, `n ≤ N + 1`, are products over the prime factors of `n`. -/
@[fun_prop]
theorem computableTidilyInPolyTime_explicitTable :
    ComputableTidilyInPolyTime explicitTable encUnary (encList (encList encBits)) := by
  unfold explicitTable monomialTable
  simp_rw [← fieldDegree_eq_prod]
  fun_prop

/-! ### Field arithmetic in coordinates -/

/-- A multiplication table, as a list of rows of coordinate words. -/
abbrev encTable : List (List (List Bool)) ↪ List Bool :=
  encList (encList encBits)

/-- An entry of a computed multiplication table. -/
@[fun_prop]
theorem computableTidilyInPolyTime_tableEntry {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {u w : α → ℕ}
    (htab : ComputableTidilyInPolyTime tab input encTable)
    (hu : ComputableTidilyInPolyTime u input encUnary)
    (hw : ComputableTidilyInPolyTime w input encUnary) :
    ComputableTidilyInPolyTime (fun a => tableEntry (tab a) (u a) (w a)) input encBits :=
  computableTidilyInPolyTime_getD_list (computableTidilyInPolyTime_getD_list htab hu []) hw []

/-- **Multiplication in coordinates**, uniformly in the multiplication table: the sum of at most
`n ^ 2` table entries, `n` the number of rows. -/
theorem computableTidilyInPolyTime_fieldMul : ComputableTidilyInPolyTime
    (fun p : List (List (List Bool)) × List Bool × List Bool => fieldMul p.1 p.2.1 p.2.2)
    (encPair encTable (encPair encBits encBits)) encBits := by
  unfold fieldMul
  fun_prop

/-- Multiplication in coordinates, as a composition rule. -/
@[fun_prop]
theorem computableTidilyInPolyTime_fieldMul' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {a b : α → List Bool}
    (htab : ComputableTidilyInPolyTime tab input encTable)
    (ha : ComputableTidilyInPolyTime a input encBits)
    (hb : ComputableTidilyInPolyTime b input encBits) :
    ComputableTidilyInPolyTime (fun x => fieldMul (tab x) (a x) (b x)) input encBits :=
  computableTidilyInPolyTime_fieldMul.comp (htab.prod (ha.prod hb))

theorem length_fieldMul (tab : List (List (List Bool))) (a b : List Bool) :
    (fieldMul tab a b).length = tab.length := by
  simp [fieldMul]

/-- The powers `y ^ (2 ^ (k + 1) - 1)`, by `k` multiplications and squarings; every
intermediate power has `n` coordinates. -/
theorem computableTidilyInPolyTime_powerPred : ComputableTidilyInPolyTime
    (fun p : List (List (List Bool)) × List Bool × ℕ => powerPred p.1 p.2.1 p.2.2)
    (encPair encTable (encPair encBits encUnary)) encBits := by
  unfold powerPred
  refine iterateWithInput_of_bounded_growth (by fun_prop) (by fun_prop) (by fun_prop)
    ⟨(length_list (encList encBits)).comp (fst _ _) |>.polyBounded, fun p z => ?_⟩
  simp [length_fieldMul]

/-- Powers in coordinates, as a composition rule. -/
@[fun_prop]
theorem computableTidilyInPolyTime_powerPred' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {y : α → List Bool} {k : α → ℕ}
    (htab : ComputableTidilyInPolyTime tab input encTable)
    (hy : ComputableTidilyInPolyTime y input encBits)
    (hk : ComputableTidilyInPolyTime k input encUnary) :
    ComputableTidilyInPolyTime (fun x => powerPred (tab x) (y x) (k x)) input encBits := by
  simpa only [Function.comp_def] using
    computableTidilyInPolyTime_powerPred.comp (htab.prod (hy.prod hk))

/-- One step of the dynamic program for the elementary symmetric polynomials. -/
theorem computableTidilyInPolyTime_esymmStep : ComputableTidilyInPolyTime
    (fun p : (List (List (List Bool)) × List (List Bool)) × List Bool =>
      esymmStep p.1.1 p.1.2 p.2)
    (encPair (encPair encTable (encList encBits)) encBits) (encList encBits) := by
  unfold esymmStep
  fun_prop

theorem length_esymmStep (tab : List (List (List Bool))) (E : List (List Bool))
    (z : List Bool) : (esymmStep tab E z).length = E.length := by
  simp [esymmStep]

/-- **The elementary symmetric polynomial `e_t` in coordinates**: the dynamic program keeps `t`
words of at most `n` coordinates. -/
theorem computableTidilyInPolyTime_esymmCoords : ComputableTidilyInPolyTime
    (fun p : (List (List (List Bool)) × ℕ) × List (List Bool) => esymmCoords p.1.1 p.1.2 p.2)
    (encPair (encPair encTable encUnary) (encList encBits)) encBits := by
  have hsize : ComputableTidilyInPolyTime
      (fun p : (List (List (List Bool)) × ℕ) × List (List Bool) =>
        p.1.2 * (2 * p.1.1.length + 1))
      (encPair (encPair encTable encUnary) (encList encBits)) encUnary := by
    fun_prop
  have h := (foldlWith_spec (encIn := encPair (encPair encTable encUnary) (encList encBits))
    (encA := encBits) (encL := encList encBits)
    (par := fun p : (List (List (List Bool)) × ℕ) × List (List Bool) => p.1.1)
    (list := Prod.snd) (init := fun p => List.replicate p.1.2 []) (step := esymmStep)
    (by fun_prop) (by fun_prop) (by fun_prop) computableTidilyInPolyTime_esymmStep
    (fun p _ state => state.length = p.1.2 ∧ ∀ e ∈ state, e.length ≤ p.1.1.length)
    (fun p => by simp) (fun p consumed state value _ h => by
      refine ⟨by rw [length_esymmStep, h.1], fun e he => ?_⟩
      simp only [esymmStep, List.mem_map, List.mem_range] at he
      obtain ⟨j, -, rfl⟩ := he
      simp)
    (size := fun p => p.1.2 * (2 * p.1.1.length + 1)) hsize.polyBounded
    (fun p consumed state _ h => by
      rw [length_encList, ← h.1]
      refine (List.sum_le_length_nsmul _ (2 * p.1.1.length + 1) fun x hx => ?_).trans ?_
      · simp only [List.mem_map] at hx
        obtain ⟨e, he, rfl⟩ := hx
        have := h.2 e he
        simp only [encBits]
        simp
        omega
      · simp)).1
  unfold esymmCoords
  exact computableTidilyInPolyTime_getD_list h (by fun_prop) []

/-- The elementary symmetric polynomial in coordinates, as a composition rule. -/
@[fun_prop]
theorem computableTidilyInPolyTime_esymmCoords' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} {t : α → ℕ} {zs : α → List (List Bool)}
    (htab : ComputableTidilyInPolyTime tab input encTable)
    (ht : ComputableTidilyInPolyTime t input encUnary)
    (hzs : ComputableTidilyInPolyTime zs input (encList encBits)) :
    ComputableTidilyInPolyTime (fun x => esymmCoords (tab x) (t x) (zs x)) input encBits := by
  simpa only [Function.comp_def] using
    computableTidilyInPolyTime_esymmCoords.comp ((htab.prod ht).prod hzs)

/-- The traces of the basis elements, from the diagonals of the multiplication table. -/
theorem computableTidilyInPolyTime_traceVector :
    ComputableTidilyInPolyTime traceVector encTable encBits := by
  unfold traceVector
  fun_prop

/-- The traces of the basis elements, as a composition rule. -/
@[fun_prop]
theorem computableTidilyInPolyTime_traceVector' {α : Type} {input : α ↪ List Bool}
    {tab : α → List (List (List Bool))} (htab : ComputableTidilyInPolyTime tab input encTable) :
    ComputableTidilyInPolyTime (fun x => traceVector (tab x)) input encBits := by
  simpa only [Function.comp_def] using computableTidilyInPolyTime_traceVector.comp htab

/-- The trace as a bit. -/
theorem computableTidilyInPolyTime_traceBit : ComputableTidilyInPolyTime
    (fun p : List Bool × List Bool => traceBit p.1 p.2) (encPair encBits encBits) encBool := by
  unfold traceBit
  fun_prop

/-- The trace as a bit, as a composition rule. -/
@[fun_prop]
theorem computableTidilyInPolyTime_traceBit' {α : Type} {input : α ↪ List Bool}
    {τ a : α → List Bool} (hτ : ComputableTidilyInPolyTime τ input encBits)
    (ha : ComputableTidilyInPolyTime a input encBits) :
    ComputableTidilyInPolyTime (fun x => traceBit (τ x) (a x)) input encBool := by
  simpa only [Function.comp_def] using computableTidilyInPolyTime_traceBit.comp (hτ.prod ha)

/-- **`traceSym 1 r t` in coordinates**, uniformly in the multiplication table, `r` and `t` in
unary, and the input bits. -/
theorem computableTidilyInPolyTime_traceSymCoords : ComputableTidilyInPolyTime
    (fun p : ((List (List (List Bool)) × ℕ) × ℕ) × List Bool =>
      traceSymCoords p.1.1.1 p.1.1.2 p.1.2 p.2)
    (encPair (encPair (encPair encTable encUnary) encUnary) encBits) encBool := by
  unfold traceSymCoords
  fun_prop

/-! ### The explicit disperser -/

/-- **The program is polynomial-time.** -/
theorem computableTidilyInPolyTime_explicitDisperserProgram :
    ComputableTidilyInPolyTime explicitDisperserProgram encBits encBool := by
  unfold explicitDisperserProgram
  simpa only [Function.comp_def] using computableTidilyInPolyTime_traceSymCoords.comp
    ((((computableTidilyInPolyTime_explicitTable.comp length_bits).prod
      (computableTidilyInPolyTime_numBlocks.comp length_bits)).prod
      (computableTidilyInPolyTime_symDegree.comp length_bits)).prod id')

/-- **The explicit affine disperser is computable in polynomial time**: on a bit list `x` of length
`N`, the value `explicitDisperser N x` is computed by a tidy multi-tape machine in time polynomial
in `N`. The certificate charges the whole computation: the parameters, the exhaustive searches for
the irreducible polynomials by trial division, the remainders of the powers of `X`, the
multiplication table, and every field operation of `traceSym 1 r t`. -/
theorem computableTidilyInPolyTime_explicitDisperser :
    ComputableTidilyInPolyTime
      (fun x : List Bool => explicitDisperser x.length (BitString.ofList x.length x))
      encBits encBool := by
  rw [← funext explicitDisperserProgram_eq]
  exact computableTidilyInPolyTime_explicitDisperserProgram

/-- **The explicit affine disperser is in `P`**: the bit lists `x` with
`explicitDisperser x.length (BitString.ofList x.length x) = true` form a problem in `P`. -/
theorem setOf_explicitDisperser_mem_P :
    {x : List Bool | explicitDisperser x.length (BitString.ofList x.length x) = true} ∈
      Cslib.Complexity.P encBits :=
  ⟨_, computableTidilyInPolyTime_explicitDisperser, fun _ => Iff.rfl⟩

end Cslib.AffineDisperser
