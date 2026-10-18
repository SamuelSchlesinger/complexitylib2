/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.PH

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Combinatorics.FiniteCover
import Complexity.Foundations.Combinatorics.MajorityVote

/-!
# The Sipser–Lautemann theorem

Every problem in `BPP` lies in the second level `Σ₂ ∩ Π₂` of the polynomial hierarchy, and hence
in `PH` [Sipser (1983); Lautemann][Lautemann1983]; see also
[Arora and Barak, Theorem 7.15][AroraBarak09].

Given a `BPP` verifier `V` using random strings of length `m = p (enc a).length`, repeating the
test `2 R` times (with `R = 6 m + 48`) and taking a strict majority (`> R` accepting runs) reduces
the error fraction to at most `(8 / 9) ^ R` (`Cslib.card_filter_card_filter_le_le`). Under bitwise
XOR shifts on the space `Seed m = (Fin (2 R) → Fin m → Bool)` of amplified seeds:

* **Completeness** (`a ∈ A`): since `2 ^ (2 R m) * (8 ^ R) ^ (2 R) < (9 ^ R) ^ (2 R)`, the finite
  covering lemma (`Cslib.exists_cover_of_scaled_card_lt`) yields `T = 2 R` shift vectors covering
  the entire space of amplified seeds.
* **Soundness** (`a ∉ A`): for any `T = 2 R` shift vectors, each shifted accepting set has size at
  most `(8 / 9) ^ R` of the seed space, and `T * 8 ^ R < 9 ^ R`, so their union cannot cover all
  amplified seeds.

The resulting `Σ₂` verifier `SipserLautemann.verifier` reads a concatenated certificate `w = u ++ r`
with existential block length `T * (2 R m)` and universal block length `2 R m`, reconstructs each
shifted trial seed by bitwise XOR, and checks whether some shift yields more than `R` accepting
trials. Closure of `BPP` under complement (`Cslib.Complexity.compl_mem_BPP`) and quantifier duality
(`Cslib.Complexity.compl_mem_PiP_of_mem_SigmaP`) then give `BPP enc ⊆ PiP 2 enc` without repeating
the construction.

## Main definitions

* `Cslib.Complexity.SipserLautemann.Seed`, `Cslib.Complexity.SipserLautemann.shiftSeed`,
  `Cslib.Complexity.SipserLautemann.majorityAccepts`: amplified seeds, bitwise XOR shifts and strict
  majority acceptance.
* `Cslib.Complexity.SipserLautemann.verifier`: the `Σ₂` matrix verifier for a `BPP` problem.
* `Cslib.Complexity.SipserLautemann.witnessPoly`, `Cslib.Complexity.SipserLautemann.seedPoly`:
  the polynomial block lengths of the existential shift table and universal seed.

## Main results

* `Cslib.Complexity.SipserLautemann.exists_shifts_majorityAccepts`,
  `Cslib.Complexity.SipserLautemann.exists_seed_not_majorityAccepts`: combinatorial completeness and
  soundness of shifted majority votes.
* `Cslib.Complexity.SipserLautemann.verifier_polyTime`: the matrix verifier is computable tidily in
  polynomial time.
* `Cslib.Complexity.SipserLautemann.isAlternatingVerifier_verifier`: the matrix verifier is a valid
  `Σ₂` alternating verifier for any `BPP` problem.
* `Cslib.Complexity.BPP_subset_SigmaP_two`: `BPP enc ⊆ SigmaP 2 enc`.
* `Cslib.Complexity.BPP_subset_PiP_two`: `BPP enc ⊆ PiP 2 enc`.
* `Cslib.Complexity.BPP_subset_SigmaP_two_inter_PiP_two`: `BPP enc ⊆ SigmaP 2 enc ∩ PiP 2 enc`.
* `Cslib.Complexity.BPP_subset_PH`: `BPP enc ⊆ PH enc`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Theorem 7.15][AroraBarak09]
* [C. Lautemann, *BPP and the polynomial hierarchy*][Lautemann1983]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

namespace SipserLautemann

/-! ### Amplification and shift parameters -/

/-- Half the number of majority-amplification trials for a single-trial seed of length `m`:
`6 * m + 48 = 6 * (m + 7) + 6`. -/
def halfRuns (m : ℕ) : ℕ := 6 * m + 48

/-- Number of independent repetitions in majority amplification: `2 * halfRuns m = 12 * m + 96`.
A run accepts when strictly more than `halfRuns m` of the `runs m` trials accept. -/
def runs (m : ℕ) : ℕ := 2 * halfRuns m

/-- Number of shift vectors in the Lautemann cover: `shifts m = runs m = 12 * m + 96`. -/
def shifts (m : ℕ) : ℕ := runs m

/-- Length of an amplified universal seed: `runs m * m` bits. -/
def seedLen (m : ℕ) : ℕ := runs m * m

/-- Length of the existential witness concatenating `shifts m` shift vectors:
`shifts m * seedLen m` bits. -/
def witnessLen (m : ℕ) : ℕ := shifts m * seedLen m

/-- Polynomial giving `runs (p.eval n)` at input length `n`. -/
noncomputable def runsPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C 2 * (Polynomial.C 6 * p + Polynomial.C 48)

/-- Polynomial giving `seedLen (p.eval n)` at input length `n`: the length of the universal
quantifier block `r`. -/
noncomputable def seedPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  runsPoly p * p

/-- Polynomial giving `witnessLen (p.eval n)` at input length `n`: the length of the existential
quantifier block `u`. -/
noncomputable def witnessPoly (p : Polynomial ℕ) : Polynomial ℕ :=
  runsPoly p * seedPoly p

@[simp]
theorem eval_runsPoly (p : Polynomial ℕ) (n : ℕ) : (runsPoly p).eval n = runs (p.eval n) := by
  simp [runsPoly, runs, halfRuns]

@[simp]
theorem eval_seedPoly (p : Polynomial ℕ) (n : ℕ) : (seedPoly p).eval n = seedLen (p.eval n) := by
  simp [seedPoly, seedLen]

@[simp]
theorem eval_witnessPoly (p : Polynomial ℕ) (n : ℕ) :
    (witnessPoly p).eval n = witnessLen (p.eval n) := by
  simp [witnessPoly, witnessLen, shifts]

private theorem halfRuns_eq (m : ℕ) : halfRuns m = 6 * (m + 7) + 6 := by
  unfold halfRuns
  omega

private theorem shifts_pos (m : ℕ) : 0 < shifts m := by
  unfold shifts runs halfRuns
  omega

private theorem runs_pos (m : ℕ) : 0 < runs m := by
  unfold runs halfRuns
  omega

private theorem shifts_le_two_pow (m : ℕ) : shifts m ≤ 2 ^ (m + 7) := by
  unfold shifts runs halfRuns
  induction m with
  | zero => decide
  | succ m ih =>
    rw [Nat.add_right_comm m 1 7, pow_succ]
    omega

private theorem two_pow_mul_eight_pow_halfRuns_lt (m : ℕ) :
    2 ^ (m + 7) * 8 ^ halfRuns m < 9 ^ halfRuns m := by
  rw [halfRuns_eq]
  exact Cslib.two_pow_mul_eight_pow_lt (m + 7)

private theorem two_pow_m_mul_eight_pow_halfRuns_lt (m : ℕ) :
    2 ^ m * 8 ^ halfRuns m < 9 ^ halfRuns m := by
  have hm : 2 ^ m ≤ 2 ^ (m + 7) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact (Nat.mul_le_mul_right _ hm).trans_lt (two_pow_mul_eight_pow_halfRuns_lt m)

private theorem shifts_mul_eight_pow_halfRuns_lt (m : ℕ) :
    shifts m * 8 ^ halfRuns m < 9 ^ halfRuns m :=
  (Nat.mul_le_mul_right _ (shifts_le_two_pow m)).trans_lt (two_pow_mul_eight_pow_halfRuns_lt m)

/-! ### Combinatorial shift-cover and soundness on amplified seeds -/

/-- An amplified seed for single-trial seed length `m`: `runs m` blocks of `m` bits each. -/
abbrev Seed (m : ℕ) : Type := Fin (runs m) → Fin m → Bool

/-- Bitwise XOR shift of an amplified seed `r` by a shift vector `u`. -/
def shiftSeed {m : ℕ} (r u : Seed m) : Seed m :=
  fun j k => r j k ^^ u j k

theorem shiftSeed_comm {m : ℕ} (r u : Seed m) : shiftSeed r u = shiftSeed u r := by
  ext j k
  exact Bool.xor_comm (r j k) (u j k)

@[simp]
theorem shiftSeed_self_left {m : ℕ} (r u : Seed m) : shiftSeed r (shiftSeed r u) = u := by
  ext j k
  simp only [shiftSeed]
  cases r j k <;> cases u j k <;> rfl

@[simp]
theorem shiftSeed_self_right {m : ℕ} (r u : Seed m) : shiftSeed (shiftSeed r u) u = r := by
  ext j k
  simp only [shiftSeed]
  cases r j k <;> cases u j k <;> rfl

/-- Bitwise XOR with a fixed seed `r` is a bijection on `Seed m`. -/
def shiftSeedEquiv {m : ℕ} (r : Seed m) : Seed m ≃ Seed m where
  toFun u := shiftSeed r u
  invFun u := shiftSeed r u
  left_inv u := shiftSeed_self_left r u
  right_inv u := shiftSeed_self_left r u

/-- The amplified test accepts `ω : Seed m` when a strict majority (`> halfRuns m`) of the
`runs m = 2 * halfRuns m` blocks satisfy the single-trial predicate `P`. -/
def majorityAccepts {m : ℕ} (P : (Fin m → Bool) → Bool) (ω : Seed m) : Prop :=
  halfRuns m < (univ.filter fun j : Fin (runs m) => P (ω j) = true).card

instance {m : ℕ} (P : (Fin m → Bool) → Bool) : DecidablePred (majorityAccepts P) :=
  fun _ => inferInstanceAs (Decidable (_ < _))

private theorem card_seed_eq (m : ℕ) : Fintype.card (Seed m) = (2 ^ m) ^ runs m := by
  simp [Seed, Fintype.card_fin, Fintype.card_bool]

private theorem card_seed_eq_pow (m : ℕ) :
    Fintype.card (Seed m) = Fintype.card (Fin m → Bool) ^ (2 * halfRuns m) := by
  rw [Fintype.card_fun, Fintype.card_fin]
  rfl

/-- **Completeness on amplified seeds.** If at least two thirds of the single-trial seeds satisfy
`P s = true`, then there exist `shifts m` shift vectors covering every amplified seed `r : Seed m`
under `majorityAccepts P`. -/
theorem exists_shifts_majorityAccepts {m : ℕ} {P : (Fin m → Bool) → Bool}
    (hP : 2 * 2 ^ m ≤ 3 * (univ.filter fun s : Fin m → Bool => P s = true).card) :
    ∃ tests : Fin (shifts m) → Seed m, ∀ r : Seed m, ∃ i,
      majorityAccepts P (shiftSeed r (tests i)) := by
  let G : Finset (Fin m → Bool) := univ.filter fun s => P s = true
  have hG : 2 * Fintype.card (Fin m → Bool) ≤ 3 * G.card := by
    simpa [Fintype.card_fin, Fintype.card_bool, G] using hP
  refine Cslib.exists_cover_of_scaled_card_lt
    (fun u r : Seed m => majorityAccepts P (shiftSeed r u))
    (8 ^ halfRuns m) (9 ^ halfRuns m) (shifts m) (fun r => ?_) ?_
  · have hbij : Fintype.card {u : Seed m // ¬ majorityAccepts P (shiftSeed r u)} =
        Fintype.card {ω : Seed m // ¬ majorityAccepts P ω} :=
      Fintype.card_congr (Equiv.subtypeEquiv (shiftSeedEquiv r) fun _ => Iff.rfl)
    have hcard : Fintype.card {ω : Seed m // ¬ majorityAccepts P ω} =
        (univ.filter fun ω : Seed m => (univ.filter fun j => ω j ∈ G).card ≤ halfRuns m).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext ω
      simp [majorityAccepts, G, not_lt]
    rw [hbij, hcard, card_seed_eq_pow]
    exact Cslib.card_filter_card_filter_le_le G hG (halfRuns m)
  · rw [card_seed_eq]
    change (2 ^ m) ^ shifts m * (8 ^ halfRuns m) ^ shifts m < (9 ^ halfRuns m) ^ shifts m
    rw [← mul_pow]
    exact Nat.pow_lt_pow_left (two_pow_m_mul_eight_pow_halfRuns_lt m) (shifts_pos m).ne'

/-- **Soundness on amplified seeds.** If at least two thirds of the single-trial seeds satisfy
`P s = false`, then for every tuple `tests : Fin (shifts m) → Seed m` of shift vectors, some
amplified seed `r : Seed m` fails `majorityAccepts P (shiftSeed r (tests i))` for all `i`. -/
theorem exists_seed_not_majorityAccepts {m : ℕ} {P : (Fin m → Bool) → Bool}
    (hP : 2 * 2 ^ m ≤ 3 * (univ.filter fun s : Fin m → Bool => P s = false).card)
    (tests : Fin (shifts m) → Seed m) :
    ∃ r : Seed m, ∀ i, ¬ majorityAccepts P (shiftSeed r (tests i)) := by
  let G₀ : Finset (Fin m → Bool) := univ.filter fun s => P s = false
  have hG₀ : 2 * Fintype.card (Fin m → Bool) ≤ 3 * G₀.card := by
    simpa [Fintype.card_fin, Fintype.card_bool, G₀] using hP
  let bad (i : Fin (shifts m)) : Finset (Seed m) :=
    univ.filter fun r : Seed m => majorityAccepts P (shiftSeed r (tests i))
  have hbad (i : Fin (shifts m)) :
      9 ^ halfRuns m * (bad i).card ≤ 8 ^ halfRuns m * Fintype.card (Seed m) := by
    have hcard : (bad i).card = (univ.filter fun ω : Seed m => majorityAccepts P ω).card := by
      rw [← Fintype.card_subtype, ← Fintype.card_subtype]
      refine Fintype.card_congr (Equiv.subtypeEquiv (shiftSeedEquiv (tests i)) fun r => ?_)
      simp [shiftSeed_comm, shiftSeedEquiv]
    have hsub : (univ.filter fun ω : Seed m => majorityAccepts P ω) ⊆
        univ.filter fun ω : Seed m => (univ.filter fun j => ω j ∈ G₀).card ≤ halfRuns m := by
      intro ω hω
      have hω' : halfRuns m < (univ.filter fun j : Fin (runs m) => P (ω j) = true).card :=
        (mem_filter.1 hω).2
      refine mem_filter.2 ⟨mem_univ ω, ?_⟩
      have hpart := Finset.card_filter_add_card_filter_not
        (s := (univ : Finset (Fin (runs m)))) (fun j => ω j ∈ G₀)
      rw [Finset.card_univ, Fintype.card_fin] at hpart
      have hruns : runs m = 2 * halfRuns m := rfl
      have hnot : (univ.filter fun j : Fin (runs m) => ω j ∉ G₀) =
          univ.filter fun j : Fin (runs m) => P (ω j) = true := by
        ext j
        simp [G₀]
      rw [hnot] at hpart
      omega
    rw [hcard, card_seed_eq_pow]
    exact (Nat.mul_le_mul_left _ (card_le_card hsub)).trans
      (Cslib.card_filter_card_filter_le_le G₀ hG₀ (halfRuns m))
  let failures := univ.biUnion bad
  have hunion : 9 ^ halfRuns m * failures.card ≤
      shifts m * 8 ^ halfRuns m * Fintype.card (Seed m) := by
    calc 9 ^ halfRuns m * failures.card
        ≤ 9 ^ halfRuns m * ∑ i, (bad i).card := Nat.mul_le_mul_left _ card_biUnion_le
      _ = ∑ i, 9 ^ halfRuns m * (bad i).card := mul_sum ..
      _ ≤ ∑ _i : Fin (shifts m), 8 ^ halfRuns m * Fintype.card (Seed m) :=
        sum_le_sum fun i _ => hbad i
      _ = shifts m * 8 ^ halfRuns m * Fintype.card (Seed m) := by
        simp [Nat.mul_assoc]
  have hstrict : 9 ^ halfRuns m * failures.card < 9 ^ halfRuns m * Fintype.card (Seed m) :=
    hunion.trans_lt (Nat.mul_lt_mul_of_pos_right
      (shifts_mul_eight_pow_halfRuns_lt m) Fintype.card_pos)
  have hlt : failures.card < (univ : Finset (Seed m)).card := by
    simpa using Nat.lt_of_mul_lt_mul_left hstrict
  obtain ⟨r, _, hr⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨r, fun i hi => hr ?_⟩
  exact mem_biUnion.2 ⟨i, mem_univ i, mem_filter.2 ⟨mem_univ r, hi⟩⟩

/-! ### Bitstring encoding and decoding of seeds and shift tables -/

/-- Decode a flat bitstring `r` into an amplified seed `Seed m` by reading bit `j * m + k` with
default `false`. -/
def listToSeed (m : ℕ) (r : List Bool) : Seed m :=
  fun j k => r.getD (j.1 * m + k.1) false

/-- Decode a flat bitstring `u` into a tuple of shift vectors `Fin (shifts m) → Seed m` by reading
bit `i * seedLen m + j * m + k` with default `false`. -/
def listToShifts (m : ℕ) (u : List Bool) : Fin (shifts m) → Seed m :=
  fun i j k => u.getD (i.1 * seedLen m + j.1 * m + k.1) false

/-- Encode an amplified seed `ω : Seed m` as a flat bitstring of length `seedLen m`. -/
def seedToList {m : ℕ} (ω : Seed m) : List Bool :=
  List.ofFn fun idx : Fin (seedLen m) =>
    if hm : 0 < m then
      ω ⟨idx.1 / m, (Nat.div_lt_iff_lt_mul hm).2 idx.2⟩ ⟨idx.1 % m, Nat.mod_lt _ hm⟩
    else false

/-- Encode a tuple of shift vectors `tests : Fin (shifts m) → Seed m` as a flat bitstring of
length `witnessLen m`. -/
def shiftsToList {m : ℕ} (tests : Fin (shifts m) → Seed m) : List Bool :=
  List.ofFn fun idx : Fin (witnessLen m) =>
    if hL : 0 < seedLen m then
      have hm : 0 < m := Nat.pos_of_ne_zero fun h0 => by simp [seedLen, h0] at hL
      let i : Fin (shifts m) := ⟨idx.1 / seedLen m, (Nat.div_lt_iff_lt_mul hL).2 idx.2⟩
      let rem := idx.1 % seedLen m
      have hrem : rem < runs m * m := Nat.mod_lt _ hL
      let j : Fin (runs m) := ⟨rem / m, (Nat.div_lt_iff_lt_mul hm).2 hrem⟩
      let k : Fin m := ⟨rem % m, Nat.mod_lt _ hm⟩
      tests i j k
    else false

@[simp]
theorem length_seedToList {m : ℕ} (ω : Seed m) : (seedToList ω).length = seedLen m := by
  simp [seedToList]

@[simp]
theorem length_shiftsToList {m : ℕ} (tests : Fin (shifts m) → Seed m) :
    (shiftsToList tests).length = witnessLen m := by
  simp [shiftsToList]

private theorem mul_add_lt_mul {a b A B : ℕ} (ha : a < A) (hb : b < B) :
    a * B + b < A * B := by
  calc a * B + b < a * B + B := Nat.add_lt_add_left hb _
    _ = (a + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul_right B ha

private theorem mul_add_div_and_mod {a b c : ℕ} (hc : c < b) :
    (a * b + c) / b = a ∧ (a * b + c) % b = c := by
  have hb : 0 < b := Nat.zero_lt_of_lt hc
  rw [Nat.mul_comm a b, Nat.mul_add_div hb, Nat.mul_add_mod, Nat.div_eq_of_lt hc,
    Nat.mod_eq_of_lt hc, add_zero]
  exact ⟨rfl, rfl⟩

@[simp]
theorem listToSeed_seedToList {m : ℕ} (ω : Seed m) : listToSeed m (seedToList ω) = ω := by
  ext j k
  have hm : 0 < m := Nat.zero_lt_of_lt k.2
  have hidx : j.1 * m + k.1 < seedLen m := mul_add_lt_mul j.2 k.2
  obtain ⟨hdiv, hmod⟩ := mul_add_div_and_mod (a := j.1) k.2
  simp [listToSeed, seedToList, List.getD_eq_getElem?_getD, hidx, hm, hdiv, hmod]

@[simp]
theorem listToShifts_shiftsToList {m : ℕ} (tests : Fin (shifts m) → Seed m) :
    listToShifts m (shiftsToList tests) = tests := by
  ext i j k
  have hm : 0 < m := Nat.zero_lt_of_lt k.2
  have hrem : j.1 * m + k.1 < seedLen m := mul_add_lt_mul j.2 k.2
  have hL : 0 < seedLen m := Nat.zero_lt_of_lt hrem
  have hidx : i.1 * seedLen m + (j.1 * m + k.1) < witnessLen m := mul_add_lt_mul i.2 hrem
  obtain ⟨hdiv₁, hmod₁⟩ := mul_add_div_and_mod (a := i.1) hrem
  obtain ⟨hdiv₂, hmod₂⟩ := mul_add_div_and_mod (a := j.1) k.2
  simp only [listToShifts, shiftsToList, Nat.add_assoc, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, hidx, ↓reduceDIte, Option.getD_some, hL]
  simp only [hdiv₁, hmod₁, hdiv₂, hmod₂, Fin.eta]

/-! ### The functional matrix verifier and its polynomial-time certificate -/

variable {α : Type}

/-- Extract the `j`-th trial seed of length `m` under the `i`-th shift from a combined certificate
`w = u ++ r`, where `u` has length `T * L` (`T = shifts m`, `L = seedLen m`) and `r` has length `L`.
Bit `k` of the `j`-th block of `r` sits at index `T * L + j * m + k` in `w`, and bit `k` of the
`j`-th block of the `i`-th shift sits at index `i * L + j * m + k` in `w`. -/
def trialSeed (m L T : ℕ) (w : List Bool) (i j : ℕ) : List Bool :=
  (List.range m).map fun k =>
    w.getD (T * L + j * m + k) false ^^ w.getD (i * L + j * m + k) false

/-- Whether the `i`-th shift vector causes a strict majority (`> halfRuns m`) of the `runs m`
trials to be accepted by `V`. -/
def shiftAccepts (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (a : α) (w : List Bool) (i : ℕ) : Bool :=
  let m := p.eval (enc a).length
  decide (halfRuns m <
    (List.range (runs m)).countP fun j => V (a, trialSeed m (seedLen m) (shifts m) w i j))

/-- The Sipser–Lautemann `Σ₂` matrix verifier: given `(a, w)` where `w = u ++ r` consists of an
existential shift-table certificate `u` of length `witnessLen m` and a universal seed `r` of length
`seedLen m` (for `m = p.eval (enc a).length`), test whether some shift `i < shifts m` makes a
strict majority of the `runs m` shifted trials accept. -/
def verifier (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (x : α × List Bool) : Bool :=
  let m := p.eval (enc x.1).length
  (List.range (shifts m)).any fun i => shiftAccepts enc p V x.1 x.2 i

private theorem listBool_to_bits :
    ComputableTidilyInPolyTime (fun l : List Bool => l) (encList encBool) encBits := by
  have heq (l : List Bool) (acc : List Bool) :
      l.foldl (fun acc b => acc ++ [b]) acc = acc ++ l := by
    induction l generalizing acc with
    | nil => simp
    | cons b l ih => simp [ih]
  have h := ComputableTidilyInPolyTime.foldl_of_bounded_growth
    (encA := encBool) (encL := encList encBool) (encB := encBits)
    (list := id) (init := fun _ => []) (step := fun acc b => acc ++ [b])
    .id' (.const []) (by fun_prop) (growth := 1) (fun _ _ => by simp)
  simpa only [heq, List.nil_append, id_eq] using h

private theorem bitsMapWithInput {γ β : Type} {encIn : γ ↪ List Bool} {encA : β ↪ List Bool}
    {f : γ → β → Bool} {list : γ → List β}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encA))
    (hf : ComputableTidilyInPolyTime (fun p : γ × β => f p.1 p.2) (encPair encIn encA) encBool) :
    ComputableTidilyInPolyTime (fun x => (list x).map (f x)) encIn encBits :=
  listBool_to_bits.comp (.mapWithInput hlist hf)

attribute [local fun_prop] bitsMapWithInput

/-- If `V` is computable tidily in polynomial time, then so is the Sipser–Lautemann matrix verifier
`verifier enc p V`. -/
@[fun_prop]
theorem verifier_polyTime {enc : α ↪ List Bool} {p : Polynomial ℕ} {V : α × List Bool → Bool}
    (hV : ComputableTidilyInPolyTime V (encPair enc encBits) encBool) :
    ComputableTidilyInPolyTime (verifier enc p V) (encPair enc encBits) encBool := by
  unfold verifier shiftAccepts trialSeed shifts seedLen runs halfRuns
  fun_prop

/-! ### Correctness of the matrix verifier -/

/-- On a combined certificate `u ++ r` with `u.length = witnessLen m`, `trialSeed` reconstructs
the `j`-th block of the shifted seed `shiftSeed (listToSeed m r) (listToShifts m u i)`. -/
theorem trialSeed_append {m : ℕ} {u r : List Bool} (hu : u.length = witnessLen m)
    (i : Fin (shifts m)) (j : Fin (runs m)) :
    trialSeed m (seedLen m) (shifts m) (u ++ r) i.1 j.1 =
      List.ofFn (shiftSeed (listToSeed m r) (listToShifts m u i) j) := by
  apply List.ext_getElem (by simp [trialSeed])
  intro k hk₁ hk₂
  simp only [trialSeed, List.length_map, List.length_range] at hk₁
  have hrem : j.1 * m + k < seedLen m := mul_add_lt_mul j.2 hk₁
  have hlt : i.1 * seedLen m + j.1 * m + k < u.length := by
    rw [hu, Nat.add_assoc]
    exact mul_add_lt_mul i.2 hrem
  have hge : u.length ≤ shifts m * seedLen m + j.1 * m + k := by
    rw [hu, witnessLen]
    omega
  have hsub : shifts m * seedLen m + j.1 * m + k - u.length = j.1 * m + k := by
    rw [hu, witnessLen]
    omega
  simp only [trialSeed, List.getElem_map, List.getElem_range, List.getElem_ofFn,
    shiftSeed, listToSeed, listToShifts, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right hge, hsub, List.getElem?_append_left hlt]

private theorem countP_range_eq_card_filter (n : ℕ) (pred : ℕ → Bool) :
    (List.range n).countP pred = (univ.filter fun j : Fin n => pred j.1 = true).card := by
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  symm
  refine Finset.card_bij (fun (j : Fin n) _ => j.1) ?_ ?_ ?_
  · intro j hj
    simp only [mem_filter, mem_univ, true_and, List.mem_toFinset, List.mem_filter,
      List.mem_range] at hj ⊢
    exact ⟨j.2, hj⟩
  · intro j₁ _ j₂ _ h
    exact Fin.ext h
  · intro k hk
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, mem_filter,
      mem_univ, true_and] at hk ⊢
    exact ⟨⟨k, hk.1⟩, hk.2, rfl⟩

/-- On a combined certificate `u ++ r` with `u.length = witnessLen (p.eval (enc a).length)`,
`shiftAccepts` agrees with `majorityAccepts` on the `i`-th shifted seed. -/
theorem shiftAccepts_append_iff {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {a : α} {u r : List Bool}
    (hu : u.length = witnessLen (p.eval (enc a).length))
    (i : Fin (shifts (p.eval (enc a).length))) :
    shiftAccepts enc p V a (u ++ r) i.1 = true ↔
      majorityAccepts (fun s => V (a, List.ofFn s))
        (shiftSeed (listToSeed (p.eval (enc a).length) r)
          (listToShifts (p.eval (enc a).length) u i)) := by
  unfold shiftAccepts majorityAccepts
  dsimp only
  rw [decide_eq_true_iff, countP_range_eq_card_filter]
  refine Iff.of_eq (congrArg (halfRuns (p.eval (enc a).length) < ·) (congrArg Finset.card ?_))
  ext j
  simp only [mem_filter, mem_univ, true_and, trialSeed_append hu i j]

/-- On a combined certificate `u ++ r` with `u.length = witnessLen (p.eval (enc a).length)`,
`verifier enc p V (a, u ++ r)` accepts iff some shift `i` satisfies `majorityAccepts`. -/
theorem verifier_append_iff {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {a : α} {u r : List Bool}
    (hu : u.length = witnessLen (p.eval (enc a).length)) :
    verifier enc p V (a, u ++ r) = true ↔
      ∃ i : Fin (shifts (p.eval (enc a).length)),
        majorityAccepts (fun s => V (a, List.ofFn s))
          (shiftSeed (listToSeed (p.eval (enc a).length) r)
            (listToShifts (p.eval (enc a).length) u i)) := by
  unfold verifier
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, hi, hacc⟩
    exact ⟨⟨i, hi⟩, (shiftAccepts_append_iff hu ⟨i, hi⟩).1 hacc⟩
  · rintro ⟨i, hacc⟩
    exact ⟨i.1, i.2, (shiftAccepts_append_iff hu i).2 hacc⟩

/-- If `V` decides `A` with bounded error using seed polynomial `p`, then `verifier enc p V` is a
valid `Σ₂` alternating verifier for `A` with quantifier block lengths
`[witnessPoly p, seedPoly p]`. -/
theorem isAlternatingVerifier_verifier {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {A : Set α} (hA : DecidesWithBoundedError enc p V A) :
    IsAlternatingVerifier enc true [witnessPoly p, seedPoly p] (verifier enc p V) A := by
  intro a
  set m := p.eval (enc a).length
  simp only [List.map_cons, List.map_nil, eval_witnessPoly, eval_seedPoly,
    alternation_true_cons, alternation_false_cons, alternation_nil, List.append_nil]
  constructor
  · intro ha
    obtain ⟨tests, hcover⟩ := exists_shifts_majorityAccepts ((hA a).1 ha)
    refine ⟨shiftsToList tests, length_shiftsToList tests, fun r _ => ?_⟩
    rw [verifier_append_iff (length_shiftsToList tests), listToShifts_shiftsToList]
    exact hcover (listToSeed m r)
  · rintro ⟨u, hu, hforall⟩
    by_contra hna
    obtain ⟨ω, hω⟩ := exists_seed_not_majorityAccepts ((hA a).2 hna) (listToShifts m u)
    have hacc := hforall (seedToList ω) (length_seedToList ω)
    rw [verifier_append_iff hu, listToSeed_seedToList] at hacc
    obtain ⟨i, hi⟩ := hacc
    exact hω i hi

end SipserLautemann

/-! ### Main class inclusions -/

variable {α : Type} {enc : α ↪ List Bool}

/-- **The Sipser–Lautemann theorem (`Σ₂` form)** [Sipser (1983); Lautemann][Lautemann1983],
[Arora and Barak, Theorem 7.15][AroraBarak09]: every problem in `BPP` lies in `Σ₂`. -/
theorem BPP_subset_SigmaP_two : BPP enc ⊆ SigmaP 2 enc := by
  rintro A ⟨p, V, hV, hA⟩
  exact ⟨[SipserLautemann.witnessPoly p, SipserLautemann.seedPoly p],
    SipserLautemann.verifier enc p V, rfl,
    SipserLautemann.verifier_polyTime hV,
    SipserLautemann.isAlternatingVerifier_verifier hA⟩

/-- **The Sipser–Lautemann theorem (`Π₂` form)**: every problem in `BPP` lies in `Π₂`, obtained
from `BPP_subset_SigmaP_two` by complement closure of `BPP` and quantifier duality. -/
theorem BPP_subset_PiP_two : BPP enc ⊆ PiP 2 enc := fun A hA => by
  simpa using compl_mem_PiP_of_mem_SigmaP (BPP_subset_SigmaP_two (compl_mem_BPP hA))

/-- **The Sipser–Lautemann theorem**: `BPP ⊆ Σ₂ ∩ Π₂` [Arora and Barak, Theorem 7.15][AroraBarak09],
[Lautemann][Lautemann1983]. -/
theorem BPP_subset_SigmaP_two_inter_PiP_two : BPP enc ⊆ SigmaP 2 enc ∩ PiP 2 enc :=
  Set.subset_inter BPP_subset_SigmaP_two BPP_subset_PiP_two

/-- Every problem in `BPP` lies in the polynomial hierarchy `PH`. -/
theorem BPP_subset_PH : BPP enc ⊆ PH enc :=
  BPP_subset_SigmaP_two.trans (SigmaP_subset_PH 2)

end Cslib.Complexity
