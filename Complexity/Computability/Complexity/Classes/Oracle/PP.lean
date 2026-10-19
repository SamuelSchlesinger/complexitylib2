/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle
public import Complexity.Computability.Complexity.Classes.PP
public import Complexity.Computability.Complexity.Classes.SharpP
public import Complexity.Computability.Complexity.Classes.Toda
import Complexity.Computability.Complexity.Classes.Oracle.Simulation
import Complexity.Computability.Complexity.Classes.Inclusions
import Complexity.Computability.Complexity.Classes.PP.Characterization
import Complexity.Computability.Complexity.Classes.SharpP.Closure
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Probabilistic.Oracle.Composition
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bitwise

/-!
# Polynomial time with a `PP` oracle

`P^PP` relative to the encoding `enc` of instances (`Cslib.Complexity.PWithPPOracle`) consists of
the problems `L` decided by one deterministic oracle program, strict oracle PPT as in
`Cslib.Complexity.ComputableInPolyTimeWithOracle`, that is correct against every oracle language
agreeing with some problem `B ∈ PP` on the encoded instances of `B`, for some encoded type of
instances of `B`. As for `Cslib.Complexity.PWithSharpPOracle`, the program is fixed before the
oracle and the answers on words that are not codes are arbitrary.

A bit of a value `f a` of a function `f ∈ #P` is computed in `P^PP` by binary search
(`Cslib.Complexity.mem_PWithPPOracle_of_testBit`): the problem `{(a, k) | k ≤ f a}` is in `PP`,
by the characterisation through `GapP` (`Cslib.Complexity.setOf_le_mem_PP`), and `N` queries
`lo + 2 ^ (j - 1) ≤ f a`, for `j = N, …, 1`, determine `f a < 2 ^ N`
(`Cslib.Complexity.BinarySearch.iterate_step`). With the form of Toda's theorem that decides every
problem in the polynomial hierarchy by one bit of a `#P` value
(`Cslib.Complexity.exists_SharpP_testBit_of_mem_BPOp_ParityP`), this gives **Toda's theorem
`PH ⊆ P^PP`** [Toda][Toda1991] (`Cslib.Complexity.PH_subset_PWithPPOracle`). The class does not
count queries.

## Main definitions

* `Cslib.Complexity.PWithPPOracle`: polynomial time with a `PP` oracle.
* `Cslib.Complexity.BinarySearch.step`: one round of binary search.

## Main results

* `Cslib.Complexity.P_subset_PWithPPOracle`, `Cslib.Complexity.PP_subset_PWithPPOracle`:
  `P ⊆ P^PP` and `PP ⊆ P^PP`.
* `Cslib.Complexity.setOf_le_mem_PP`: comparing with a `#P` value is in `PP`.
* `Cslib.Complexity.mem_PWithPPOracle_of_testBit`: one bit of a `#P` value is in `P^PP`.
* `Cslib.Complexity.BPOp_ParityP_subset_PWithPPOracle`: `BP·⊕P ⊆ P^PP`.
* `Cslib.Complexity.PH_subset_PWithPPOracle`: **Toda's theorem, `PH ⊆ P^PP`**.

## References

* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

variable {α : Type}

open Classical in
/-- **`P^PP`**: the problems `L` such that, for some type `β` with encoding `encβ` and some
`B ∈ PP encβ`, one deterministic oracle program, strict oracle PPT on the encoding `enc` of
instances, decides `L` against every oracle language containing the code `encβ b` exactly when
`b ∈ B`. Answers on words that are not codes are arbitrary. -/
def PWithPPOracle (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ (β : Type) (encβ : β ↪ List Bool) (B : Set β), B ∈ PP encβ ∧
    ∃ program : α → WordQueryComp Unit Bool,
      IsOraclePPTOn enc encBool (fun a => OracleComp.interpret ProbOracleComp.query (program a)) ∧
        ∀ A : Set (List Bool), (∀ b, encβ b ∈ A ↔ b ∈ B) →
          ∀ a, a ∈ L ↔ OracleComp.interpret (m := Id) (languageOracle A) (program a) = true}

variable {enc : α ↪ List Bool} {L : Set α}

/-- **`P ⊆ P^PP`**: a polynomial-time decider makes no query. -/
theorem P_subset_PWithPPOracle : P enc ⊆ PWithPPOracle enc := by
  rintro L ⟨g, hg, hL⟩
  have hempty : (∅ : Set α) ∈ PP enc :=
    BPP_subset_PP (P_subset_BPP ⟨fun _ => false, .const false, fun _ => by simp⟩)
  exact ⟨α, enc, ∅, hempty, fun a => pure (g a), hg.isOraclePPTOn, fun _ _ a => hL a⟩

/-- **`PP ⊆ P^PP`**: the program asks the oracle about its instance, with one query. -/
theorem PP_subset_PWithPPOracle : PP enc ⊆ PWithPPOracle enc := by
  classical
  intro L hL
  refine ⟨α, enc, L, hL, fun a => (fun reply => decide (reply = [true])) <$>
    (List.take 1 <$> OracleComp.query ((), enc a)), ?_, fun A hA a => ?_⟩
  · simp only [OracleComp.interpret_map, OracleComp.interpret_query]
    exact (IsOraclePPTOn.query_take () (ComputableTidilyInPolyTime.encode enc)
      (limit := fun _ => 1) (by fun_prop)).map (by fun_prop)
  · change a ∈ L ↔ decide (List.take 1 (languageOracle A ((), enc a)) = [true]) = true
    rw [languageOracle_apply, ← hA a]
    by_cases hm : enc a ∈ A <;> simp [hm]

/-! ### Comparing with a `#P` value -/

/-- **Comparing with a `#P` value is in `PP`**: for `f ∈ #P`, the pairs `(a, k)` with `k ≤ f a`,
`k` in binary, are the instances where the `GapP` function `f a + 1 - k` is positive. -/
theorem setOf_le_mem_PP {f : α → ℕ} (hf : f ∈ SharpP enc) :
    {x : α × ℕ | x.2 ≤ f x.1} ∈ PP (encPair enc encNat) := by
  refine mem_PP_iff_exists_GapP.2 ⟨fun x => ((f x.1 + 1 : ℕ) : ℤ) - (x.2 : ℕ),
    ⟨_, SharpP.add_one_mem (SharpP.comp_mem hf (ComputableTidilyInPolyTime.fst enc encNat)), _,
      SharpP.of_polyTime (ComputableTidilyInPolyTime.snd enc encNat), fun _ => rfl⟩,
    fun x => ?_⟩
  simp only [Set.mem_ofPred_eq, sub_pos, Nat.cast_lt]
  omega

/-! ### Binary search -/

namespace BinarySearch

/-- One round of binary search for a number `F`: in the state `(lo, j)` with `j > 0` bits left,
test whether `lo + 2 ^ (j - 1) ≤ F`, and keep the half containing `F`. -/
def step (F : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  if s.2 = 0 then s else (if s.1 + 2 ^ (s.2 - 1) ≤ F then s.1 + 2 ^ (s.2 - 1) else s.1, s.2 - 1)

/-- **Binary search finds `F < 2 ^ N` in `N` rounds.** -/
theorem iterate_step {F N : ℕ} (hF : F < 2 ^ N) : ((step F)^[N] (0, N)).1 = F := by
  have key (t : ℕ) (ht : t ≤ N) : ∃ lo, (step F)^[t] (0, N) = (lo, N - t) ∧ lo ≤ F ∧
      F < lo + 2 ^ (N - t) := by
    induction t with
    | zero => exact ⟨0, rfl, Nat.zero_le _, by simpa using hF⟩
    | succ t ih =>
      obtain ⟨lo, hlo, hle, hlt⟩ := ih (by omega)
      rw [Function.iterate_succ_apply', hlo]
      obtain ⟨j, hj⟩ : ∃ j, N - t = j + 1 := ⟨N - t - 1, by omega⟩
      have hj' : N - (t + 1) = j := by omega
      rw [hj] at hlt
      rw [pow_succ] at hlt
      unfold step
      simp only [hj, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, hj']
      split_ifs with h
      · exact ⟨_, rfl, h, by omega⟩
      · exact ⟨_, rfl, hle, by omega⟩
  obtain ⟨lo, hlo, hle, hlt⟩ := key N le_rfl
  rw [hlo]
  simp only [Nat.sub_self, pow_zero] at hlt
  simp only
  omega

end BinarySearch

/-- One round of binary search for `f a`, asking the oracle whether `(a, lo + 2 ^ (j - 1))` is in
`{(a, k) | k ≤ f a}`. -/
def searchQuery (enc : α ↪ List Bool) (a : α) (s : ℕ × ℕ) : WordQueryComp Unit (ℕ × ℕ) :=
  if s.2 = 0 then pure s else
    (fun reply => (if reply == [true] then s.1 + 2 ^ (s.2 - 1) else s.1, s.2 - 1)) <$>
      (List.take 1 <$> OracleComp.query ((), encPair enc encNat (a, s.1 + 2 ^ (s.2 - 1))))

private theorem interpret_iterate {ι κ : Type} {spec : OracleSpec.{0, 0} ι}
    {target : OracleSpec.{0, 0} κ} (handler : (q : ι) → OracleComp target (spec q)) {σ : Type}
    (n : ℕ) (step : σ → OracleComp spec σ) (s : σ) :
    OracleComp.interpret handler (OracleComp.iterate n step s) =
      OracleComp.iterate n (fun s => OracleComp.interpret handler (step s)) s := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [OracleComp.iterate_succ, OracleComp.interpret_bind, ih]

/-- A round of the search as a program with private coins and word queries. -/
theorem interpret_searchQuery (a : α) (s : ℕ × ℕ) :
    OracleComp.interpret ProbOracleComp.query (searchQuery enc a s) =
      if s.2 = 0 then pure s else
        (fun reply => (if reply == [true] then s.1 + 2 ^ (s.2 - 1) else s.1, s.2 - 1)) <$>
          (List.take 1 <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
            ((), encPair enc encNat (a, s.1 + 2 ^ (s.2 - 1)))) := by
  unfold searchQuery
  split <;> simp [OracleComp.interpret_map, OracleComp.interpret_query]

open Classical in
/-- Against an oracle agreeing with `{(a, k) | k ≤ f a}` on codes, a round of the search is
`BinarySearch.step (f a)`. -/
theorem interpret_id_searchQuery {f : α → ℕ} {A : Set (List Bool)}
    (hA : ∀ x : α × ℕ, encPair enc encNat x ∈ A ↔ x.2 ≤ f x.1) (a : α) (s : ℕ × ℕ) :
    OracleComp.interpret (m := Id) (languageOracle A) (searchQuery enc a s) =
      BinarySearch.step (f a) s := by
  unfold searchQuery BinarySearch.step
  split
  · rfl
  · change (fun reply : List Bool =>
      (if reply == [true] then s.1 + 2 ^ (s.2 - 1) else s.1, s.2 - 1))
        (List.take 1 (languageOracle A ((), encPair enc encNat (a, s.1 + 2 ^ (s.2 - 1))))) = _
    rw [languageOracle_apply]
    by_cases hm : encPair enc encNat (a, s.1 + 2 ^ (s.2 - 1)) ∈ A
    · simp only [decide_eq_true hm, (hA _).1 hm, ↓reduceIte, List.take_succ_cons, List.take_zero,
        beq_self_eq_true]
    · have hle : ¬ s.1 + 2 ^ (s.2 - 1) ≤ f a := fun h => hm ((hA (a, _)).2 h)
      simp only [decide_eq_false hm, hle, ↓reduceIte, List.take_succ_cons, List.take_zero]
      rfl

/-- **One bit of a `#P` value is in `P^PP`**: a problem decided by the bit at a polynomial
position of a function `f ∈ #P` on its own instances is in `P^PP`. The program finds `f a` by
binary search with queries `k ≤ f a` to the `PP` problem `{(a, k) | k ≤ f a}`. -/
theorem mem_PWithPPOracle_of_testBit {f : α → ℕ} (hf : f ∈ SharpP enc)
    {p : Polynomial ℕ} (h : ∀ a, a ∈ L ↔ (f a).testBit (p.eval (enc a).length)) :
    L ∈ PWithPPOracle enc := by
  classical
  obtain ⟨r, hr⟩ := SharpP.exists_le_two_pow hf
  -- the number of rounds
  set N : α → ℕ := fun a => r.eval (enc a).length + 1 with hN
  have hfN (a : α) : f a < 2 ^ N a :=
    (hr a).trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _))
  have hNpt : ComputableTidilyInPolyTime N enc encUnary := by
    simp only [hN]
    fun_prop
  refine ⟨α × ℕ, encPair enc encNat, {x | x.2 ≤ f x.1}, setOf_le_mem_PP hf,
    fun a => (fun s => s.1.testBit (p.eval (enc a).length)) <$>
      OracleComp.iterate (N a) (searchQuery enc a) (0, N a), ?_, fun A hA a => ?_⟩
  · simp only [OracleComp.interpret_map, interpret_iterate]
    have hinit : ComputableTidilyInPolyTime (fun a => ((0 : ℕ), N a)) enc
        (encPair encNat encUnary) :=
      (ComputableTidilyInPolyTime.const 0).prod hNpt
    have hstep : IsOraclePPTOn (encPair enc (encPair encNat encUnary)) (encPair encNat encUnary)
        (fun pair : α × (ℕ × ℕ) =>
          OracleComp.interpret ProbOracleComp.query (searchQuery enc pair.1 pair.2)) := by
      simp only [interpret_searchQuery]
      refine IsOraclePPTOn.ite (by fun_prop)
        (ComputableTidilyInPolyTime.snd enc (encPair encNat encUnary)).isOraclePPTOn ?_
      exact IsOraclePPTOn.map_with (IsOraclePPTOn.query_take () (by fun_prop) (by fun_prop))
        (by fun_prop)
    have hfinal : ComputableTidilyInPolyTime
        (fun pair : α × (ℕ × ℕ) => pair.2.1.testBit (p.eval (enc pair.1).length))
        (encPair enc (encPair encNat encUnary)) encBool := by
      have h : ComputableTidilyInPolyTime
          (fun pair : α × (ℕ × ℕ) => ((pair.2.1.bits)[p.eval (enc pair.1).length]?).getD false)
          (encPair enc (encPair encNat encUnary)) encBool := by
        fun_prop
      refine h.of_enc_eq fun pair => ?_
      rw [Nat.testBit_eq_inth, List.getI_eq_getElem?_getD]
      rfl
    have hpreserve (a : α) (i : ℕ) (s : ℕ × ℕ) (hi : i < N a)
        (hinv : s.2 = N a - i ∧ s.1 + 2 ^ s.2 ≤ 2 ^ N a) (next : ℕ × ℕ)
        (hnext : next ∈ ProbOracleComp.support
          (OracleComp.interpret ProbOracleComp.query (searchQuery enc a s))) :
        next.2 = N a - (i + 1) ∧ next.1 + 2 ^ next.2 ≤ 2 ^ N a := by
      obtain ⟨hs, hlo⟩ := hinv
      have hs0 : s.2 ≠ 0 := by omega
      rw [interpret_searchQuery] at hnext
      simp only [hs0, ↓reduceIte, Functor.map_map] at hnext
      obtain ⟨reply, -, rfl⟩ := ProbOracleComp.mem_support_map hnext
      obtain ⟨j, hj⟩ : ∃ j, s.2 = j + 1 := ⟨s.2 - 1, by omega⟩
      rw [hj, pow_succ] at hlo
      refine ⟨by simp only; omega, ?_⟩
      simp only [hj, Nat.add_sub_cancel]
      split_ifs <;> omega
    have hbound (a : α) (i : ℕ) (s : ℕ × ℕ) (_ : i ≤ N a)
        (hinv : s.2 = N a - i ∧ s.1 + 2 ^ s.2 ≤ 2 ^ N a) :
        (encPair encNat encUnary s).length ≤ 3 * N a + 1 := by
      obtain ⟨hs, hlo⟩ := hinv
      have hsize : s.1.size ≤ N a := Nat.size_le.2 (by
        have := Nat.one_le_two_pow (n := s.2)
        omega)
      rw [← Nat.size_eq_bits_len] at hsize
      simp only [length_encPair, encNat_apply, encUnary_apply, List.length_replicate]
      omega
    exact (IsOraclePPTOn.iterateWith_spec
      (step := fun a s => OracleComp.interpret ProbOracleComp.query (searchQuery enc a s))
      hNpt hinit hstep (fun a i s => s.2 = N a - i ∧ s.1 + 2 ^ s.2 ≤ 2 ^ N a)
      (fun a => ⟨by simp, by simp⟩) hpreserve
      (((PolyBounded.const 3).mul hNpt.polyBounded).add (.const 1)) hbound).1.map_with hfinal
  · rw [h a, OracleComp.interpret_map]
    change _ ↔ (OracleComp.interpret (m := Id) (languageOracle A)
      (OracleComp.iterate (N a) (searchQuery enc a) (0, N a))).1.testBit _ = true
    rw [OracleComp.interpret_id_iterate]
    simp only [interpret_id_searchQuery (f := f) (fun x => hA x)]
    rw [BinarySearch.iterate_step (hfN a)]

/-! ### Toda's theorem -/

/-- **`BP·⊕P ⊆ P^PP`**: a problem decided with bounded error by a problem in `⊕P` about pairs of
an instance and a random string is decided by one bit of a function in `#P`, found by binary
search with a `PP` oracle. -/
theorem BPOp_ParityP_subset_PWithPPOracle :
    BPOp enc (ParityP (encPair enc encBits)) ⊆ PWithPPOracle enc := fun _ hL =>
  let ⟨_, hf, _, h⟩ := exists_SharpP_testBit_of_mem_BPOp_ParityP hL
  mem_PWithPPOracle_of_testBit hf h

/-- **Toda's theorem: `PH ⊆ P^PP`** [Toda][Toda1991]. Every problem in the polynomial hierarchy is
decided by a polynomial-time oracle program against every oracle language agreeing with a problem
in `PP` on its encoded instances. -/
theorem PH_subset_PWithPPOracle : PH enc ⊆ PWithPPOracle enc :=
  PH_subset_BPOp_ParityP.trans BPOp_ParityP_subset_PWithPPOracle

end Cslib.Complexity
