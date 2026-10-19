/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.NaturalProof
public import Complexity.Crypto.Computational.GGM.Evaluation
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Complexity.Computability.Circuit.Boolean.Word
import Complexity.Computability.Circuit.Synthesis
import Complexity.Crypto.Primitives.PRG.NisanWigderson.Sampling
import Complexity.Foundations.Data.Finset.Expect
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential
import Cslib.Crypto.Primitives.PRG.Basic

/-!
# The GGM construction against circuits

The construction of Goldreich, Goldwasser and Micali [GGM1986] turns a length-doubling generator
`G` with seeds of `k` bits into a keyed family of functions: the key labels the root of a binary
tree of depth `n`, the two children of a node labelled `s` are labelled by the two halves of
`G s`, and the value at an input `x` of `n` bits is the label of the leaf reached by following `x`
(`evalBits`). This is the list-based `Cslib.Crypto.GGM.eval` for words of fixed width
(`ofFn_evalBits`). Keeping the first bit of the label gives a keyed family of Boolean functions
(`booleanFamily`), the family used by Razborov and Rudich [RazborovRudich1997, Section 4].

This module proves the nonuniform security of that family with concrete losses. Circuit sizes
count every AND, OR, NOT and constant gate of the De Morgan basis, and the tests are deterministic
circuits on the whole truth table (`Cslib.Circuits.Boolean.IsCircuitTest`), which query the
function at every input. Write `C` for the circuit complexity of `G` as a function with `2 k`
outputs.

* **Size of the members.** Every function of the family is computed with `n (C + 4 k) + 2`
  gates (`complexity_booleanFamily_le`).
* **Security.** If no test with `t + 2 ^ n (n C + 1)` gates distinguishes `G` from uniform with
  advantage more than `ε`, then no test with `t` gates distinguishes the truth table of a random
  member of the family from a uniformly random truth table with advantage more than
  `(2 ^ n - 1) ε` (`secure_truthTableGenerator_booleanFamily`). The proof is the hybrid argument
  over the levels of the tree. The hybrid at depth `j` labels the `2 ^ j` nodes at depth `j`
  uniformly at random; between depths `j` and `j + 1`, the `2 ^ j` expansions are replaced by
  uniform strings one at a time. Fixing all of them but one turns a test of truth tables into a
  test of that expansion, which computes the subtree below it; every bit of the truth table is
  then a constant or a bit of an evaluation along at most `n` levels.
* **Asymptotics.** A family of generators of polynomial circuit complexity that resists circuits
  of size `2 ^ m` with advantage `2 ^ (-m)` on seeds of length `k ≥ m ^ d`
  (`Cslib.Crypto.PRG.IsSubexponentiallySecure`, implied by security against circuits of size
  `2 ^ (k ^ ε)` with advantage `2 ^ (-k ^ ε)` for `d ε ≥ 1`) gives, with keys of length
  `(n + 1) ^ (2 d)`, an exponentially secure family (`isExponentiallySecure_booleanFamily`). By
  the natural proofs barrier, no `P/poly`-natural property is then useful against `P/poly`
  (`Cslib.Circuits.Boolean.not_isUseful_PPoly_of_isNatural_of_generator`).

The adaptive hybrids of `Cslib.Crypto.GGM.hybridGame` concern uniform oracle adversaries and are
not used here: a circuit reading the whole truth table queries every leaf, so the hybrids are over
complete levels of the tree.

## Main definitions

* `Cslib.Crypto.GGM.evalBits`: evaluation of the GGM tree with labels of fixed width.
* `Cslib.Crypto.GGM.booleanFamily`: the GGM family of Boolean functions.
* `Cslib.Crypto.PRG.IsSubexponentiallySecure`: generators resisting circuits of size
  `2 ^ (k ^ (1 / d))`.

## Main results

* `Cslib.Crypto.GGM.ofFn_evalBits`: agreement with the list construction `Cslib.Crypto.GGM.eval`.
* `Cslib.Crypto.GGM.complexity_booleanFamily_le`: the members have circuits of size
  `n (C + 4 k) + 2`.
* `Cslib.Crypto.GGM.secure_truthTableGenerator_booleanFamily`: security against circuits, with
  explicit loss in size and advantage.
* `Cslib.Crypto.PRG.IsSubexponentiallySecure.of_rpow`: security against circuits of size
  `2 ^ (k ^ ε)` gives subexponential security.
* `Cslib.Crypto.GGM.isExponentiallySecure_booleanFamily`: subexponentially secure generators give
  exponentially secure families.
* `Cslib.Circuits.Boolean.not_isUseful_PPoly_of_isNatural_of_generator`: the natural proofs
  barrier from subexponentially secure generators.

## References

* [O. Goldreich, S. Goldwasser, S. Micali, *How to construct random functions*][GGM1986]
* [A. A. Razborov, S. Rudich, *Natural proofs*][RazborovRudich1997]
-/

@[expose] public section

namespace Cslib.Crypto.GGM

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.MCSP Finset Function
open scoped BigOperators NNReal

variable {k n : ℕ}

/-! ### Evaluation with labels of fixed width -/

/-- The half of a string of length `2 k` selected by a bit: the first `k` bits for `false`, the
last `k` bits for `true`. -/
def half (y : BitString (2 * k)) (bit : Bool) : BitString k :=
  fun i => y ⟨bit.toNat * k + i, by cases bit <;> simp <;> omega⟩

/-- Evaluate the GGM tree with labels of width `k` [GGM1986]: starting from the seed, replace the
label by the half of its expansion selected by each query bit in turn, from the first bit of the
query to the last. -/
def evalBits (G : PRG.Generator (BitString k) (BitString (2 * k))) :
    {n : ℕ} → BitString k → BitString n → BitString k
  | 0, seed, _ => seed
  | _ + 1, seed, x => evalBits G (half (G seed) (x 0)) (Fin.tail x)

@[simp] theorem evalBits_zero (G : PRG.Generator (BitString k) (BitString (2 * k)))
    (seed : BitString k) (x : BitString 0) : evalBits G seed x = seed :=
  rfl

theorem evalBits_succ (G : PRG.Generator (BitString k) (BitString (2 * k)))
    (seed : BitString k) (x : BitString (n + 1)) :
    evalBits G seed x = evalBits G (half (G seed) (x 0)) (Fin.tail x) :=
  rfl

/-- A generator of fixed-width strings as a generator of lists: it reads the first `k` bits of its
input, taking missing bits to be `false`. -/
def listGenerator (G : PRG.Generator (BitString k) (BitString (2 * k))) :
    List Bool → List Bool :=
  fun seed => List.ofFn (G fun i => seed.getD i false)

/-- The half selected by a bit is the child selected by `Cslib.Crypto.GGM.selectChild`. -/
theorem ofFn_half (y : BitString (2 * k)) (bit : Bool) :
    List.ofFn (half y bit) = selectChild k (List.ofFn y) bit := by
  apply List.ext_getElem
  · cases bit <;> simp [selectChild] <;> omega
  · intro i _ _
    cases bit <;> simp [selectChild, half]

/-- **Agreement with the list construction.** Evaluation with labels of fixed width is
`Cslib.Crypto.GGM.eval` for the generator read as a generator of lists. -/
theorem ofFn_evalBits (G : PRG.Generator (BitString k) (BitString (2 * k)))
    (seed : BitString k) (x : BitString n) :
    List.ofFn (evalBits G seed x) = eval (listGenerator G) (List.ofFn seed) (List.ofFn x) := by
  induction n generalizing seed with
  | zero => simp
  | succ n ih =>
    rw [evalBits_succ, ih, List.ofFn_succ, eval_cons]
    congr 1
    rw [child, List.length_ofFn, ofFn_half, listGenerator]
    congr 3
    funext i
    simp

/-- **The GGM family of Boolean functions** [RazborovRudich1997]: the function with key `seed`
maps an input of `n` bits to the first bit of the label it reaches in the GGM tree. -/
def booleanFamily [NeZero k] (G : PRG.Generator (BitString k) (BitString (2 * k))) (n : ℕ)
    (seed : BitString k) : BooleanFunction n :=
  fun x => evalBits G seed x 0

/-! ### Circuits for tree evaluation -/

/-- Evaluation along a fixed query of length `n` costs at most `n` copies of a circuit for the
generator: as a function of the seed, each step is the generator followed by a wiring. -/
theorem complexity_evalBits_le (G : PRG.Generator (BitString k) (BitString (2 * k)))
    (x : BitString n) :
    complexity interpretation (fun seed => evalBits G seed x) ≤
      n * complexity interpretation ⇑G := by
  induction n with
  | zero =>
    have h : (fun seed : BitString k => evalBits G seed x) = fun seed => seed ∘ id := rfl
    rw [h, complexity_wiring, zero_mul]
  | succ n ih =>
    have h : (fun seed : BitString k => evalBits G seed x) =
        (fun seed => evalBits G seed (Fin.tail x)) ∘ (fun y => y ∘ fun i : Fin k =>
          (⟨(x 0).toNat * k + i, by cases x 0 <;> simp <;> omega⟩ : Fin (2 * k))) ∘ ⇑G := rfl
    have hstep := complexity_comp_le (I := interpretation) ⇑G (fun y => y ∘ fun i : Fin k =>
      (⟨(x 0).toNat * k + i, by cases x 0 <;> simp <;> omega⟩ : Fin (2 * k)))
    rw [complexity_wiring, add_zero] at hstep
    rw [h]
    calc _ ≤ _ := complexity_comp_le _ _
      _ ≤ complexity interpretation ⇑G + n * complexity interpretation ⇑G :=
          add_le_add hstep (ih (Fin.tail x))
      _ = (n + 1) * complexity interpretation ⇑G := by ring

/-- One bit of the evaluation along a fixed query of length `n`, as a function of a string of
length `2 k` whose selected half is the seed, costs at most `n` copies of a circuit for the
generator. -/
theorem complexity_evalBits_half_le (G : PRG.Generator (BitString k) (BitString (2 * k)))
    (bit : Bool) (x : BitString n) (i : Fin k) :
    complexity interpretation (single fun y => evalBits G (half y bit) x i) ≤
      n * complexity interpretation ⇑G := by
  have h : (single fun y => evalBits G (half y bit) x i) =
      (fun z => z ∘ fun _ : Fin 1 => i) ∘ (fun seed => evalBits G seed x) ∘
        (fun y => y ∘ fun i : Fin k =>
          (⟨bit.toNat * k + i, by cases bit <;> simp <;> omega⟩ : Fin (2 * k))) := rfl
  rw [h]
  refine (complexity_comp_le _ _).trans ?_
  rw [complexity_wiring, add_zero]
  refine (complexity_comp_le _ _).trans ?_
  rw [complexity_wiring, zero_add]
  exact complexity_evalBits_le G x

/-- **Circuits for tree evaluation.** If the bits of a seed and of a query of length `n` are
available, the bits of the label reached are synthesized with, per query bit, a smallest circuit
for the generator and `k` multiplexers of four gates. -/
theorem synthesis_evalBits {N : ℕ} (G : PRG.Generator (BitString k) (BitString (2 * k)))
    {s : Set (BooleanFunction N)} (seed : BitString N → BitString k)
    (query : BitString N → BitString n) (hseed : ∀ i, (fun z => seed z i) ∈ s)
    (hquery : ∀ i, (fun z => query z i) ∈ s) :
    Synthesis interpretation s (Set.range fun i z => evalBits G (seed z) (query z) i)
      (n * (complexity interpretation ⇑G + 4 * k)) := by
  induction n generalizing s seed with
  | zero =>
    rw [zero_mul]
    exact Synthesis.of_subset (Set.range_subset_iff.2 hseed)
  | succ n ih =>
    obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := ⇑G)
    -- the expansion of the current label, by a smallest circuit for the generator
    have h1 : Synthesis interpretation s (Set.range fun j z => G (seed z) j)
        (complexity interpretation ⇑G) := by
      have h := Synthesis.circuit (I := interpretation) c (fun i z => seed z i) hseed
      rw [hsize] at h
      convert h using 3 with j
      funext z
      exact (congrFun (hc (seed z)) j).symm
    -- the half selected by the first query bit, by one multiplexer per bit
    have h2 : Synthesis interpretation (s ∪ Set.range fun j z => G (seed z) j)
        (Set.range fun i z => half (G (seed z)) (query z 0) i) (4 * k) := by
      have h := Synthesis.family (I := interpretation)
        (s := s ∪ Set.range fun j z => G (seed z) j)
        (fun i : Fin k => fun z => half (G (seed z)) (query z 0) i) (fun _ => 4) fun i => by
          have hmux := Synthesis.mux (s := s ∪ Set.range fun j z => G (seed z) j)
            (Or.inl (hquery 0)) (Or.inr ⟨⟨1 * k + i, by omega⟩, rfl⟩)
            (Or.inr ⟨⟨0 * k + i, by omega⟩, rfl⟩)
          convert hmux using 2
          funext z
          cases query z 0 <;> rfl
      simpa [mul_comm] using h
    have h3 := ih (s := s ∪ Set.range fun i z => half (G (seed z)) (query z 0) i)
      (fun z => half (G (seed z)) (query z 0)) (fun z => Fin.tail (query z))
      (fun i => Or.inr ⟨i, rfl⟩) (fun i => Or.inl (hquery i.succ))
    exact ((h1.trans h2).trans h3).mono Set.Subset.rfl Set.Subset.rfl (le_of_eq (by ring))

/-- **The members of the GGM family have small circuits**: two constants for the key, then per
input bit a smallest circuit for the generator and `k` multiplexers of four gates. -/
theorem complexity_booleanFamily_le [NeZero k]
    (G : PRG.Generator (BitString k) (BitString (2 * k))) (n : ℕ) (seed : BitString k) :
    complexity interpretation (single (booleanFamily G n seed)) ≤
      n * (complexity interpretation ⇑G + 4 * k) + 2 := by
  refine Synthesis.complexity_le ?_
  have hconst := (Synthesis.const (s := inputs n) false).union (Synthesis.const true)
  have h := synthesis_evalBits G (s := inputs n ∪ ({fun _ => false} ∪ {fun _ => true}))
    (fun _ => seed) id (fun i => by cases seed i <;> simp) (fun i => Or.inl ⟨i, rfl⟩)
  exact (hconst.trans h).mono Set.Subset.rfl (Set.singleton_subset_iff.2 ⟨0, rfl⟩)
    (le_of_eq (add_comm _ _))

/-! ### The hybrid argument for independent samples -/

section Independent

variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α] [Fintype β]
  [Nonempty β]

/-- Resampling one coordinate of a uniformly random function keeps it uniformly random. -/
private theorem expect_expect_update (F : (ι → α) → ℝ) (i : ι) :
    𝔼 s, 𝔼 a, F (update s i a) = 𝔼 s, F s := by
  let e : Equiv.Perm ((ι → α) × α) :=
    Function.Involutive.toPerm (fun p => (update p.1 i p.2, p.1 i)) fun p => by simp
  calc 𝔼 s, 𝔼 a, F (update s i a) = 𝔼 p : (ι → α) × α, F (e p).1 :=
        (Fintype.expect_prod_type (fun p : (ι → α) × α => F (e p).1)).symm
    _ = 𝔼 p : (ι → α) × α, F p.1 := Fintype.expect_equiv e _ _ fun _ => rfl
    _ = 𝔼 s, F s := Fintype.expect_comp_fst F

/-- **The hybrid argument for independent samples.** Let `T` be a statistic of `ι`-indexed tuples
in `β`. If, with all other coordinates fixed, replacing `g a` for a uniform `a` by a uniform `b` at
one coordinate changes the average of `T` by at most `ε`, then replacing every coordinate changes
it by at most `|ι| ε`. -/
private theorem abs_expect_comp_sub_expect_le (g : α → β) (T : (ι → β) → ℝ) {ε : ℝ}
    (hT : ∀ (c : ι → β) (i : ι), |𝔼 a, T (update c i (g a)) - 𝔼 b, T (update c i b)| ≤ ε) :
    |𝔼 s : ι → α, T (fun i => g (s i)) - 𝔼 y : ι → β, T y| ≤ Fintype.card ι * ε := by
  -- the hybrid in which the coordinates in `S` are uniform
  let v : Finset ι → (ι → α) → (ι → β) → ι → β := fun S s y j => if j ∈ S then y j else g (s j)
  let H : Finset ι → ℝ := fun S => 𝔼 s, 𝔼 y, T (v S s y)
  have hstep (i : ι) (S : Finset ι) (hi : i ∉ S) : |H S - H (insert i S)| ≤ ε := by
    have hS : H S = 𝔼 s, 𝔼 y, 𝔼 a, T (update (v S s y) i (g a)) := by
      change 𝔼 s, 𝔼 y, T (v S s y) = _
      rw [← expect_expect_update (fun s => 𝔼 y, T (v S s y)) i]
      refine expect_congr rfl fun s _ => ?_
      rw [expect_comm]
      refine expect_congr rfl fun y _ => expect_congr rfl fun a _ => congrArg T ?_
      funext j
      by_cases hj : j = i
      · subst hj; simp [v, hi]
      · simp [v, hj]
    have hS' : H (insert i S) = 𝔼 s, 𝔼 y, 𝔼 b, T (update (v S s y) i b) := by
      change 𝔼 s, 𝔼 y, T (v (insert i S) s y) = _
      refine expect_congr rfl fun s _ => ?_
      rw [← expect_expect_update (fun y => T (v (insert i S) s y)) i]
      refine expect_congr rfl fun y _ => expect_congr rfl fun b _ => congrArg T ?_
      funext j
      by_cases hj : j = i
      · subst hj; simp [v]
      · simp [v, hj]
    rw [hS, hS', ← expect_sub_distrib]
    refine (abs_expect_le _ _).trans ?_
    refine (expect_le_expect fun s _ => ?_).trans_eq (Fintype.expect_const ε)
    rw [← expect_sub_distrib]
    refine (abs_expect_le _ _).trans ?_
    refine (expect_le_expect fun y _ => ?_).trans_eq (Fintype.expect_const ε)
    exact hT _ i
  have hind (S : Finset ι) : |H ∅ - H S| ≤ S.card * ε := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert i S hi ih =>
      calc |H ∅ - H (insert i S)| ≤ |H ∅ - H S| + |H S - H (insert i S)| := abs_sub_le _ _ _
        _ ≤ S.card * ε + ε := add_le_add ih (hstep i S hi)
        _ = (insert i S).card * ε := by rw [card_insert_of_notMem hi]; push_cast; ring
  have h0 : H ∅ = 𝔼 s : ι → α, T (fun i => g (s i)) := by
    simp only [H, v, notMem_empty, ite_false, Fintype.expect_const]
  have h1 : H univ = 𝔼 y : ι → β, T y := by
    simp only [H, v, mem_univ, ite_true, Fintype.expect_const]
  simpa only [h0, h1, card_univ] using hind univ

omit [DecidableEq ι] [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] in
/-- The first bits of uniformly random labels are uniformly random. -/
private theorem expect_comp_apply_zero [DecidableEq ι] [NeZero k] (F : (ι → Bool) → ℝ) :
    𝔼 L : ι → BitString k, F (fun x => L x 0) = 𝔼 f, F f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  let e : (ι → Fin (k + 1) → Bool) ≃ (ι → Bool) × (ι → Fin k → Bool) :=
    (Equiv.arrowCongr (Equiv.refl ι) (Fin.consEquiv fun _ => Bool).symm).trans
      (Equiv.arrowProdEquivProdArrow _ _ _)
  rw [← Fintype.expect_comp_fst (β := ι → Fin k → Bool) F]
  exact Fintype.expect_equiv e _ _ fun _ => rfl

end Independent

/-! ### The GGM hybrids -/

section Hybrids

variable {j m : ℕ}

/-- The leaves of a hybrid tree of depth `n = j + m`: the labels at depth `j` are given, and the
remaining `m` levels are expanded by the generator. -/
private def leaves (G : PRG.Generator (BitString k) (BitString (2 * k))) (j m : ℕ)
    (h : j + m = n) (labels : BitString j → BitString k) (x : BitString n) : BitString k :=
  evalBits G (labels fun i : Fin j => x ⟨i, by omega⟩) fun i : Fin m => x ⟨j + i, by omega⟩

/-- The labels at depth `j + 1` given by the expansions of the labels at depth `j`. -/
private def reshape (Y : BitString j → BitString (2 * k)) : BitString (j + 1) → BitString k :=
  fun p => half (Y (Fin.init p)) (p (Fin.last j))

/-- Expanding one level of a hybrid tree. -/
private theorem leaves_succ (G : PRG.Generator (BitString k) (BitString (2 * k)))
    (h : j + (m + 1) = n) (labels : BitString j → BitString k) :
    leaves G j (m + 1) h labels =
      leaves G (j + 1) m (by omega) (reshape fun q => G (labels q)) := by
  funext x
  rw [leaves, evalBits_succ]
  congr 1
  funext i
  simp only [Fin.tail, Fin.val_succ]
  congr 1
  ext
  simp only
  omega

/-- The expansions of the labels at depth `j` determine the labels at depth `j + 1`, and
conversely. -/
private theorem bijective_reshape :
    Bijective (reshape : (BitString j → BitString (2 * k)) → BitString (j + 1) → BitString k) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun Y Y' hY => ?_, ?_⟩
  · funext q i
    by_cases hi : (i : ℕ) < k
    · have := congrFun (congrFun hY (Fin.snoc (α := fun _ => Bool) q false)) ⟨i, hi⟩
      simpa [reshape, half, Fin.init_snoc, Fin.snoc_last] using this
    · have := congrFun (congrFun hY (Fin.snoc (α := fun _ => Bool) q true)) ⟨i - k, by omega⟩
      simp only [reshape, half, Fin.init_snoc, Fin.snoc_last, Bool.toNat_true, one_mul] at this
      convert this using 2 <;> ext <;> simp <;> omega
  · simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul]
    ring_nf

variable [NeZero k]

/-- The probability that a test of truth tables accepts the hybrid with uniformly random labels at
depth `j`. -/
private noncomputable def hybridProb (G : PRG.Generator (BitString k) (BitString (2 * k)))
    (D : BitString (2 ^ n) → Bool) (j m : ℕ) (h : j + m = n) : ℝ :=
  𝔼 labels : BitString j → BitString k,
    if D (truthTable n fun x => leaves G j m h labels x 0) then 1 else 0

/-- **One hybrid step.** If no test obtained from `D` by fixing all expansions at depth `j` but
one distinguishes the generator with advantage more than `ε`, the hybrids at depths `j` and
`j + 1` differ by at most `2 ^ j ε`. -/
private theorem abs_hybridProb_sub_le (G : PRG.Generator (BitString k) (BitString (2 * k)))
    (D : BitString (2 ^ n) → Bool) (h : j + (m + 1) = n) {ε : ℝ}
    (hε : ∀ (c : BitString j → BitString (2 * k)) (q : BitString j),
      |𝔼 a, (if D (truthTable n fun x =>
          leaves G (j + 1) m (by omega) (reshape (update c q (G a))) x 0) then 1 else 0 : ℝ) -
        𝔼 b, (if D (truthTable n fun x =>
          leaves G (j + 1) m (by omega) (reshape (update c q b)) x 0) then 1 else 0 : ℝ)| ≤ ε) :
    |hybridProb G D j (m + 1) h - hybridProb G D (j + 1) m (by omega)| ≤ 2 ^ j * ε := by
  have h0 : hybridProb G D j (m + 1) h = 𝔼 labels : BitString j → BitString k,
      (if D (truthTable n fun x => leaves G (j + 1) m (by omega)
        (reshape fun q => G (labels q)) x 0) then 1 else 0 : ℝ) := by
    simp only [hybridProb, leaves_succ G h]
  have h1 : hybridProb G D (j + 1) m (by omega) = 𝔼 Y : BitString j → BitString (2 * k),
      (if D (truthTable n fun x => leaves G (j + 1) m (by omega) (reshape Y) x 0)
        then 1 else 0 : ℝ) :=
    (Fintype.expect_bijective _ bijective_reshape _ _ fun _ => rfl).symm
  rw [h0, h1]
  simpa [BitString, Fintype.card_fun] using abs_expect_comp_sub_expect_le ⇑G
    (fun Y => (if D (truthTable n fun x => leaves G (j + 1) m (by omega) (reshape Y) x 0)
      then 1 else 0 : ℝ)) hε

/-- **The size of the reduction.** Fixing all expansions at depth `j` but the one at `q`, a test
of truth tables becomes a test of that expansion. Each bit of the truth table is then a constant or
a bit of the evaluation along the remaining `m` levels, so the test costs at most `2 ^ n (m C + 1)`
gates more than the test of truth tables, where `C` is the circuit complexity of the
generator. -/
private theorem complexity_slice_le (G : PRG.Generator (BitString k) (BitString (2 * k)))
    (D : BitString (2 ^ n) → Bool) (h : j + 1 + m = n)
    (c : BitString j → BitString (2 * k)) (q : BitString j) :
    complexity interpretation (single fun y => D (truthTable n fun x =>
        leaves G (j + 1) m h (reshape (update c q y)) x 0)) ≤
      2 ^ n * (m * complexity interpretation ⇑G + 1) + complexity interpretation (single D) := by
  refine (complexity_comp_le (fun y => truthTable n fun x =>
    leaves G (j + 1) m h (reshape (update c q y)) x 0) (single D)).trans
    (Nat.add_le_add_right ?_ _)
  refine (complexity_pi_le (I := interpretation) fun i y => truthTable n (fun x =>
    leaves G (j + 1) m h (reshape (update c q y)) x 0) i).trans ?_
  refine (sum_le_sum (g := fun _ => m * complexity interpretation ⇑G + 1) fun i _ => ?_).trans_eq
    (by simp)
  -- the bit of the truth table at the input `x`
  set x := (BitString.equivFin n).symm i
  set p : BitString (j + 1) := fun l => x ⟨l, by omega⟩
  by_cases hp : Fin.init p = q
  · have he : (fun y => truthTable n (fun x =>
        leaves G (j + 1) m h (reshape (update c q y)) x 0) i) =
        fun y => evalBits G (half y (p (Fin.last j))) (fun l : Fin m => x ⟨j + 1 + l, by omega⟩)
          0 := by
      funext y
      simp only [truthTable_apply, leaves, reshape]
      rw [← hp, update_self]
    rw [he]
    exact (complexity_evalBits_half_le G _ _ 0).trans (Nat.le_succ _)
  · have he : (fun y => truthTable n (fun x =>
        leaves G (j + 1) m h (reshape (update c q y)) x 0) i) =
        fun _ => evalBits G (half (c (Fin.init p)) (p (Fin.last j)))
          (fun l : Fin m => x ⟨j + 1 + l, by omega⟩) 0 := by
      funext y
      simp only [truthTable_apply, leaves, reshape]
      rw [update_of_ne hp]
    rw [he]
    exact (Synthesis.const _).complexity_le.trans (Nat.le_add_left _ _)

/-- The first hybrid is the GGM family with a uniformly random key. -/
private theorem hybridProb_zero (G : PRG.Generator (BitString k) (BitString (2 * k)))
    (D : BitString (2 ^ n) → Bool) :
    hybridProb G D 0 n (zero_add n) =
      ((truthTableGenerator (booleanFamily G n)).realExperiment
        (fun T => PMF.pure (D T)) true).toReal := by
  rw [PRG.Generator.toReal_realExperiment_pure, ← Fintype.expect_boole, hybridProb]
  refine Fintype.expect_equiv (Equiv.funUnique (BitString 0) (BitString k)) _ _ fun L => ?_
  have hx (x : BitString n) : (fun i : Fin n => x ⟨0 + i, by omega⟩) = x :=
    funext fun i => congrArg x (Fin.ext (zero_add _))
  have hL (x : BitString n) : L (fun i : Fin 0 => x ⟨i, by omega⟩) =
      Equiv.funUnique (BitString 0) (BitString k) L :=
    congrArg L (Subsingleton.elim _ _)
  simp only [leaves, hx, hL, truthTableGenerator_apply]
  rfl

/-- The last hybrid is a uniformly random function. -/
private theorem hybridProb_self (G : PRG.Generator (BitString k) (BitString (2 * k)))
    (D : BitString (2 ^ n) → Bool) :
    hybridProb G D n 0 (add_zero n) =
      (PRG.Generator.idealExperiment (fun T => PMF.pure (D T)) true).toReal := by
  rw [PRG.Generator.toReal_idealExperiment_pure, ← Fintype.expect_boole,
    ← Fintype.expect_equiv (truthTable n) (fun f => if D (truthTable n f) then (1 : ℝ) else 0) _
      fun _ => rfl, ← expect_comp_apply_zero (k := k), hybridProb]
  rfl

end Hybrids

/-! ### Security of the GGM family against circuits -/

/-- **The GGM family is pseudorandom against circuits** [GGM1986], [RazborovRudich1997]. Let `G`
be a length-doubling generator with labels of width `k ≥ 1` whose circuit complexity is `C`. If no
test computed with `t + 2 ^ n (n C + 1)` gates distinguishes the output of `G` from uniform with
advantage more than `ε`, then no test computed with `t` gates distinguishes the truth table of the
GGM function on `n` inputs with a uniformly random key from a uniformly random truth table with
advantage more than `(2 ^ n - 1) ε`.

The proof is the hybrid argument over the levels of the tree, where the hybrid at depth `j`
labels the nodes at depth `j` uniformly at random. Between depths `j` and `j + 1` the `2 ^ j`
expansions are replaced by uniform strings one at a time; fixing the others, a test of truth
tables computes the subtree below the remaining one with at most `2 ^ n (n C + 1)` more
gates. -/
theorem secure_truthTableGenerator_booleanFamily [NeZero k]
    {G : PRG.Generator (BitString k) (BitString (2 * k))} {t : ℕ} {ε : ℝ≥0}
    (hG : G.Secure (IsCircuitTest (t + 2 ^ n * (n * complexity interpretation ⇑G + 1))) ε) :
    (truthTableGenerator (booleanFamily G n)).Secure (IsCircuitTest t) ((2 ^ n - 1) * ε) := by
  rintro _ ⟨D, hD, rfl⟩
  -- the hybrids at depths `j` and `n` differ by at most `(2 ^ n - 2 ^ j) ε`
  have htel (m : ℕ) : ∀ j (h : j + m = n),
      |hybridProb G D j m h - hybridProb G D n 0 (add_zero n)| ≤ (2 ^ n - 2 ^ j) * ε := by
    induction m with
    | zero =>
      intro j h
      subst h
      simp
    | succ m ih =>
      intro j h
      have hstep := abs_hybridProb_sub_le G D h (ε := ε) fun c q => by
        have hslice := complexity_slice_le G D (j := j) (m := m) (by omega) c q
        have hadv := hG (fun y => PMF.pure (D (truthTable n fun x =>
          leaves G (j + 1) m (by omega) (reshape (update c q y)) x 0)))
          ⟨_, hslice.trans (by rw [add_comm]; gcongr; omega), rfl⟩
        rwa [PRG.Generator.advantage, PRG.Generator.toReal_realExperiment_pure,
          PRG.Generator.toReal_idealExperiment_pure, ← Fintype.expect_boole,
          ← Fintype.expect_boole] at hadv
      calc _ ≤ |hybridProb G D j (m + 1) h - hybridProb G D (j + 1) m (by omega)| +
            |hybridProb G D (j + 1) m (by omega) - hybridProb G D n 0 (add_zero n)| :=
            abs_sub_le _ _ _
        _ ≤ 2 ^ j * ε + (2 ^ n - 2 ^ (j + 1)) * ε := add_le_add hstep (ih (j + 1) (by omega))
        _ = (2 ^ n - 2 ^ j) * ε := by ring
  have h := htel n 0 (zero_add n)
  rw [hybridProb_zero, hybridProb_self, pow_zero] at h
  rw [PRG.Generator.advantage, NNReal.coe_mul, NNReal.coe_sub (one_le_pow₀ one_le_two),
    NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_one]
  exact h

end Cslib.Crypto.GGM

namespace Cslib.Crypto.PRG

open scoped NNReal

/-- A family of length-doubling generators is *subexponentially secure* against circuits, with
exponent `1 / d`, when on seeds of length `k` no test computed with at most `2 ^ m` gates has
advantage more than `2 ^ (-m)` against `G k`, for every `m` with `m ^ d ≤ k`. Up to rounding,
`G k` resists circuits of size `2 ^ (k ^ ε)` with advantage `2 ^ (-k ^ ε)` for `ε = 1 / d`, the
hypothesis of [RazborovRudich1997]. -/
def IsSubexponentiallySecure (G : ∀ k, Generator (BitString k) (BitString (2 * k))) (d : ℕ) :
    Prop :=
  ∀ k m, m ^ d ≤ k → (G k).Secure (Circuits.Boolean.IsCircuitTest (2 ^ m)) (2 ^ m)⁻¹

/-- A generator family secure against circuits of size `2 ^ (k ^ ε)` with advantage
`2 ^ (-k ^ ε)`, for some `ε > 0`, is subexponentially secure with exponent `1 / d` for every
`d ≥ 1 / ε`. -/
theorem IsSubexponentiallySecure.of_rpow {G : ∀ k, Generator (BitString k) (BitString (2 * k))}
    {ε : ℝ} {d : ℕ} (hd : 1 ≤ d * ε)
    (hG : ∀ k, (G k).Secure (Circuits.Boolean.IsCircuitTest ⌊(2 : ℝ) ^ ((k : ℝ) ^ ε)⌋₊)
      ((2 : ℝ≥0) ^ ((k : ℝ) ^ ε))⁻¹) :
    IsSubexponentiallySecure G d := by
  intro k m hm
  have hmk : (m : ℝ) ≤ (k : ℝ) ^ ε := by
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp only [CharP.cast_eq_zero]; positivity
    have hε : 0 < ε := by
      rcases le_or_gt ε 0 with h | h
      · nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
      · exact h
    calc (m : ℝ) = (m : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (m : ℝ) ^ ((d : ℝ) * ε) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm0) hd
      _ = ((m : ℝ) ^ d) ^ ε := by rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
      _ ≤ (k : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hm) hε.le
  have hsize : 2 ^ m ≤ ⌊(2 : ℝ) ^ ((k : ℝ) ^ ε)⌋₊ := by
    refine Nat.le_floor ?_
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two hmk
  have herr : ((2 : ℝ≥0) ^ ((k : ℝ) ^ ε))⁻¹ ≤ (2 ^ m)⁻¹ := by
    refine inv_anti₀ (by positivity) ?_
    rw [← NNReal.rpow_natCast]
    exact NNReal.rpow_le_rpow_of_exponent_le one_le_two hmk
  exact ((hG k).of_admissible fun A ⟨test, htest, hA⟩ => ⟨test, htest.trans hsize, hA⟩).mono herr

end Cslib.Crypto.PRG

namespace Cslib.Crypto.GGM

open Cslib.Circuits Cslib.Circuits.Boolean Filter
open scoped NNReal

/-- **The GGM family from a subexponentially secure generator is exponentially secure**
[GGM1986], [RazborovRudich1997, Section 4]. Let `G` be a family of length-doubling generators of
polynomial circuit complexity, subexponentially secure with exponent `1 / d`. With keys of length
`(n + 1) ^ (2 d)`, the GGM functions on `n` inputs are pseudorandom against circuits of size
`2 ^ (c n)` with error `2 ^ (-c n)` for every `c` and all large `n`. -/
theorem isExponentiallySecure_booleanFamily
    {G : ∀ k, PRG.Generator (BitString k) (BitString (2 * k))} {d : ℕ}
    (hsize : PolynomiallyBounded fun k => complexity interpretation ⇑(G k))
    (hG : PRG.IsSubexponentiallySecure G d) :
    IsExponentiallySecure fun n => booleanFamily (G ((n + 1) ^ (2 * d))) n := by
  intro c
  have hpoly : PolynomiallyBounded fun n =>
      n * complexity interpretation ⇑(G ((n + 1) ^ (2 * d))) + 1 := by
    have := hsize.comp (g := fun n => (n + 1) ^ (2 * d)) (by fun_prop)
    fun_prop
  filter_upwards [hpoly.eventually_lt_two_pow, eventually_ge_atTop (c + 3)] with n hn hc
  -- the generator resists circuits with `2 ^ (n ^ 2)` gates
  have hsec : (G ((n + 1) ^ (2 * d))).Secure (IsCircuitTest (2 ^ (n ^ 2))) (2 ^ (n ^ 2))⁻¹ :=
    hG _ _ (by
      rw [← pow_mul]
      exact Nat.pow_le_pow_left (Nat.le_succ n) _)
  -- which exceeds the size of the reduction
  have hsize : 2 ^ (c * n) + 2 ^ n * (n * complexity interpretation ⇑(G ((n + 1) ^ (2 * d))) + 1)
      ≤ 2 ^ (n ^ 2) := by
    have h1 : 2 ^ (c * n) ≤ 2 ^ ((c + 3) * n - 1) := Nat.pow_le_pow_right two_pos (by
      rw [add_mul]; omega)
    have h2 : 2 ^ n * (n * complexity interpretation ⇑(G ((n + 1) ^ (2 * d))) + 1) ≤
        2 ^ ((c + 3) * n - 1) := by
      calc _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul_left _ hn.le
        _ = 2 ^ (2 * n) := by rw [← pow_add, two_mul]
        _ ≤ _ := Nat.pow_le_pow_right two_pos (by rw [add_mul]; omega)
    calc _ ≤ 2 * 2 ^ ((c + 3) * n - 1) := by omega
      _ = 2 ^ ((c + 3) * n) := by
          rw [← pow_succ']
          congr 1
          have : 1 ≤ (c + 3) * n := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
          omega
      _ ≤ 2 ^ (n ^ 2) := Nat.pow_le_pow_right two_pos (by rw [sq]; exact Nat.mul_le_mul_right _ hc)
  refine (secure_truthTableGenerator_booleanFamily ((hsec.of_admissible fun A ⟨test, htest, hA⟩ =>
    ⟨test, htest.trans hsize, hA⟩))).mono ?_
  -- and the loss `2 ^ n` in the advantage is absorbed
  have hpow : (2 : ℝ≥0) ^ n * 2 ^ (c * n) ≤ 2 ^ (n ^ 2) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ one_le_two (by rw [sq]; nlinarith)
  calc ((2 : ℝ≥0) ^ n - 1) * (2 ^ (n ^ 2))⁻¹ ≤ 2 ^ n * (2 ^ n * 2 ^ (c * n))⁻¹ := by
        gcongr
        exact tsub_le_self
    _ = (2 ^ (c * n))⁻¹ := by
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

end Cslib.Crypto.GGM

namespace Cslib.Circuits.Boolean

/-- **The natural proofs barrier from pseudorandom generators** [RazborovRudich1997, Section 4].
If a family of length-doubling generators of polynomial circuit complexity is subexponentially
secure against circuits, then no `P/poly`-natural property is useful against `P/poly`. The GGM
functions with keys of length polynomial in the number of inputs form an exponentially secure keyed
family whose members have circuits of polynomial size
(`Cslib.Crypto.GGM.isExponentiallySecure_booleanFamily`,
`Cslib.Crypto.GGM.complexity_booleanFamily_le`). -/
theorem not_isUseful_PPoly_of_isNatural_of_generator
    {G : ∀ k, Crypto.PRG.Generator (BitString k) (BitString (2 * k))} {d : ℕ}
    (hsize : PolynomiallyBounded fun k => complexity interpretation ⇑(G k))
    (hG : Crypto.PRG.IsSubexponentiallySecure G d) {C : ∀ n, Set (BooleanFunction n)}
    (hC : IsNatural PPoly C) : ¬ IsUseful PPoly C := by
  have hkey : PolynomiallyBounded fun n => (n + 1) ^ (2 * d) := by fun_prop
  have hcomp := hsize.comp hkey
  exact not_isUseful_PPoly_of_isNatural (s := fun n =>
      n * (complexity interpretation ⇑(G ((n + 1) ^ (2 * d))) + 4 * (n + 1) ^ (2 * d)) + 2)
    (by fun_prop) (fun n => Crypto.GGM.complexity_booleanFamily_le _ n)
    (Crypto.GGM.isExponentiallySecure_booleanFamily hsize hG) hC

end Cslib.Circuits.Boolean
