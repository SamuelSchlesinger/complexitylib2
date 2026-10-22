/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.ModGates
public import Complexity.Computability.Circuit.Boolean.ModMajority
public import Complexity.Computability.Circuit.Boolean.ThresholdNC1
public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Complexity.Classes.Inclusions
public import Complexity.Computability.Complexity.Classes.PH.Kannan
import Complexity.Computability.Circuit.Boolean.PPolyHard
import Complexity.Computability.Circuit.Boolean.Smolensky.Majority
import Complexity.Computability.Complexity.Classes.PH.KarpLipton
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Foundations.Data.Nat.PolynomialBound.Log

/-!
# ACC⁰, fast `Sym⁺` evaluation, and modular circuit lower bounds

**ACC⁰** (`Cslib.Circuits.Boolean.ACC0`) is the union of the modular constant-depth circuit classes
`AC0Mod q` over all fixed moduli `q ≥ 2` [Barrington1989], [Vollmer, Chapter 4][Vollmer1999],
[Arora and Barak, Section 14.2][AroraBarak09]: the languages over `Bool` decided at every input
length by polynomial-size, constant-depth nonuniform circuits over negations, unbounded fan-in
conjunctions and disjunctions, and unbounded fan-in `MOD_q` gates (`modGate q`). Since `modGate 0`
is disjunction and `modGate 1` is the constant `false`, the union over all `q : ℕ` gives the same
class (`ACC0_eq_iUnion_AC0Mod`).

Repeating each input wire of a `MOD_q` gate `k ≥ 1` times multiplies the Hamming weight by `k`, and
`(w * k) % (q * k) = (w % q) * k`, so a single `MOD_{q * k}` gate simulates a `MOD_q` gate
(`AC0Mod_subset_AC0Mod_mul_right`, `AC0Mod_subset_AC0Mod_of_dvd`). Two circuits with moduli `q₁`
and `q₂` therefore embed into the common modulus `q₁ * q₂`, making `ACC0` closed under complement,
intersection, and union (`ACC0.compl`, `ACC0.inf`, `ACC0.sup`).

Every `AC0Mod q` is contained in `TC0` (`AC0Mod_subset_TC0`, hence `ACC0_subset_TC0`), and
replacing the majority gate in `modCircuitOfMajority` by the logarithmic-depth De Morgan majority
circuit (`majorityDeMorganCircuit`) embeds `ACMod q i ⊆ AC (i + 1) ⊆ NC (i + 2)` and
`ACC0 ⊆ AC 1 ⊆ NC 2 ⊆ PPoly` (`AC0Mod_subset_AC_one`, `ACC0_subset_AC_one`,
`ACC0_subset_NC_two`, `ACC0_subset_PPoly`). By Håstad's and Razborov–Smolensky's lower bounds for
parity, `AC0 ⊂ AC0Mod 2 ⊆ ACC0` (`AC0_ssubset_AC0Mod_two`, `AC0_ssubset_ACC0`) and
`AC0Mod p ⊂ ACC0` for every odd prime `p` (`AC0Mod_ssubset_ACC0`).

The second half of the file develops ingredients used in Williams's algorithmic method for `ACC⁰`
[Williams2014]. Williams's separation `NEXP ⊄ ACC⁰` itself is not proved here: the
Yao–Beigel–Tarui compilation of `ACC⁰` circuits into `Sym⁺` circuits, the resulting fast `ACC⁰`
satisfiability algorithm, and the easy-witness argument are not formalized.

* **Depth-two `Sym⁺` (`Sym ∘ AND`) circuits and fast Zeta multipoint evaluation**: a
  `SymPlusCircuit n s` evaluates a symmetric function `sym : ℕ → Bool` on the count of satisfied
  positive conjunction masks `masks : Fin s → BitString n`. Splitting `n = n₁ + n₂` factors each
  mask into left and right sub-masks (`evalMask_append`), expressing
  `activeCount (Fin.append x₁ x₂)` as the Boolean-lattice Zeta transform
  `zetaTransform (C.coeffTable x₂) x₁` of a `2 ^ n₁`-entry coefficient table accumulated from `x₂`
  (`zetaTransform_coeffTable_eq_activeCount`). The recursive divide-and-conquer Fast Zeta Transform
  (`fastZeta`) computes `zetaTransform` (`fastZeta_eq_zetaTransform`), so `fastSymPlusEval` agrees
  with `SymPlusCircuit.eval` on all `2 ^ (n₁ + n₂)` inputs (`fastSymPlusEval_eq_eval`) and
  characterizes satisfiability (`isSatisfiable_iff_exists_fastSymPlusEval`).
* **Lower bounds against `AC0Mod` and `ACC0` in `P`, `Σ₂`, and `NEXP`**:
  - Unconditionally, parity is in `P ⊆ EXP ⊆ NEXP` (`parity_mem_P`, `parity_mem_NEXP`), giving a
    language in `P` (and `NEXP`) outside `AC0` (`exists_mem_NEXP_notMem_AC0`) and outside
    `AC0Mod p` for every odd prime `p` (`exists_mem_NEXP_notMem_AC0Mod`).
  - Unconditionally, for every modulus `q` (prime or composite) and every degree `k`, simulating
    `MOD_q` gates by De Morgan circuits (`SIZEMod_subset_SIZE`) and applying Kannan's theorem gives
    a language in `Σ₂ ⊆ NEXP` with no `MOD_q` circuits of size `O(n ^ k)` of any depth
    (`exists_mem_SigmaP_two_notMem_SIZEMod`, `exists_mem_NEXP_notMem_SIZEMod`).
  - Unconditionally, if `NEXP ⊆ ACC0`, then `NEXP ⊆ PPoly` and the polynomial hierarchy collapses
    to `Σ₂` (`PH_eq_SigmaP_two_of_NEXP_subset_ACC0`), placing Kannan's `Σ₃` language into `Σ₂`
    (`Kannan.language_mem_SigmaP_two_of_NEXP_subset_ACC0`).

## Main definitions

* `Cslib.Circuits.Boolean.ACC0`: the class ACC⁰ = `⋃ q ≥ 2, AC0Mod q`.
* `Cslib.Circuits.Boolean.SIZEMod`: languages decided by `MOD_q` circuits of size at most `s n`.
* `Cslib.Circuits.Boolean.SymPlusCircuit`: depth-two `Sym ∘ AND` circuits.
* `Cslib.Circuits.Boolean.zetaTransform`, `Cslib.Circuits.Boolean.fastZeta`: the Boolean-lattice
  Zeta transform and its divide-and-conquer evaluation.
* `Cslib.Circuits.Boolean.SymPlusCircuit.coeffTable`,
  `Cslib.Circuits.Boolean.SymPlusCircuit.fastSymPlusEval`: split-variable coefficient table and
  fast multipoint evaluation of a `Sym⁺` circuit.

## Main results

* `Cslib.Circuits.Boolean.AC0Mod_zero`, `Cslib.Circuits.Boolean.AC0Mod_one`:
  `AC⁰[0] = AC⁰[1] = AC⁰`.
* `Cslib.Circuits.Boolean.AC0Mod_subset_AC0Mod_of_dvd`: `AC⁰[q] ⊆ AC⁰[q']` when `q ∣ q'` and
  `0 < q'`.
* `Cslib.Circuits.Boolean.ACC0_eq_iUnion_AC0Mod`: `ACC⁰ = ⋃ q, AC⁰[q]`.
* `Cslib.Circuits.Boolean.ACC0.compl`, `Cslib.Circuits.Boolean.ACC0.inf`,
  `Cslib.Circuits.Boolean.ACC0.sup`: Boolean closure of `ACC⁰`.
* `Cslib.Circuits.Boolean.ACC0_subset_TC0`, `Cslib.Circuits.Boolean.ACC0_subset_AC_one`,
  `Cslib.Circuits.Boolean.ACC0_subset_NC_two`, `Cslib.Circuits.Boolean.ACC0_subset_PPoly`.
* `Cslib.Circuits.Boolean.AC0_ssubset_ACC0`, `Cslib.Circuits.Boolean.AC0Mod_ssubset_ACC0`:
  strictness of `AC⁰ ⊂ ACC⁰` and `AC⁰[p] ⊂ ACC⁰` for odd prime `p`.
* `Cslib.Circuits.Boolean.SymPlusCircuit.zetaTransform_coeffTable_eq_activeCount`,
  `Cslib.Circuits.Boolean.fastZeta_eq_zetaTransform`,
  `Cslib.Circuits.Boolean.SymPlusCircuit.fastSymPlusEval_eq_eval`: correctness of Williams's fast
  `Sym⁺` evaluation.
* `Cslib.Circuits.Boolean.exists_mem_SigmaP_two_notMem_SIZEMod`,
  `Cslib.Circuits.Boolean.exists_mem_NEXP_notMem_SIZEMod`: unconditional fixed-degree `MOD_q`
  circuit lower bounds in `Σ₂` and `NEXP` for every modulus `q`.
* `Cslib.Circuits.Boolean.PH_eq_SigmaP_two_of_NEXP_subset_ACC0`: `NEXP ⊆ ACC⁰` collapses `PH` to
  `Σ₂`.

## References

* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
* [A. C.-C. Yao, *On ACC and threshold circuits*][Yao1990]
* [R. Beigel, J. Tarui, *On ACC*][BeigelTarui1994]
* [D. A. M. Barrington, *Bounded-width polynomial-size branching programs recognize exactly those
  languages in NC¹*][Barrington1989]
* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Set Finset BitString Unbounded Cslib.Complexity Turing.MultiTapeTM Filter

/-! ### Degenerate moduli `q = 0, 1` and divisibility monotonicity for `AC0Mod` -/

/-- For `q = 0`, `modGate 0 m` tests whether the Hamming weight is nonzero, which is the
unbounded disjunction `.or m`. -/
theorem modGate_zero (m : ℕ) (x : Fin m → Bool) :
    modGate 0 m x = Unbounded.interpretation (.or m) x := by
  simp [modGate, Nat.mod_zero, card_eq_zero, filter_eq_empty_iff]

/-- For `q = 1`, `modGate 1 m` is the constant `false`. -/
@[simp] theorem modGate_one (m : ℕ) (x : Fin m → Bool) :
    modGate 1 m x = false := by
  simp [modGate, Nat.mod_one]

/-- For `q = 2`, `modGate 2 m` is the `m`-bit parity function `parity m`. -/
theorem modGate_two_eq_parity (m : ℕ) : modGate 2 m = parity m := by
  funext x
  simp only [modGate, parity, parityOn, ne_eq, Nat.mod_two_ne_zero]

/-- A circuit over the `AC⁰` basis simulating an operation of `AC⁰[0]`. -/
def modZeroCircuit : (op : ExtOp) → Circuit Unbounded.signature (extSignature.Arity op) 1
  | .ac op => Circuit.oneGate (σ := Unbounded.signature) op id
  | .gate m => Circuit.oneGate (σ := Unbounded.signature) (.or m) id

theorem computes_modZeroCircuit (op : ExtOp) :
    (modZeroCircuit op).Computes Unbounded.interpretation
      (single (extInterpretation (modGate 0) op)) := by
  intro x
  funext o
  rw [Subsingleton.elim o 0]
  cases op with
  | ac op => rfl
  | gate m =>
    simp only [modZeroCircuit, Circuit.eval_oneGate, id_eq, single, extInterpretation_gate,
      modGate_zero]

/-- **`AC⁰[0] = AC⁰`**: modulo `0`, a `MOD_0` gate is an unbounded `OR` gate. -/
@[simp] theorem AC0Mod_zero : AC0Mod 0 = AC0 := by
  refine (ConstDepth.subset_of_simulation (b := 1) (c := 1) fun op =>
    ⟨modZeroCircuit op, computes_modZeroCircuit op, ?_, ?_⟩).antisymm (AC0_subset_AC0Mod 0)
  · cases op <;> simp [modZeroCircuit]
  · cases op <;> simp [modZeroCircuit]

/-- A circuit over the `AC⁰` basis simulating an operation of `AC⁰[1]`. -/
def modOneCircuit : (op : ExtOp) → Circuit Unbounded.signature (extSignature.Arity op) 1
  | .ac op => Circuit.oneGate (σ := Unbounded.signature) op id
  | .gate _ => constCircuit (Signature.Hom.id _) false

theorem computes_modOneCircuit (op : ExtOp) :
    (modOneCircuit op).Computes Unbounded.interpretation
      (single (extInterpretation (modGate 1) op)) := by
  intro x
  funext o
  rw [Subsingleton.elim o 0]
  cases op with
  | ac op => rfl
  | gate m => simp [modOneCircuit, single]

/-- **`AC⁰[1] = AC⁰`**: modulo `1`, a `MOD_1` gate is the constant `false`. -/
@[simp] theorem AC0Mod_one : AC0Mod 1 = AC0 := by
  refine (ConstDepth.subset_of_simulation (b := 1) (c := 1) fun op =>
    ⟨modOneCircuit op, computes_modOneCircuit op, ?_, ?_⟩).antisymm (AC0_subset_AC0Mod 1)
  · cases op <;> simp [modOneCircuit]
  · cases op with
    | ac op => simp [modOneCircuit]
    | gate m => exact depth_constCircuit_le false

/-- Repeating each of the `m` coordinates of `x` `k` times via `finProdFinEquiv` multiplies the
Hamming weight by `k`. -/
theorem weight_comp_finProdFinEquiv_fst {m k : ℕ} (x : Fin m → Bool) :
    BitString.weight (fun j : Fin (m * k) => x (finProdFinEquiv.symm j).1) =
      BitString.weight x * k := by
  rw [BitString.weight_eq_sum_toNat, BitString.weight_eq_sum_toNat]
  rw [Equiv.sum_comp finProdFinEquiv.symm (fun p : Fin m × Fin k => (x p.1).toNat),
    Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- A `MOD_q` gate on `m` inputs is computed by a single `MOD_{q * k}` gate on `m * k` inputs
when `0 < k`, by repeating each input wire `k` times. -/
theorem modGate_mul_right (q m : ℕ) {k : ℕ} (hk : 0 < k) (x : Fin m → Bool) :
    modGate (q * k) (m * k) (fun j => x (finProdFinEquiv.symm j).1) = modGate q m x := by
  simp only [modGate_eq_modCount, modCount, weight_comp_finProdFinEquiv_fst,
    Nat.mul_mod_mul_right, ne_eq, mul_eq_zero, hk.ne', or_false]

/-- A circuit over the `AC⁰[q * k]` basis simulating a single operation of `AC⁰[q]`. -/
def modMulCircuit (k : ℕ) : (op : ExtOp) → Circuit extSignature (extSignature.Arity op) 1
  | .ac op => Circuit.oneGate (σ := extSignature) (.ac op) id
  | .gate m => Circuit.oneGate (σ := extSignature) (.gate (m * k))
      fun j => (finProdFinEquiv.symm j).1

theorem computes_modMulCircuit (q : ℕ) {k : ℕ} (hk : 0 < k) (op : ExtOp) :
    (modMulCircuit k op).Computes (extInterpretation (modGate (q * k)))
      (single (extInterpretation (modGate q) op)) := by
  intro x
  funext o
  rw [Subsingleton.elim o 0]
  cases op with
  | ac op => rfl
  | gate m =>
    simp only [modMulCircuit, Circuit.eval_oneGate, single, extInterpretation_gate]
    exact modGate_mul_right q m hk x

/-- **`AC⁰[q] ⊆ AC⁰[q * k]`** for every `k > 0`: a `MOD_{q * k}` gate simulates a `MOD_q` gate by
repeating each wire `k` times. -/
theorem AC0Mod_subset_AC0Mod_mul_right (q : ℕ) {k : ℕ} (hk : 0 < k) :
    AC0Mod q ⊆ AC0Mod (q * k) := by
  refine ConstDepth.subset_of_simulation (b := 1) (c := 1) fun op =>
    ⟨modMulCircuit k op, computes_modMulCircuit q hk op, ?_, ?_⟩
  · cases op <;> simp [modMulCircuit]
  · cases op <;> simp [modMulCircuit]

/-- **`AC⁰[q] ⊆ AC⁰[k * q]`** for every `k > 0`. -/
theorem AC0Mod_subset_AC0Mod_mul_left {k : ℕ} (hk : 0 < k) (q : ℕ) :
    AC0Mod q ⊆ AC0Mod (k * q) := by
  rw [mul_comm]
  exact AC0Mod_subset_AC0Mod_mul_right q hk

/-- **Divisibility monotonicity**: if `q ∣ q'` and `0 < q'`, then `AC⁰[q] ⊆ AC⁰[q']`. -/
theorem AC0Mod_subset_AC0Mod_of_dvd {q q' : ℕ} (hq' : 0 < q') (h : q ∣ q') :
    AC0Mod q ⊆ AC0Mod q' := by
  obtain ⟨k, rfl⟩ := h
  have hk : 0 < k := Nat.pos_of_mul_pos_left hq'
  exact AC0Mod_subset_AC0Mod_mul_right q hk

/-! ### Definition of `ACC⁰` and closure properties -/

/-- **ACC⁰**: the class of languages over `Bool` decided at every input length by constant-depth,
polynomial-size circuits over negation, unbounded fan-in conjunction and disjunction, and
unbounded fan-in `MOD_q` gates for some fixed modulus `q ≥ 2` [Barrington1989],
[Vollmer, Chapter 4][Vollmer1999]. -/
def ACC0 : Set (Language Bool) :=
  ⋃ q ≥ 2, AC0Mod q

/-- Membership in `ACC⁰`: a language belongs to `ACC0` iff it belongs to `AC0Mod q` for some
modulus `q ≥ 2`. -/
theorem mem_ACC0_iff {L : Language Bool} :
    L ∈ ACC0 ↔ ∃ q ≥ 2, L ∈ AC0Mod q := by
  simp [ACC0]

/-- **AC⁰ ⊆ ACC⁰**: every `AC⁰` language belongs to `AC⁰[2] ⊆ ACC⁰`. -/
theorem AC0_subset_ACC0 : AC0 ⊆ ACC0 :=
  fun _ hL => mem_ACC0_iff.2 ⟨2, le_rfl, AC0_subset_AC0Mod 2 hL⟩

/-- **AC⁰[q] ⊆ ACC⁰** for every modulus `q : ℕ` (including `q = 0, 1`). -/
theorem AC0Mod_subset_ACC0 (q : ℕ) : AC0Mod q ⊆ ACC0 := by
  rcases q with _ | _ | q
  · rw [AC0Mod_zero]
    exact AC0_subset_ACC0
  · rw [AC0Mod_one]
    exact AC0_subset_ACC0
  · exact fun _ hL => mem_ACC0_iff.2 ⟨q + 2, by omega, hL⟩

/-- **`ACC⁰` is the union of `AC⁰[q]` over all `q : ℕ`.** -/
theorem ACC0_eq_iUnion_AC0Mod : ACC0 = ⋃ q, AC0Mod q := by
  refine Subset.antisymm (iUnion₂_subset fun q _ => subset_iUnion AC0Mod q) ?_
  exact iUnion_subset AC0Mod_subset_ACC0

/-- Membership in `ACC⁰` is equivalent to membership in `AC⁰[q]` for some `q : ℕ`. -/
theorem mem_ACC0_iff_exists_AC0Mod {L : Language Bool} :
    L ∈ ACC0 ↔ ∃ q, L ∈ AC0Mod q := by
  rw [ACC0_eq_iUnion_AC0Mod, Set.mem_iUnion]

/-- The modular counting language `Language.ofSlices (modGate q)` is in `AC⁰[q]`. -/
theorem modGate_mem_AC0Mod (q : ℕ) : Language.ofSlices (modGate q) ∈ AC0Mod q := by
  refine ConstDepth.mem_iff.2 ⟨1, fun _ => 1, by fun_prop, fun n =>
    ⟨Circuit.oneGate (σ := extSignature) (.gate n) id, fun x => ?_,
      (Circuit.depth_oneGate _ _).le, le_rfl⟩⟩
  funext j
  rw [Language.slice_ofSlices]
  rfl

/-- The modular counting language `Language.ofSlices (modGate q)` is in `ACC⁰`. -/
theorem modGate_mem_ACC0 (q : ℕ) : Language.ofSlices (modGate q) ∈ ACC0 :=
  AC0Mod_subset_ACC0 q (modGate_mem_AC0Mod q)

/-- **Parity is in `AC⁰[2]`.** -/
theorem parity_mem_AC0Mod_two : Language.ofSlices parity ∈ AC0Mod 2 := by
  have h : Language.ofSlices parity = Language.ofSlices (modGate 2) := by
    congr 1
    funext n
    exact (modGate_two_eq_parity n).symm
  rw [h]
  exact modGate_mem_AC0Mod 2

/-- **Parity is in `ACC⁰`.** -/
theorem parity_mem_ACC0 : Language.ofSlices parity ∈ ACC0 :=
  AC0Mod_subset_ACC0 2 parity_mem_AC0Mod_two

/-- **`AC⁰` is strictly contained in `AC⁰[2]`.** -/
theorem AC0_ssubset_AC0Mod_two : AC0 ⊂ AC0Mod 2 :=
  (Set.ssubset_iff_of_subset (AC0_subset_AC0Mod 2)).2
    ⟨_, parity_mem_AC0Mod_two, parity_notMem_AC0⟩

/-- **`AC⁰` is strictly contained in `ACC⁰`.** -/
theorem AC0_ssubset_ACC0 : AC0 ⊂ ACC0 :=
  (Set.ssubset_iff_of_subset AC0_subset_ACC0).2
    ⟨_, parity_mem_ACC0, parity_notMem_AC0⟩

/-- **`AC⁰[p]` is strictly contained in `ACC⁰`** for every odd prime `p`, witnessed by parity
[Razborov1987], [Smolensky1987]. -/
theorem AC0Mod_ssubset_ACC0 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : AC0Mod p ⊂ ACC0 :=
  (Set.ssubset_iff_of_subset (AC0Mod_subset_ACC0 p)).2
    ⟨_, parity_mem_ACC0, Smolensky.parity_notMem_AC0Mod hp2⟩

namespace AC0Mod

variable {q : ℕ} {L M : Language Bool}

/-- The empty language is in `AC⁰[q]`. -/
theorem bot_mem (q : ℕ) : (⊥ : Language Bool) ∈ AC0Mod q :=
  ConstDepth.bot_mem Unbounded.toExt

/-- The full language is in `AC⁰[q]`. -/
theorem top_mem (q : ℕ) : (⊤ : Language Bool) ∈ AC0Mod q :=
  ConstDepth.top_mem Unbounded.toExt

/-- `AC⁰[q]` is closed under complement. -/
theorem compl (hL : L ∈ AC0Mod q) : Lᶜ ∈ AC0Mod q :=
  ConstDepth.compl Unbounded.toExt hL

/-- `AC⁰[q]` is closed under intersection. -/
theorem inf (hL : L ∈ AC0Mod q) (hM : M ∈ AC0Mod q) : L ⊓ M ∈ AC0Mod q :=
  ConstDepth.inf Unbounded.toExt hL hM

/-- `AC⁰[q]` is closed under union. -/
theorem sup (hL : L ∈ AC0Mod q) (hM : M ∈ AC0Mod q) : L ⊔ M ∈ AC0Mod q :=
  ConstDepth.sup Unbounded.toExt hL hM

end AC0Mod

namespace ACC0

variable {L M : Language Bool}

/-- The empty language is in `ACC⁰`. -/
theorem bot_mem : (⊥ : Language Bool) ∈ ACC0 :=
  AC0_subset_ACC0 (ConstDepth.bot_mem (Signature.Hom.id _))

/-- The full language is in `ACC⁰`. -/
theorem top_mem : (⊤ : Language Bool) ∈ ACC0 :=
  AC0_subset_ACC0 (ConstDepth.top_mem (Signature.Hom.id _))

/-- **`ACC⁰` is closed under complement.** -/
theorem compl (hL : L ∈ ACC0) : Lᶜ ∈ ACC0 := by
  obtain ⟨q, hq, hLq⟩ := mem_ACC0_iff.1 hL
  exact mem_ACC0_iff.2 ⟨q, hq, AC0Mod.compl hLq⟩

/-- **`ACC⁰` is closed under intersection**: circuits with moduli `q₁` and `q₂` embed into
`AC⁰[q₁ * q₂]`. -/
theorem inf (hL : L ∈ ACC0) (hM : M ∈ ACC0) : L ⊓ M ∈ ACC0 := by
  obtain ⟨q₁, hq₁, hL₁⟩ := mem_ACC0_iff.1 hL
  obtain ⟨q₂, hq₂, hM₂⟩ := mem_ACC0_iff.1 hM
  refine mem_ACC0_iff.2 ⟨q₁ * q₂, by nlinarith, ?_⟩
  exact AC0Mod.inf
    (AC0Mod_subset_AC0Mod_mul_right q₁ (by omega) hL₁)
    (AC0Mod_subset_AC0Mod_mul_left (by omega) q₂ hM₂)

/-- **`ACC⁰` is closed under union**: circuits with moduli `q₁` and `q₂` embed into
`AC⁰[q₁ * q₂]`. -/
theorem sup (hL : L ∈ ACC0) (hM : M ∈ ACC0) : L ⊔ M ∈ ACC0 := by
  obtain ⟨q₁, hq₁, hL₁⟩ := mem_ACC0_iff.1 hL
  obtain ⟨q₂, hq₂, hM₂⟩ := mem_ACC0_iff.1 hM
  refine mem_ACC0_iff.2 ⟨q₁ * q₂, by nlinarith, ?_⟩
  exact AC0Mod.sup
    (AC0Mod_subset_AC0Mod_mul_right q₁ (by omega) hL₁)
    (AC0Mod_subset_AC0Mod_mul_left (by omega) q₂ hM₂)

end ACC0

/-! ### Inclusions `ACC⁰ ⊆ TC⁰`, `ACC⁰ ⊆ AC¹ ⊆ NC²`, and `ACC⁰ ⊆ P/poly` -/

/-- **`ACC⁰ ⊆ TC⁰`** [Vollmer, Chapter 4][Vollmer1999]: every `AC⁰[q]` is contained in `TC⁰`. -/
theorem ACC0_subset_TC0 : ACC0 ⊆ TC0 :=
  iUnion₂_subset fun q _ => AC0Mod_subset_TC0 q

/-- Quadratic upper bound on the size of `majorityDeMorganCircuit k`. -/
theorem size_majorityDeMorganCircuit_le_sq (k : ℕ) :
    (majorityDeMorganCircuit k).size ≤ 65 * (k + 1) ^ 2 := by
  have h := size_majorityDeMorganCircuit_le k
  have hclog : Nat.clog 2 (k + 1) ≤ k + 1 :=
    (Nat.clog_le_iff_le_pow one_lt_two).2 Nat.lt_two_pow_self.le
  nlinarith

namespace Unbounded

/-- A circuit over the unbounded fan-in basis simulating each operation of the `MOD_q` multiplicity
basis, using `majorityDeMorganCircuit` mapped into `Unbounded.signature` inside
`modCircuitOfMajority`. -/
def modMultUnboundedCircuit (q : ℕ) :
    (op : MultOp) → Circuit Unbounded.signature (multSignature.Arity op) 1
  | .ac op => Circuit.oneGate (σ := Unbounded.signature) op id
  | .gate _ mult =>
    let K := ∑ i, modMult q (mult i)
    (modCircuitOfMajority (Signature.Hom.id _) q
      ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded)).comp
      (Circuit.wiring Unbounded.signature (expandIndex fun i => modMult q (mult i)))

/-- `modMultUnboundedCircuit q op` computes `op` under `Unbounded.interpretation`. -/
theorem computes_modMultUnboundedCircuit (q : ℕ) (op : MultOp) :
    (modMultUnboundedCircuit q op).Computes Unbounded.interpretation
      (single (multInterpretation (modCount q) op)) := by
  cases op with
  | ac op =>
    intro x
    funext o
    rw [Subsingleton.elim o 0]
    rfl
  | gate N mult =>
    intro x
    set K := ∑ i, modMult q (mult i)
    have hM : ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded).Computes
        Unbounded.interpretation (single (majority (K + (K + 2)))) :=
      (computes_majorityDeMorganCircuit (K + (K + 2))).mapOp
    rw [modMultUnboundedCircuit, Circuit.eval_comp, Circuit.eval_wiring,
      computes_modCircuitOfMajority hM q]
    funext o
    simp only [single, multInterpretation_gate, modGate_eq_modCount, modCount]
    rw [weight_comp_expandIndex, decide_eq_decide]
    exact multWeight_modMult_mod_ne_zero_iff q mult x

/-- Polynomial size bound for `modMultUnboundedCircuit q op`. -/
theorem size_modMultUnboundedCircuit_le (q : ℕ) (op : MultOp) :
    (modMultUnboundedCircuit q op).size ≤
      2100 * (max q 1 * multSignature.Arity op + 1) ^ 3 := by
  cases op with
  | ac op =>
    simp only [modMultUnboundedCircuit, Circuit.size_oneGate]
    have : 1 ≤ (max q 1 * multSignature.Arity (.ac op) + 1) ^ 3 :=
      Nat.one_le_pow _ _ (by omega)
    linarith
  | gate N mult =>
    rw [modMultUnboundedCircuit, Circuit.size_comp, Circuit.size_wiring, zero_add]
    set K := ∑ i : Fin N, modMult q (mult i)
    have hK : K ≤ max q 1 * N := by
      simpa [K, mul_comm] using Finset.sum_le_card_nsmul (univ : Finset (Fin N))
        (fun i => modMult q (mult i)) (max q 1) fun i _ => modMult_le q _
    have hM : (((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded).size) ≤
        65 * (2 * K + 3) ^ 2 := by
      rw [Circuit.size_mapOp, show 2 * K + 3 = K + (K + 2) + 1 by omega]
      exact size_majorityDeMorganCircuit_le_sq (K + (K + 2))
    change (modCircuitOfMajority (Signature.Hom.id _) q
      ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded)).size ≤
      2100 * (max q 1 * N + 1) ^ 3
    have hcube : (K + 1) ^ 3 ≤ (max q 1 * N + 1) ^ 3 :=
      Nat.pow_le_pow_left (Nat.add_le_add_right hK 1) 3
    calc (modCircuitOfMajority (Signature.Hom.id _) q
          ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded)).size
        ≤ 1 + (K + 1) * (2 * (2 +
            ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded).size) + 2) :=
          size_modCircuitOfMajority_le q
      _ ≤ 1 + (K + 1) * (2 * (2 + 65 * (2 * K + 3) ^ 2) + 2) := by gcongr
      _ ≤ 2100 * (K + 1) ^ 3 := by
        have hring : 2100 * (K + 1) ^ 3 =
            1 + (K + 1) * (2 * (2 + 65 * (2 * K + 3) ^ 2) + 2) +
              (1580 * K ^ 3 + 4220 * K ^ 2 + 3564 * K + 923) := by ring
        omega
      _ ≤ 2100 * (max q 1 * N + 1) ^ 3 := Nat.mul_le_mul_left 2100 hcube

/-- Logarithmic depth bound for `modMultUnboundedCircuit q op`. -/
theorem depth_modMultUnboundedCircuit_le (q : ℕ) (op : MultOp) :
    (modMultUnboundedCircuit q op).depth ≤
      6 + 23 * Nat.clog 2 (2 * max q 1 * multSignature.Arity op + 3) := by
  cases op with
  | ac op =>
    simp only [modMultUnboundedCircuit, Circuit.depth_oneGate]
    omega
  | gate N mult =>
    refine (Circuit.depth_comp_le _ _).trans ?_
    rw [Circuit.depth_wiring, add_zero]
    set K := ∑ i : Fin N, modMult q (mult i)
    have hK : K ≤ max q 1 * N := by
      simpa [K, mul_comm] using Finset.sum_le_card_nsmul (univ : Finset (Fin N))
        (fun i => modMult q (mult i)) (max q 1) fun i _ => modMult_le q _
    have h2K : 2 * K ≤ 2 * max q 1 * N := by linarith
    have hM : (((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded).depth) ≤
        2 + 23 * Nat.clog 2 (2 * max q 1 * N + 3) := by
      rw [Circuit.depth_mapOp]
      refine (depth_majorityDeMorganCircuit_le (K + (K + 2))).trans ?_
      have hclog : Nat.clog 2 (K + (K + 2) + 1) ≤ Nat.clog 2 (2 * max q 1 * N + 3) :=
        Nat.clog_mono_right 2 (by omega)
      omega
    have hd := depth_modCircuitOfMajority_le (φ := Signature.Hom.id _)
      (M := (majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded) q
    change (modCircuitOfMajority (Signature.Hom.id _) q
      ((majorityDeMorganCircuit (K + (K + 2))).mapOp deMorganToUnbounded)).depth ≤
      6 + 23 * Nat.clog 2 (2 * max q 1 * N + 3)
    omega

/-- **Unbounded fan-in circuits simulate `MOD_q` gates in logarithmic depth**: a circuit with
`MOD_q` gates of `n` inputs, `s` gates and depth `d` has an equivalent circuit over the unbounded
fan-in basis of at most `2100 * s * (max q 1 * (n + s) + 1) ^ 3` gates and depth at most
`(6 + 23 * ⌈log₂ (2 * max q 1 * (n + s) + 3)⌉) * d`. -/
theorem exists_unbounded_simulation_modGate {n m : ℕ} (q : ℕ) (C : Circuit extSignature n m) :
    ∃ D : Circuit Unbounded.signature n m,
      D.eval Unbounded.interpretation = C.eval (extInterpretation (modGate q)) ∧
      D.size ≤ C.size * (2100 * (max q 1 * (n + C.size) + 1) ^ 3) ∧
      D.depth ≤ (6 + 23 * Nat.clog 2 (2 * max q 1 * (n + C.size) + 3)) * C.depth := by
  refine ⟨(multCircuit C).simulate (modMultUnboundedCircuit q), ?_, ?_, ?_⟩
  · rw [Circuit.eval_simulate _ _ (computes_modMultUnboundedCircuit q),
      eval_multCircuit (G := modCount q) (modGate_eq_modCount q)]
  · rw [Circuit.size_simulate, Program.cost_eq_sum]
    refine (Finset.sum_le_sum (g := fun _ => 2100 * (max q 1 * (n + C.size) + 1) ^ 3)
      fun k _ => (size_modMultUnboundedCircuit_le q _).trans ?_).trans_eq
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, size_multCircuit])
    have har := arity_lines_multCircuit_le C k
    gcongr
  · refine (Circuit.depth_simulate_le _ _).trans
      (((multCircuit C).depthWith_le_mul_depth fun k =>
        (depth_modMultUnboundedCircuit_le q _).trans ?_).trans
        (Nat.mul_le_mul_left _ (depth_multCircuit_le C)))
    have har := arity_lines_multCircuit_le C k
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_left 23
        (Nat.clog_mono_right 2 (Nat.add_le_add_right (Nat.mul_le_mul_left (2 * max q 1) har) 3))) 6

/-- **De Morgan circuits simulate `MOD_q` circuits in polynomial size**: every circuit over the
`AC⁰[q]` basis of `n` inputs and `s` gates has an equivalent fan-in-two De Morgan circuit of size
at most `(2100 * (max q 1) ^ 3) ^ 2 * (n + s + 1) ^ 8`. -/
theorem exists_deMorgan_simulation_modGate {n m : ℕ} (q : ℕ) (C : Circuit extSignature n m) :
    ∃ D : Circuit Boolean.signature n m,
      D.eval Boolean.interpretation = C.eval (extInterpretation (modGate q)) ∧
      D.size ≤ (2100 * (max q 1) ^ 3) ^ 2 * (n + C.size + 1) ^ 8 := by
  obtain ⟨U, hUe, hUs, -⟩ := exists_unbounded_simulation_modGate q C
  obtain ⟨D, hDe, hDs, -⟩ := exists_deMorgan_simulation U
  refine ⟨D, hDe.trans hUe, hDs.trans ?_⟩
  have hQ : 1 ≤ max q 1 := le_max_right q 1
  have hK : max q 1 * (n + C.size) + 1 ≤ max q 1 * (n + C.size + 1) := by nlinarith
  have hU1 : U.size ≤ 2100 * (max q 1) ^ 3 * (n + C.size + 1) ^ 4 := by
    have h1 : C.size ≤ n + C.size + 1 := by omega
    have h2 : (max q 1 * (n + C.size) + 1) ^ 3 ≤ (max q 1) ^ 3 * (n + C.size + 1) ^ 3 := by
      calc (max q 1 * (n + C.size) + 1) ^ 3
          ≤ (max q 1 * (n + C.size + 1)) ^ 3 := Nat.pow_le_pow_left hK 3
        _ = (max q 1) ^ 3 * (n + C.size + 1) ^ 3 := by ring
    calc U.size ≤ C.size * (2100 * (max q 1 * (n + C.size) + 1) ^ 3) := hUs
      _ ≤ (n + C.size + 1) * (2100 * ((max q 1) ^ 3 * (n + C.size + 1) ^ 3)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul_left 2100 h2)
      _ = 2100 * (max q 1) ^ 3 * (n + C.size + 1) ^ 4 := by ring
  have hnU : n + U.size ≤ 2100 * (max q 1) ^ 3 * (n + C.size + 1) ^ 4 := by
    have hQ3 : 1 ≤ (max q 1) ^ 3 := Nat.one_le_pow 3 _ hQ
    have hpow4 : n + 1 ≤ (n + C.size + 1) ^ 4 := by
      calc n + 1 ≤ (n + C.size + 1) ^ 1 := by simp
        _ ≤ (n + C.size + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : C.size * (2100 * (max q 1 * (n + C.size) + 1) ^ 3) ≤
        2100 * (max q 1) ^ 3 * C.size * (n + C.size + 1) ^ 3 := by
      have h2 : (max q 1 * (n + C.size) + 1) ^ 3 ≤ (max q 1) ^ 3 * (n + C.size + 1) ^ 3 := by
        calc (max q 1 * (n + C.size) + 1) ^ 3
            ≤ (max q 1 * (n + C.size + 1)) ^ 3 := Nat.pow_le_pow_left hK 3
          _ = (max q 1) ^ 3 * (n + C.size + 1) ^ 3 := by ring
      calc C.size * (2100 * (max q 1 * (n + C.size) + 1) ^ 3)
          ≤ C.size * (2100 * ((max q 1) ^ 3 * (n + C.size + 1) ^ 3)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2100 h2)
        _ = 2100 * (max q 1) ^ 3 * C.size * (n + C.size + 1) ^ 3 := by ring
    have h3 : (n + 1) + C.size * (n + C.size + 1) ^ 3 ≤ (n + C.size + 1) ^ 4 := by
      have : (n + 1) * 1 + C.size * (n + C.size + 1) ^ 3 ≤
          (n + 1) * (n + C.size + 1) ^ 3 + C.size * (n + C.size + 1) ^ 3 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left (n + 1) (Nat.one_le_pow 3 _ (by omega))) _
      calc (n + 1) + C.size * (n + C.size + 1) ^ 3
          ≤ (n + 1) * (n + C.size + 1) ^ 3 + C.size * (n + C.size + 1) ^ 3 := by simpa using this
        _ = (n + C.size + 1) ^ 4 := by ring
    nlinarith
  calc U.size * (n + U.size)
      ≤ (2100 * (max q 1) ^ 3 * (n + C.size + 1) ^ 4) *
          (2100 * (max q 1) ^ 3 * (n + C.size + 1) ^ 4) := Nat.mul_le_mul hU1 hnU
    _ = (2100 * (max q 1) ^ 3) ^ 2 * (n + C.size + 1) ^ 8 := by ring

end Unbounded

/-- **`ACⁱ[q] ⊆ ACⁱ⁺¹`**: polynomial-size circuits with `MOD_q` gates of depth `O((log n) ^ i)` are
simulated by polynomial-size circuits over the unbounded fan-in basis of depth
`O((log n) ^ (i + 1))`. -/
theorem ACMod_subset_AC_succ (q i : ℕ) : ACMod q i ⊆ AC (i + 1) := by
  rintro L ⟨c, s, hs, hC⟩
  obtain ⟨e, he⟩ := PolynomiallyBounded.exists_clog_le_mul_log
    (s := fun n => 2 * max q 1 * (n + s n) + 3) (by fun_prop)
  refine ⟨(23 * e + 6) * c, fun n => s n * (2100 * (max q 1 * (n + s n) + 1) ^ 3),
    by fun_prop, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  obtain ⟨D, hDe, hDs, hDd⟩ := Unbounded.exists_unbounded_simulation_modGate q C
  refine ⟨D, fun x => (congrFun hDe x).trans (hCc x), ?_, ?_⟩
  · have hmono := Nat.add_le_add_right
      (Nat.mul_le_mul_left (2 * max q 1) (Nat.add_le_add_left hCs n)) 3
    have hclog : Nat.clog 2 (2 * max q 1 * (n + C.size) + 3) ≤ e * (Nat.log 2 n + 1) :=
      (Nat.clog_mono_right 2 hmono).trans (he n)
    have hlog : 6 + 23 * Nat.clog 2 (2 * max q 1 * (n + C.size) + 3) ≤
        (23 * e + 6) * (Nat.log 2 n + 1) := by nlinarith
    calc D.depth ≤ (6 + 23 * Nat.clog 2 (2 * max q 1 * (n + C.size) + 3)) * C.depth := hDd
      _ ≤ ((23 * e + 6) * (Nat.log 2 n + 1)) * (c * (Nat.log 2 n + 1) ^ i) :=
        Nat.mul_le_mul hlog hCd
      _ = (23 * e + 6) * c * (Nat.log 2 n + 1) ^ (i + 1) := by ring
  · refine hDs.trans ?_
    beta_reduce
    gcongr

/-- **`AC⁰[q] ⊆ AC¹`.** -/
theorem AC0Mod_subset_AC_one (q : ℕ) : AC0Mod q ⊆ AC 1 := by
  rw [← ACMod_zero]
  exact ACMod_subset_AC_succ q 0

/-- **`ACC⁰ ⊆ AC¹`.** -/
theorem ACC0_subset_AC_one : ACC0 ⊆ AC 1 :=
  iUnion₂_subset fun q _ => AC0Mod_subset_AC_one q

/-- **`AC⁰[q] ⊆ NC²`.** -/
theorem AC0Mod_subset_NC_two (q : ℕ) : AC0Mod q ⊆ NC 2 :=
  (AC0Mod_subset_AC_one q).trans (AC_subset_NC_succ 1)

/-- **`ACC⁰ ⊆ NC²`.** -/
theorem ACC0_subset_NC_two : ACC0 ⊆ NC 2 :=
  ACC0_subset_AC_one.trans (AC_subset_NC_succ 1)

/-- **`NCⁱ ⊆ P/poly`** for every `i`: a language decided by polynomial-size De Morgan circuits of
polylogarithmic depth has polynomially bounded circuit complexity. -/
theorem NC_subset_PPoly (i : ℕ) : NC i ⊆ PPoly := by
  rintro L ⟨c, s, hs, hC⟩
  refine hs.mono_of_le fun n => ?_
  obtain ⟨C, hCc, -, hCs⟩ := hC n
  exact (complexity_le_of_computes C hCc).trans hCs

/-- **`ACⁱ ⊆ P/poly`** for every `i`. -/
theorem AC_subset_PPoly (i : ℕ) : AC i ⊆ PPoly :=
  (AC_subset_NC_succ i).trans (NC_subset_PPoly (i + 1))

/-- **`AC⁰[q] ⊆ P/poly`** for every modulus `q`. -/
theorem AC0Mod_subset_PPoly (q : ℕ) : AC0Mod q ⊆ PPoly :=
  (AC0Mod_subset_AC_one q).trans (AC_subset_PPoly 1)

/-- **`ACC⁰ ⊆ P/poly`.** -/
theorem ACC0_subset_PPoly : ACC0 ⊆ PPoly :=
  ACC0_subset_AC_one.trans (AC_subset_PPoly 1)

/-- **Some language over `Bool` is not in `ACC⁰`** (by Shannon's counting argument and
`ACC0 ⊆ PPoly`). -/
theorem exists_notMem_ACC0 : ∃ L : Language Bool, L ∉ ACC0 := by
  obtain ⟨L, hL⟩ := PPoly.exists_not_mem
  exact ⟨L, fun h => hL (ACC0_subset_PPoly h)⟩

/-! ### Williams's `Sym⁺` (`Sym ∘ AND`) circuits and fast Zeta multipoint evaluation -/

/-- Whether the positive conjunction with mask `p` is satisfied by `x`: every coordinate where `p`
is `true` is also `true` in `x`. -/
def evalMask {n : ℕ} (p x : BitString n) : Bool :=
  decide (∀ i : Fin n, p i = true → x i = true)

theorem evalMask_eq_true_iff {n : ℕ} {p x : BitString n} :
    evalMask p x = true ↔ ∀ i : Fin n, p i = true → x i = true :=
  decide_eq_true_iff

@[simp] theorem evalMask_false {n : ℕ} (x : BitString n) :
    evalMask (fun _ => false) x = true := by
  simp [evalMask]

@[simp] theorem evalMask_self {n : ℕ} (x : BitString n) :
    evalMask x x = true := by
  simp [evalMask]

/-- On `Fin.cons b q`, a mask `Fin.cons false q` ignores the first bit `x 0` and tests `q` on
`Fin.tail x`. -/
theorem evalMask_cons_false {m : ℕ} (q : BitString m) (x : BitString (m + 1)) :
    evalMask (Fin.cons false q) x = evalMask q (Fin.tail x) := by
  rw [Bool.eq_iff_iff, evalMask_eq_true_iff, evalMask_eq_true_iff, Fin.forall_fin_succ]
  simp [Fin.tail]

/-- On `Fin.cons true q`, a mask `Fin.cons true q` tests both `x 0 = true` and `q` on
`Fin.tail x`. -/
theorem evalMask_cons_true {m : ℕ} (q : BitString m) (x : BitString (m + 1)) :
    evalMask (Fin.cons true q) x = (x 0 && evalMask q (Fin.tail x)) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, evalMask_eq_true_iff, evalMask_eq_true_iff,
    Fin.forall_fin_succ]
  simp [Fin.tail]

/-- On `Fin.append x₁ x₂`, a mask `p : BitString (n₁ + n₂)` factors into its left `n₁` coordinates
on `x₁` and its right `n₂` coordinates on `x₂`. -/
theorem evalMask_append {n₁ n₂ : ℕ} (p : BitString (n₁ + n₂))
    (x₁ : BitString n₁) (x₂ : BitString n₂) :
    evalMask p (Fin.append x₁ x₂) =
      (evalMask (fun i => p (Fin.castAdd n₂ i)) x₁ &&
        evalMask (fun i => p (Fin.natAdd n₁ i)) x₂) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, evalMask_eq_true_iff, evalMask_eq_true_iff,
    evalMask_eq_true_iff]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · simpa [Fin.append_left] using h (Fin.castAdd n₂ i) hi
    · simpa [Fin.append_right] using h (Fin.natAdd n₁ i) hi
  · rintro ⟨h₁, h₂⟩ k
    refine Fin.addCases (fun i hi => ?_) (fun i hi => ?_) k
    · simpa [Fin.append_left] using h₁ i hi
    · simpa [Fin.append_right] using h₂ i hi

/-- **The Boolean-lattice Zeta transform** (subset-sum transform): sums `f p` over all submasks
`p ≤ x` (`evalMask p x = true`). -/
def zetaTransform {m : ℕ} (f : BitString m → ℕ) (x : BitString m) : ℕ :=
  ∑ p : BitString m, if evalMask p x then f p else 0

/-- **Divide-and-conquer Fast Zeta Transform** (Yates's algorithm / sum-over-subsets recurrence)
[Williams, Section 3.2][Williams2014]: recursively computes the Zeta transform on the two
`(m - 1)`-dimensional subcubes `p 0 = false` and `p 0 = true` and combines them with a single
addition when `x 0 = true`. -/
def fastZeta : {m : ℕ} → (BitString m → ℕ) → BitString m → ℕ
  | 0, f, x => f x
  | _ + 1, f, x =>
    let z₀ := fastZeta (fun q => f (Fin.cons false q)) (Fin.tail x)
    let z₁ := fastZeta (fun q => f (Fin.cons true q)) (Fin.tail x)
    if x 0 then z₀ + z₁ else z₀

/-- **Correctness of the Fast Zeta Transform**: `fastZeta` computes `zetaTransform` at every point
of the Boolean hypercube. -/
theorem fastZeta_eq_zetaTransform {m : ℕ} (f : BitString m → ℕ) (x : BitString m) :
    fastZeta f x = zetaTransform f x := by
  induction m with
  | zero =>
    simp only [fastZeta, zetaTransform]
    rw [Fintype.sum_eq_single x fun p hp => absurd (Subsingleton.elim p x) hp]
    simp
  | succ m ih =>
    simp only [fastZeta, ih, zetaTransform]
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Bool).sum_comp, Fintype.sum_prod_type,
      Fintype.sum_bool]
    simp only [Fin.consEquiv_apply, evalMask_cons_false, evalMask_cons_true]
    cases x 0
    · simp
    · simp [add_comm]

/-- **A depth-two `Sym⁺` (`Sym ∘ AND`) circuit** on `n` Boolean inputs with `s` positive
conjunction gates [Yao1990], [BeigelTarui1994], [Williams2014]: consists of `s` conjunction masks
`masks : Fin s → BitString n` and a symmetric output function `sym : ℕ → Bool` applied to the
number of satisfied conjunctions. -/
structure SymPlusCircuit (n s : ℕ) where
  /-- The `s` positive conjunction masks. -/
  masks : Fin s → BitString n
  /-- The symmetric output gate on the count of satisfied masks in `{0, …, s}`. -/
  sym : ℕ → Bool

namespace SymPlusCircuit

variable {n n₁ n₂ s : ℕ}

/-- The number of conjunction gates of `C` satisfied by `x`. -/
def activeCount (C : SymPlusCircuit n s) (x : BitString n) : ℕ :=
  ∑ j : Fin s, if evalMask (C.masks j) x then 1 else 0

theorem activeCount_eq_card_filter (C : SymPlusCircuit n s) (x : BitString n) :
    C.activeCount x = #(univ.filter fun j : Fin s => evalMask (C.masks j) x = true) := by
  rw [activeCount, Finset.card_filter]

theorem activeCount_le (C : SymPlusCircuit n s) (x : BitString n) :
    C.activeCount x ≤ s := by
  rw [activeCount_eq_card_filter]
  exact (card_filter_le _ _).trans_eq (by simp)

/-- Evaluation of a `Sym⁺` circuit on input `x : BitString n`. -/
def eval (C : SymPlusCircuit n s) (x : BitString n) : Bool :=
  C.sym (C.activeCount x)

/-- `C` computes the Boolean function `f : BitString n → Bool`. -/
def Computes (C : SymPlusCircuit n s) (f : BitString n → Bool) : Prop :=
  ∀ x : BitString n, C.eval x = f x

/-- Whether `C` is satisfiable on `{0, 1} ^ n`. -/
def IsSatisfiable (C : SymPlusCircuit n s) : Prop :=
  ∃ x : BitString n, C.eval x = true

/-- Negating a `Sym⁺` circuit by negating its outer symmetric lookup table. -/
def not (C : SymPlusCircuit n s) : SymPlusCircuit n s where
  masks := C.masks
  sym := fun w => !C.sym w

@[simp] theorem eval_not (C : SymPlusCircuit n s) (x : BitString n) :
    C.not.eval x = !C.eval x :=
  rfl

/-- A constant `b : Bool` as a `Sym⁺` circuit with `0` conjunctions. -/
def ofConst (n : ℕ) (b : Bool) : SymPlusCircuit n 0 where
  masks := Fin.elim0
  sym := fun _ => b

@[simp] theorem eval_ofConst (n : ℕ) (b : Bool) (x : BitString n) :
    (ofConst n b).eval x = b :=
  rfl

/-- An `n`-ary conjunction `.and n` as a `Sym⁺` circuit with `1` mask. -/
def ofAnd (n : ℕ) : SymPlusCircuit n 1 where
  masks := fun _ _ => true
  sym := fun w => decide (w = 1)

@[simp] theorem eval_ofAnd (n : ℕ) (x : BitString n) :
    (ofAnd n).eval x = Unbounded.interpretation (.and n) x := by
  simp [ofAnd, eval, activeCount, evalMask]

/-- The `j`-th singleton mask, reading only input coordinate `j`. -/
def singleMask (n : ℕ) (j : Fin n) : BitString n :=
  fun i => decide (i = j)

@[simp] theorem evalMask_singleMask (n : ℕ) (j : Fin n) (x : BitString n) :
    evalMask (singleMask n j) x = x j := by
  rw [Bool.eq_iff_iff, evalMask_eq_true_iff]
  simp [singleMask]

theorem activeCount_singleMask {sym : ℕ → Bool} (x : BitString n) :
    activeCount ⟨singleMask n, sym⟩ x = BitString.weight x := by
  rw [activeCount_eq_card_filter]
  simp only [evalMask_singleMask]
  rfl

/-- Any symmetric gate `g : ℕ → Bool` of the Hamming weight on `n` bits is computed by a `Sym⁺`
circuit with `n` singleton masks. -/
def ofSymmetric (n : ℕ) (g : ℕ → Bool) : SymPlusCircuit n n where
  masks := singleMask n
  sym := g

@[simp] theorem eval_ofSymmetric (n : ℕ) (g : ℕ → Bool) (x : BitString n) :
    (ofSymmetric n g).eval x = g (BitString.weight x) := by
  simp [ofSymmetric, eval, activeCount_singleMask]

/-- `modGate q n` as a `Sym⁺` circuit of size `n`. -/
def ofModGate (q n : ℕ) : SymPlusCircuit n n :=
  ofSymmetric n fun w => decide (w % q ≠ 0)

@[simp] theorem eval_ofModGate (q n : ℕ) (x : BitString n) :
    (ofModGate q n).eval x = modGate q n x := by
  rw [ofModGate, eval_ofSymmetric, modGate_eq_modCount, modCount]

/-- Unbounded disjunction `.or n` as a `Sym⁺` circuit of size `n`. -/
def ofOr (n : ℕ) : SymPlusCircuit n n :=
  ofSymmetric n fun w => decide (w ≠ 0)

@[simp] theorem eval_ofOr (n : ℕ) (x : BitString n) :
    (ofOr n).eval x = Unbounded.interpretation (.or n) x := by
  rw [ofOr, eval_ofSymmetric, ← modGate_zero, modGate_eq_modCount, modCount, Nat.mod_zero]

/-- Input projection `fun x => x i` as a `Sym⁺` circuit with `1` singleton mask. -/
def ofProj (n : ℕ) (i : Fin n) : SymPlusCircuit n 1 where
  masks := fun _ => singleMask n i
  sym := fun w => decide (w = 1)

@[simp] theorem eval_ofProj (n : ℕ) (i : Fin n) (x : BitString n) :
    (ofProj n i).eval x = x i := by
  simp [ofProj, eval, activeCount]

/-- Push a conjunction mask `p : BitString m` forward along a wire map `w : Fin m → Fin n`:
coordinate `i : Fin n` is required to be `true` iff some wire `j : Fin m` with `p j = true`
reads input `w j = i`. -/
def pullMask {m n : ℕ} (w : Fin m → Fin n) (p : BitString m) : BitString n :=
  fun i => decide (∃ j : Fin m, p j = true ∧ w j = i)

@[simp] theorem evalMask_pullMask {m n : ℕ} (w : Fin m → Fin n) (p : BitString m)
    (x : BitString n) :
    evalMask (pullMask w p) x = evalMask p (x ∘ w) := by
  rw [Bool.eq_iff_iff, evalMask_eq_true_iff, evalMask_eq_true_iff]
  simp only [pullMask, decide_eq_true_eq, Function.comp_apply, forall_exists_index, and_imp]
  exact ⟨fun h j hj => h (w j) j hj rfl, fun h i j hj hij => hij ▸ h j hj⟩

/-- Precompose a `Sym⁺` circuit `C : SymPlusCircuit m s` with an input wiring `w : Fin m → Fin n`
without increasing the number of conjunction gates `s`. -/
def comap {m n s : ℕ} (C : SymPlusCircuit m s) (w : Fin m → Fin n) : SymPlusCircuit n s where
  masks := fun j => pullMask w (C.masks j)
  sym := C.sym

@[simp] theorem activeCount_comap {m n s : ℕ} (C : SymPlusCircuit m s) (w : Fin m → Fin n)
    (x : BitString n) :
    (C.comap w).activeCount x = C.activeCount (x ∘ w) := by
  simp [comap, activeCount]

@[simp] theorem eval_comap {m n s : ℕ} (C : SymPlusCircuit m s) (w : Fin m → Fin n)
    (x : BitString n) :
    (C.comap w).eval x = C.eval (x ∘ w) := by
  rw [eval, activeCount_comap, eval]
  rfl

/-- Size of the `Sym⁺` circuit representing a single `AC⁰[q]` operation `op`. -/
def extOpSize : ExtOp → ℕ
  | .ac .not => 1
  | .ac (.and _) => 1
  | .ac (.or m) => m
  | .gate m => m

/-- Every single gate `op : ExtOp` of the `AC⁰[q]` basis is computed by a `Sym⁺` circuit of size
`extOpSize op`. -/
def ofExtOp (q : ℕ) : (op : ExtOp) → SymPlusCircuit (extSignature.Arity op) (extOpSize op)
  | .ac .not => (ofAnd 1).not
  | .ac (.and m) => ofAnd m
  | .ac (.or m) => ofOr m
  | .gate m => ofModGate q m

@[simp] theorem eval_ofExtOp (q : ℕ) (op : ExtOp) (x : BitString (extSignature.Arity op)) :
    (ofExtOp q op).eval x = extInterpretation (modGate q) op x := by
  cases op with
  | ac op =>
    cases op with
    | not =>
      change (!(ofAnd 1).eval x) = Unbounded.interpretation .not x
      rw [eval_ofAnd]
      simp [Unbounded.interpretation]
    | and m => exact eval_ofAnd m x
    | or m => exact eval_ofOr m x
  | gate m => exact eval_ofModGate q m x

/-- Every single-gate `AC⁰[q]` circuit `Circuit.oneGate op w` is computed by the `Sym⁺` circuit
`(ofExtOp q op).comap w` of size `extOpSize op`. -/
theorem eval_ofExtOp_comap (q : ℕ) (op : ExtOp) {n : ℕ}
    (w : Fin (extSignature.Arity op) → Fin n) (x : BitString n) :
    ((ofExtOp q op).comap w).eval x =
      (Circuit.oneGate (σ := extSignature) op w).eval (extInterpretation (modGate q)) x 0 := by
  rw [eval_comap, eval_ofExtOp, Circuit.eval_oneGate]
  rfl

/-! ### Variable splitting and Williams's fast `Sym⁺` evaluation -/

/-- The left `n₁`-bit submask of the `j`-th conjunction mask of
`C : SymPlusCircuit (n₁ + n₂) s`. -/
def leftMask (C : SymPlusCircuit (n₁ + n₂) s) (j : Fin s) : BitString n₁ :=
  fun i => C.masks j (Fin.castAdd n₂ i)

/-- The right `n₂`-bit submask of the `j`-th conjunction mask of
`C : SymPlusCircuit (n₁ + n₂) s`. -/
def rightMask (C : SymPlusCircuit (n₁ + n₂) s) (j : Fin s) : BitString n₂ :=
  fun i => C.masks j (Fin.natAdd n₁ i)

/-- **Williams's partial-evaluation coefficient table** [Williams, Section 3.2][Williams2014]:
for a right half-assignment `x₂ : BitString n₂` and a left pattern `p : BitString n₁`, counts how
many gates `j : Fin s` have left mask `p` and are satisfied on the right by `x₂`. The table has
`2 ^ n₁` entries regardless of the circuit size `s`. -/
def coeffTable (C : SymPlusCircuit (n₁ + n₂) s) (x₂ : BitString n₂) (p : BitString n₁) : ℕ :=
  ∑ j : Fin s, if C.leftMask j = p && evalMask (C.rightMask j) x₂ then 1 else 0

/-- **Bilinear Zeta-transform identity for `Sym⁺` circuits**: the Zeta transform of
`C.coeffTable x₂` at `x₁` equals `C.activeCount (Fin.append x₁ x₂)`. -/
theorem zetaTransform_coeffTable_eq_activeCount (C : SymPlusCircuit (n₁ + n₂) s)
    (x₁ : BitString n₁) (x₂ : BitString n₂) :
    zetaTransform (C.coeffTable x₂) x₁ = C.activeCount (Fin.append x₁ x₂) := by
  simp only [zetaTransform, coeffTable, activeCount]
  have hite (p : BitString n₁) :
      (if evalMask p x₁ = true then
        ∑ j : Fin s, (if (C.leftMask j = p && evalMask (C.rightMask j) x₂) = true then 1 else 0)
      else 0) =
      ∑ j : Fin s,
        if evalMask p x₁ = true then
          (if (C.leftMask j = p && evalMask (C.rightMask j) x₂) = true then 1 else 0)
        else 0 := by
    split_ifs <;> simp
  simp_rw [hite]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_eq_single (C.leftMask j)]
  · rw [evalMask_append]
    change (if evalMask (C.leftMask j) x₁ = true then
        if (decide (C.leftMask j = C.leftMask j) && evalMask (C.rightMask j) x₂) = true then
          1
        else 0
      else 0) =
      if (evalMask (C.leftMask j) x₁ && evalMask (C.rightMask j) x₂) = true then 1 else 0
    cases evalMask (C.leftMask j) x₁ <;> cases evalMask (C.rightMask j) x₂ <;> simp
  · intro p hp
    simp [hp.symm]

/-- **Fast multipoint evaluation of a `Sym⁺` circuit** [Williams, Theorem 3.2][Williams2014]:
evaluates `C` on `(x₁, x₂)` by applying the Fast Zeta Transform `fastZeta` to the coefficient
table `C.coeffTable x₂` and looking up the result in `C.sym`. -/
def fastSymPlusEval (C : SymPlusCircuit (n₁ + n₂) s)
    (x₁ : BitString n₁) (x₂ : BitString n₂) : Bool :=
  C.sym (fastZeta (C.coeffTable x₂) x₁)

/-- **Correctness of `fastSymPlusEval`**: `fastSymPlusEval` agrees with `C.eval` on every split
assignment `Fin.append x₁ x₂`. -/
@[simp] theorem fastSymPlusEval_eq_eval (C : SymPlusCircuit (n₁ + n₂) s)
    (x₁ : BitString n₁) (x₂ : BitString n₂) :
    C.fastSymPlusEval x₁ x₂ = C.eval (Fin.append x₁ x₂) := by
  rw [fastSymPlusEval, fastZeta_eq_zetaTransform, zetaTransform_coeffTable_eq_activeCount, eval]

/-- **Satisfiability of a `Sym⁺` circuit via `fastSymPlusEval`**: `C` is satisfiable on
`{0, 1} ^ (n₁ + n₂)` iff `C.fastSymPlusEval x₁ x₂ = true` for some `x₁ : BitString n₁` and
`x₂ : BitString n₂`. -/
theorem isSatisfiable_iff_exists_fastSymPlusEval (C : SymPlusCircuit (n₁ + n₂) s) :
    C.IsSatisfiable ↔ ∃ (x₁ : BitString n₁) (x₂ : BitString n₂),
      C.fastSymPlusEval x₁ x₂ = true := by
  simp only [IsSatisfiable, fastSymPlusEval_eq_eval]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun i => x (Fin.castAdd n₂ i), fun i => x (Fin.natAdd n₁ i), ?_⟩
    convert hx using 2
    funext k
    refine Fin.addCases (fun i => by simp [Fin.append_left])
      (fun i => by simp [Fin.append_right]) k
  · rintro ⟨x₁, x₂, h⟩
    exact ⟨Fin.append x₁ x₂, h⟩

end SymPlusCircuit

/-! ### Unconditional separations in `P`, `Σ₂`, and `NEXP`, and the `NEXP ⊆ ACC⁰` collapse -/

/-- Folding `xor` over a Boolean word computes `parity` of its slice. -/
theorem foldl_bne_eq_parity (w : List Bool) :
    w.foldl bne false = parity w.length (fun i => w[i]) := by
  have hcount : w.foldl bne false = decide (w.count true % 2 = 1) := by
    have hgen (b : Bool) (l : List Bool) :
        l.foldl bne b = (b != decide (l.count true % 2 = 1)) := by
      induction l generalizing b with
      | nil => cases b <;> simp
      | cons a l ih =>
        rw [List.foldl_cons, ih, List.count_cons]
        cases a <;> cases b <;>
        · by_cases h : l.count true % 2 = 1
          · have h0 : (l.count true + 1) % 2 = 0 := by omega
            simp [h, h0]
          · have h1 : (l.count true + 1) % 2 = 1 := by omega
            simp [h, h1]
    simpa using hgen false w
  rw [hcount, parity, parityOn, Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq,
    Finset.card_filter]
  have hcard (l : List Bool) :
      (∑ i : Fin l.length, if l[i] = true then 1 else 0) = l.count true := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.count_cons, ← ih]
      refine (Fin.sum_univ_succ fun i : Fin (l.length + 1) =>
        if (a :: l)[i] = true then (1 : ℕ) else 0).trans ?_
      cases a <;> simp [Nat.add_comm]
  rw [hcard w]

/-- **Parity is in `P`** (`Language.ofSlices parity ∈ P encBits`). -/
theorem parity_mem_P : (Language.ofSlices parity : Set (List Bool)) ∈ P encBits := by
  refine ⟨fun w => w.foldl bne false, ?_, fun w => ?_⟩
  · exact ComputableTidilyInPolyTime.bitsFoldlWithInput bne
      ComputableTidilyInPolyTime.id' (ComputableTidilyInPolyTime.const false)
  · change w ∈ (Language.ofSlices parity : Language Bool) ↔ w.foldl bne false = true
    rw [Language.mem_ofSlices, foldl_bne_eq_parity]

/-- **Parity is in `EXP`.** -/
theorem parity_mem_EXP : (Language.ofSlices parity : Set (List Bool)) ∈ EXP encBits :=
  P_subset_EXP parity_mem_P

/-- **Parity is in `NEXP`.** -/
theorem parity_mem_NEXP : (Language.ofSlices parity : Set (List Bool)) ∈ NEXP encBits :=
  EXP_subset_NEXP parity_mem_EXP

/-- **Unconditional separation `P ⊄ AC⁰`**: parity is in `P` and not in `AC⁰`. -/
theorem exists_mem_P_notMem_AC0 :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧ L ∉ AC0 :=
  ⟨Language.ofSlices parity, parity_mem_P, parity_notMem_AC0⟩

/-- **Unconditional separation `NEXP ⊄ AC⁰`**: parity is in `NEXP` and not in `AC⁰`. -/
theorem exists_mem_NEXP_notMem_AC0 :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧ L ∉ AC0 :=
  ⟨Language.ofSlices parity, parity_mem_NEXP, parity_notMem_AC0⟩

/-- **Unconditional separation `P ⊄ AC⁰[p]`** for every odd prime `p`: parity is in `P` and not in
`AC⁰[p]` [Razborov1987], [Smolensky1987]. -/
theorem exists_mem_P_notMem_AC0Mod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ P encBits ∧ L ∉ AC0Mod p :=
  ⟨Language.ofSlices parity, parity_mem_P, Smolensky.parity_notMem_AC0Mod hp2⟩

/-- **Unconditional separation `NEXP ⊄ AC⁰[p]`** for every odd prime `p`: parity is in `NEXP` and
not in `AC⁰[p]` [Razborov1987], [Smolensky1987]. -/
theorem exists_mem_NEXP_notMem_AC0Mod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧ L ∉ AC0Mod p :=
  ⟨Language.ofSlices parity, parity_mem_NEXP, Smolensky.parity_notMem_AC0Mod hp2⟩

/-- The class of languages over `Bool` decided at every input length `n` by circuits over the
`AC⁰[q]` basis (`Unbounded.extInterpretation (modGate q)`) of size at most `s n` (of arbitrary
depth). -/
def SIZEMod (q : ℕ) (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∀ n, ∃ C : Circuit extSignature n 1,
    C.Computes (extInterpretation (modGate q)) (single (L.slice n)) ∧ C.size ≤ s n}

/-- `SIZEMod q` is monotone in the size bound. -/
theorem SIZEMod_mono (q : ℕ) : Monotone (SIZEMod q) := by
  intro s₁ s₂ hs L hL n
  obtain ⟨C, hCc, hCs⟩ := hL n
  exact ⟨C, hCc, hCs.trans (hs n)⟩

/-- Every `AC⁰[q]` language lies in `SIZEMod q s` for some polynomially bounded `s`. -/
theorem exists_mem_SIZEMod_of_mem_AC0Mod {q : ℕ} {L : Language Bool} (hL : L ∈ AC0Mod q) :
    ∃ c k : ℕ, L ∈ SIZEMod q fun n => c * (n + 1) ^ k := by
  obtain ⟨d, s, hs, hC⟩ := ConstDepth.mem_iff.1 hL
  obtain ⟨c, k, hck⟩ := polynomiallyBounded_iff_le.1 hs
  refine ⟨c, k, fun n => ?_⟩
  obtain ⟨C, hCc, -, hCs⟩ := hC n
  exact ⟨C, hCc, hCs.trans (hck n)⟩

/-- **Simulating `SIZEMod q` in De Morgan `SIZE`**: a circuit with `MOD_q` gates of size at most
`c * (n + 1) ^ k` is simulated by a fan-in-two De Morgan circuit of size at most
`(2100 * (max q 1) ^ 3) ^ 2 * (c + 1) ^ 8 * (n + 1) ^ (8 * (k + 1))`. -/
theorem SIZEMod_subset_SIZE (q c k : ℕ) :
    SIZEMod q (fun n => c * (n + 1) ^ k) ⊆
      SIZE (fun n => (2100 * (max q 1) ^ 3) ^ 2 * (c + 1) ^ 8 * (n + 1) ^ (8 * (k + 1))) := by
  intro L hL n
  obtain ⟨C, hCc, hCs⟩ := hL n
  obtain ⟨D, hDe, hDs⟩ := Unbounded.exists_deMorgan_simulation_modGate q C
  have hDc : D.Computes Boolean.interpretation (single (L.slice n)) :=
    fun x => (congrFun hDe x).trans (hCc x)
  refine (complexity_le_of_computes D hDc).trans (hDs.trans ?_)
  have hn1 : n + 1 ≤ (n + 1) ^ (k + 1) := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (Nat.succ_pos k)
  have hk1 : (n + 1) ^ k ≤ (n + 1) ^ (k + 1) :=
    Nat.pow_le_pow_right (by omega) (Nat.le_succ k)
  have hsum : n + C.size + 1 ≤ (c + 1) * (n + 1) ^ (k + 1) := by
    dsimp only at hCs
    calc n + C.size + 1 ≤ (n + 1) + c * (n + 1) ^ k := by omega
      _ ≤ 1 * (n + 1) ^ (k + 1) + c * (n + 1) ^ (k + 1) := by
        rw [one_mul]
        exact Nat.add_le_add hn1 (Nat.mul_le_mul_left c hk1)
      _ = (c + 1) * (n + 1) ^ (k + 1) := by ring
  calc (2100 * (max q 1) ^ 3) ^ 2 * (n + C.size + 1) ^ 8
      ≤ (2100 * (max q 1) ^ 3) ^ 2 * ((c + 1) * (n + 1) ^ (k + 1)) ^ 8 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 8)
    _ = (2100 * (max q 1) ^ 3) ^ 2 * (c + 1) ^ 8 * (n + 1) ^ (8 * (k + 1)) := by
        rw [mul_pow, ← pow_mul]
        ring

/-- **Kannan's language escapes `SIZEMod q`**: for every `q, k, c : ℕ`,
`Kannan.language (8 * (k + 1))` has no circuits over the `AC⁰[q]` basis of size
`c * (n + 1) ^ k` [Kannan1982]. -/
theorem Kannan.language_notMem_SIZEMod (q k c : ℕ) :
    Kannan.language (8 * (k + 1)) ∉ SIZEMod q fun n => c * (n + 1) ^ k :=
  fun hc => Kannan.language_notMem_SIZE (8 * (k + 1))
    ((2100 * (max q 1) ^ 3) ^ 2 * (c + 1) ^ 8) (SIZEMod_subset_SIZE q c k hc)

/-- **Unconditional fixed-exponent `MOD_q` circuit lower bound in `Σ₂`** (for every modulus `q`,
prime or composite): for every `q, k : ℕ`, some language in `Σ₂` has no circuits over the `AC⁰[q]`
basis of size `O(n ^ k)` (even of unbounded depth), by combining `SIZEMod_subset_SIZE` with
Kannan's theorem [Kannan1982]. -/
theorem exists_mem_SigmaP_two_notMem_SIZEMod (q k : ℕ) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ SigmaP 2 encBits ∧
      ∀ c, L ∉ SIZEMod q fun n => c * (n + 1) ^ k := by
  obtain ⟨L, hL₂, hLnot⟩ := exists_mem_SigmaP_two_notMem_SIZE (8 * (k + 1))
  refine ⟨L, hL₂, fun c hc => ?_⟩
  exact hLnot ((2100 * (max q 1) ^ 3) ^ 2 * (c + 1) ^ 8) (SIZEMod_subset_SIZE q c k hc)

/-- **Unconditional fixed-exponent `MOD_q` circuit lower bound in `NEXP`** (for every modulus `q`,
prime or composite): for every `q, k : ℕ`, some language in `NEXP` (in fact in `Σ₂`) has no
circuits over the `AC⁰[q]` basis of size `O(n ^ k)`. -/
theorem exists_mem_NEXP_notMem_SIZEMod (q k : ℕ) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits ∧
      ∀ c, L ∉ SIZEMod q fun n => c * (n + 1) ^ k := by
  obtain ⟨L, hL₂, hLnot⟩ := exists_mem_SigmaP_two_notMem_SIZEMod q k
  exact ⟨L, SigmaP_subset_NEXP 2 hL₂, hLnot⟩

/-- **If `NEXP ⊆ ACC⁰`, then `NEXP ⊆ P/poly`** (via `ACC0 ⊆ PPoly`). -/
theorem NEXP_subset_PPoly_of_NEXP_subset_ACC0
    (h : ∀ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits → L ∈ ACC0) :
    ∀ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits → L ∈ PPoly :=
  fun L hL => ACC0_subset_PPoly (h L hL)

/-- **If `NEXP ⊆ ACC⁰`, then the polynomial hierarchy collapses to `Σ₂`**
(`PH enc = SigmaP 2 enc`), via `NP ⊆ NEXP`, `ACC0 ⊆ PPoly`, and the Karp–Lipton theorem
(`PH_eq_SigmaP_two_of_SAT`) [KarpLipton1980], [Williams2014]. -/
theorem PH_eq_SigmaP_two_of_NEXP_subset_ACC0
    (h : ∀ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits → L ∈ ACC0)
    {α : Type} (enc : α ↪ List Bool) :
    PH enc = SigmaP 2 enc := by
  apply PH_eq_SigmaP_two_of_SAT
  have hSAT_NEXP : (encCNF '' SAT : Set (List Bool)) ∈ NEXP encBits :=
    NP_subset_NEXP image_SAT_mem_NP
  exact ⟨encCNF '' SAT, ACC0_subset_PPoly (h _ hSAT_NEXP),
    fun φ => encCNF.injective.mem_set_image.symm⟩

/-- **If `NEXP ⊆ ACC⁰`, then Kannan's `Σ₃` language `Kannan.language k` lies in `Σ₂`**, via
`PH_eq_SigmaP_two_of_NEXP_subset_ACC0` and `Kannan.language_mem_SigmaP_three`. -/
theorem Kannan.language_mem_SigmaP_two_of_NEXP_subset_ACC0
    (h : ∀ L : Language Bool, (L : Set (List Bool)) ∈ NEXP encBits → L ∈ ACC0) (k : ℕ) :
    (Kannan.language k : Set (List Bool)) ∈ SigmaP 2 encBits := by
  rw [← PH_eq_SigmaP_two_of_NEXP_subset_ACC0 h encBits]
  exact SigmaP_subset_PH 3 (Kannan.language_mem_SigmaP_three k)

end Cslib.Circuits.Boolean
