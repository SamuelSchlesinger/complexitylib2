/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.ACC0.Simulation
public import Complexity.Computability.Circuit.Boolean.ACC0.SymPlus
public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Complexity.Classes.Inclusions
public import Complexity.Computability.Complexity.Classes.PH.Kannan
import Complexity.Computability.Circuit.Boolean.Smolensky.Majority
import Complexity.Computability.Complexity.Classes.PH.KarpLipton
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Circuit lower bounds against `AC⁰[q]`, `SIZEMod q`, and `ACC⁰`

This module establishes unconditional and satisfiability-to-lower-bounds separations against
modular circuit classes:

* **Unconditional separations in `P` and `NEXP` against `AC⁰` and `AC⁰[p]`**: parity lies in
  `P ⊆ EXP ⊆ NEXP` (`parity_mem_P`, `parity_mem_NEXP`), giving languages in `P` and `NEXP` outside
  `AC0` (`exists_mem_P_notMem_AC0`, `exists_mem_NEXP_notMem_AC0`) and outside `AC0Mod p` for every
  odd prime `p` (`exists_mem_P_notMem_AC0Mod`, `exists_mem_NEXP_notMem_AC0Mod`).
* **Unconditional fixed-exponent `MOD_q` circuit lower bounds in `Σ₂` and `NEXP` for every modulus
  `q`**: combining `SIZEMod_subset_SIZE` with Kannan's theorem shows that
  `Kannan.language (8 * (k + 1))` escapes `SIZEMod q (c (n + 1) ^ k)`
  (`Kannan.language_notMem_SIZEMod`), yielding languages in `Σ₂` and `NEXP` outside
  `SIZEMod q (O(n ^ k))` for every modulus `q` (`exists_mem_SigmaP_two_notMem_SIZEMod`,
  `exists_mem_NEXP_notMem_SIZEMod`).
* **Karp–Lipton collapse from `NEXP ⊆ ACC⁰`** [Williams2014]: if `NEXP ⊆ ACC⁰`, then
  `NEXP ⊆ P/poly` (`NEXP_subset_PPoly_of_NEXP_subset_ACC0`) and `PH = Σ₂`
  (`PH_eq_SigmaP_two_of_NEXP_subset_ACC0`), placing Kannan's `Σ₃` language into `Σ₂`
  (`Kannan.language_mem_SigmaP_two_of_NEXP_subset_ACC0`). Williams's full `NEXP ⊄ ACC⁰` separation
  (which additionally requires the Yao–Beigel–Tarui `Sym⁺` compilation and the Impagliazzo–
  Kabanets–Wigderson easy-witness collapse from fast `Sym⁺` satisfiability) is not proved here.

## Main results

* `Cslib.Circuits.Boolean.parity_mem_P`, `Cslib.Circuits.Boolean.parity_mem_EXP`,
  `Cslib.Circuits.Boolean.parity_mem_NEXP`: parity lies in `P ⊆ EXP ⊆ NEXP`.
* `Cslib.Circuits.Boolean.exists_mem_SigmaP_two_notMem_SIZEMod`,
  `Cslib.Circuits.Boolean.exists_mem_NEXP_notMem_SIZEMod`: unconditional fixed-degree `MOD_q`
  circuit lower bounds in `Σ₂` and `NEXP` for every modulus `q`.
* `Cslib.Circuits.Boolean.PH_eq_SigmaP_two_of_NEXP_subset_ACC0`,
  `Cslib.Circuits.Boolean.Kannan.language_mem_SigmaP_two_of_NEXP_subset_ACC0`: `NEXP ⊆ ACC⁰`
  collapses `PH` to `Σ₂` and places Kannan's `Σ₃` language into `Σ₂`.

## References

* [R. Williams, *Nonuniform ACC Circuit Lower Bounds*][Williams2014]
* [R. Kannan, *Circuit-size lower bounds and non-reducibility to sparse sets*][Kannan1982]
* [R. M. Karp, R. J. Lipton, *Some connections between nonuniform and uniform complexity
  classes*][KarpLipton1980]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Set Finset BitString Unbounded Cslib.Complexity Turing.MultiTapeTM

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
  exact ⟨L, Cslib.Complexity.SigmaP_subset_NEXP 2 hL₂, hLnot⟩

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
