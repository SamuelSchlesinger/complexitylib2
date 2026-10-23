/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.Linarith

/-!
# Fixed tuples of radix registers

The number of registers and their enumeration are fixed independently of the input. Packing and
reading a fixed digit therefore require only finitely many binary additions, multiplications,
divisions and remainders. The radix itself remains an ordinary binary argument.

## Main definitions

* `Turing.MultiTapeNTM.ConfigurationGraph.packList`: little-endian radix packing.
* `Turing.MultiTapeNTM.ConfigurationGraph.digit`: fixed-position digit extraction.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.digit_packList`: exact digit recovery.
* `Turing.MultiTapeNTM.ConfigurationGraph.packList_lt`: the packed tuple fits in a radix power.
-/

@[expose] public section

namespace Turing.MultiTapeNTM.ConfigurationGraph

/-- Little-endian packing in radix `B`, using Mathlib's `Nat.ofDigits`. -/
abbrev packList (B : ℕ) : List ℕ → ℕ := Nat.ofDigits B

/-- Read a digit at a fixed position. -/
def digit (B x : ℕ) : ℕ → ℕ
  | 0 => x % B
  | i + 1 => digit B (x / B) i

/-- Each bounded digit is recovered exactly by unpacking. -/
theorem digit_packList {B : ℕ} (hB : 0 < B) (l : List ℕ)
    (hl : ∀ a ∈ l, a < B) (i : ℕ) (hi : i < l.length) :
    digit B (packList B l) i = l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    have ha : a < B := hl a (by simp)
    have ht : ∀ b ∈ l, b < B := fun b hb => hl b (by simp [hb])
    cases i with
    | zero =>
      simp only [digit, packList, Nat.ofDigits, Nat.cast_id, List.getElem_cons_zero,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    | succ i =>
      simp only [digit, packList, Nat.ofDigits, Nat.cast_id, Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt ha, Nat.zero_add, List.getElem_cons_succ]
      exact ih ht i (by simpa using hi)

/-- Bounded tuples fit below the corresponding radix power. -/
theorem packList_lt {B : ℕ} (_hB : 0 < B) (l : List ℕ) (hl : ∀ a ∈ l, a < B) :
    packList B l < B ^ l.length := by
  induction l with
  | nil => simp [packList, Nat.ofDigits]
  | cons a l ih =>
    have ha := hl a (by simp)
    have ht := ih (fun b hb => hl b (by simp [hb]))
    simp only [packList, Nat.ofDigits, List.length_cons, pow_succ]
    nlinarith

variable {ι : Type} [Fintype ι]

/-- Pack a fixed finite tuple using a fixed enumeration. -/
noncomputable def pack (B : ℕ) (f : ι → ℕ) : ℕ :=
  packList B (List.ofFn fun i => f ((Fintype.equivFin ι).symm i))

/-- Read one component of a packed finite tuple. -/
noncomputable def component (B x : ℕ) (i : ι) : ℕ :=
  digit B x (Fintype.equivFin ι i).val

theorem component_pack {B : ℕ} (hB : 0 < B) {f : ι → ℕ} (hf : ∀ i, f i < B) (i : ι) :
    component B (pack B f) i = f i := by
  unfold component pack
  have hlist : ∀ a ∈ List.ofFn (fun i => f ((Fintype.equivFin ι).symm i)), a < B := by
    simpa using (fun i : Fin (Fintype.card ι) => hf ((Fintype.equivFin ι).symm i))
  rw [digit_packList hB _ hlist _ (by simp)]
  simp

theorem pack_lt {B : ℕ} (hB : 0 < B) {f : ι → ℕ} (hf : ∀ i, f i < B) :
    pack B f < B ^ Fintype.card ι := by
  simpa only [pack, List.length_ofFn] using
    packList_lt hB (List.ofFn fun i => f ((Fintype.equivFin ι).symm i)) (by
      simpa using fun i : Fin (Fintype.card ι) => hf ((Fintype.equivFin ι).symm i))

open MultiTapeTM ComputableTidilyInSpace

/-- Reading a fixed digit uses linear space in the binary radix and packed value. -/
theorem digit_inSpace (i : ℕ) :
    ComputableTidilyInSpace (fun p : ℕ × ℕ => digit p.1 p.2 i) (encPair encNat encNat) encNat
      fun p => (encPair encNat encNat p).length := by
  induction i with
  | zero => exact budget_natMod (snd _ _) (fst _ _)
  | succ i ih =>
    exact budget_comp_linear ih
      (budget_prod (fst _ _) (budget_natDiv (snd _ _) (fst _ _)))

/-- Reading any one fixed component is a native deterministic linear-space routine. -/
theorem component_inSpace (i : ι) :
    ComputableTidilyInSpace (fun p : ℕ × ℕ => component p.1 p.2 i)
      (encPair encNat encNat) encNat fun p => (encPair encNat encNat p).length :=
  digit_inSpace (Fintype.equivFin ι i).val

/-- Packing a fixed tuple of computed components preserves a common space budget. -/
theorem pack_inSpace {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {B : α → ℕ}
    {f : α → ι → ℕ} (hB : ComputableTidilyInSpace B enc encNat S)
    (hf : ∀ i, ComputableTidilyInSpace (fun a => f a i) enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableTidilyInSpace (fun a => pack (B a) (f a)) enc encNat S := by
  have hlist : ∀ l : List ι, ComputableTidilyInSpace
      (fun a => packList (B a) (l.map (f a))) enc encNat S := by
    intro l
    induction l with
    | nil => exact budget_const 0 hin
    | cons i l ih => exact budget_natAdd (hf i) (budget_natMul hB ih)
  exact hlist (List.ofFn (Fintype.equivFin ι).symm) |>.of_enc_eq fun a => by
    simp [pack, List.map_ofFn, Function.comp_def]

end Turing.MultiTapeNTM.ConfigurationGraph
