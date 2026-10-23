/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Complexity.Foundations.Data.Nat.Radix

/-!
# Fixed tuples of radix registers

The number of registers and their enumeration are fixed independently of the input. Packing and
reading a fixed digit therefore require only finitely many binary additions, multiplications,
divisions and remainders. The radix itself remains an ordinary binary argument.

The pure operations and their recovery/capacity results live in `Cslib.Radix`, in the module
`Complexity.Foundations.Data.Nat.Radix`. Deprecated compatibility names remain here.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.digit_inSpace`: fixed-position digit extraction.
* `Turing.MultiTapeNTM.ConfigurationGraph.component_inSpace`: finite-tuple component extraction.
* `Turing.MultiTapeNTM.ConfigurationGraph.pack_inSpace`: finite-tuple packing.
-/

@[expose] public section

namespace Turing.MultiTapeNTM.ConfigurationGraph

/-- Deprecated Nat-specialized spelling of Mathlib's little-endian packing. -/
@[deprecated Nat.ofDigits +typeChanged (since := "2026-10-23")]
abbrev packList (B : ℕ) : List ℕ → ℕ := Nat.ofDigits B

@[deprecated Cslib.Radix.digit (since := "2026-10-23")]
alias digit := Cslib.Radix.digit

@[deprecated Cslib.Radix.digit_ofDigits (since := "2026-10-23")]
theorem digit_packList {B : ℕ} (hB : 0 < B) (l : List ℕ)
    (hl : ∀ a ∈ l, a < B) (i : ℕ) (hi : i < l.length) :
    Cslib.Radix.digit B (Nat.ofDigits B l) i = l[i] :=
  Cslib.Radix.digit_ofDigits hB l hl i hi

@[deprecated Nat.ofDigits_lt_base_pow_length_of_pos (since := "2026-10-23")]
theorem packList_lt {B : ℕ} (_hB : 0 < B) (l : List ℕ) (hl : ∀ a ∈ l, a < B) :
    Nat.ofDigits B l < B ^ l.length :=
  Nat.ofDigits_lt_base_pow_length_of_pos _hB l hl

@[deprecated Cslib.Radix.pack (since := "2026-10-23")]
alias pack := Cslib.Radix.pack

@[deprecated Cslib.Radix.component (since := "2026-10-23")]
alias component := Cslib.Radix.component

variable {ι : Type} [Fintype ι]

@[deprecated Cslib.Radix.component_pack (since := "2026-10-23")]
theorem component_pack {B : ℕ} (hB : 0 < B) {f : ι → ℕ} (hf : ∀ i, f i < B) (i : ι) :
    Cslib.Radix.component B (Cslib.Radix.pack B f) i = f i :=
  Cslib.Radix.component_pack hB hf i

@[deprecated Cslib.Radix.pack_lt (since := "2026-10-23")]
alias pack_lt := Cslib.Radix.pack_lt

open MultiTapeTM ComputableTidilyInSpace

/-- Reading a fixed digit uses linear space in the binary radix and packed value. -/
theorem digit_inSpace (i : ℕ) :
    ComputableTidilyInSpace (fun p : ℕ × ℕ => Cslib.Radix.digit p.1 p.2 i)
      (encPair encNat encNat) encNat fun p => (encPair encNat encNat p).length := by
  induction i with
  | zero => exact budget_natMod (snd _ _) (fst _ _)
  | succ i ih =>
    exact budget_comp_linear ih
      (budget_prod (fst _ _) (budget_natDiv (snd _ _) (fst _ _)))

/-- Reading any one fixed component is a native deterministic linear-space routine. -/
theorem component_inSpace (i : ι) :
    ComputableTidilyInSpace (fun p : ℕ × ℕ => Cslib.Radix.component p.1 p.2 i)
      (encPair encNat encNat) encNat fun p => (encPair encNat encNat p).length :=
  digit_inSpace (Fintype.equivFin ι i).val

/-- Packing a fixed tuple of computed components preserves a common space budget. -/
theorem pack_inSpace {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {B : α → ℕ}
    {f : α → ι → ℕ} (hB : ComputableTidilyInSpace B enc encNat S)
    (hf : ∀ i, ComputableTidilyInSpace (fun a => f a i) enc encNat S)
    (hin : (fun a => (enc a).length) ≼ S) :
    ComputableTidilyInSpace (fun a => Cslib.Radix.pack (B a) (f a)) enc encNat S := by
  have hlist : ∀ l : List ι, ComputableTidilyInSpace
      (fun a => Nat.ofDigits (B a) (l.map (f a))) enc encNat S := by
    intro l
    induction l with
    | nil => exact budget_const 0 hin
    | cons i l ih => exact budget_natAdd (hf i) (budget_natMul hB ih)
  exact hlist (List.ofFn (Fintype.equivFin ι).symm) |>.of_enc_eq fun a => by
    simp [Cslib.Radix.pack, List.map_ofFn, Function.comp_def]

end Turing.MultiTapeNTM.ConfigurationGraph
