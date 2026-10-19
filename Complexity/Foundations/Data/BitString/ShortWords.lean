/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Set.Finite.List
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn

/-!
# Binary words of bounded length

The binary words of length at most `L` form a finite set `shortWords L` with `2 ^ (L + 1) - 1`
elements: the words of length `m` are the `2 ^ m` lists `List.ofFn r` for `r : Fin m → Bool`, and
`∑ m ≤ L, 2 ^ m = 2 ^ (L + 1) - 1`.

## Main definitions

* `Cslib.BitString.shortWords`: the binary words of length at most `L`.

## Main results

* `Cslib.BitString.mem_shortWords`: membership is the length bound.
* `Cslib.BitString.card_shortWords`: there are `2 ^ (L + 1) - 1` such words.
* `Cslib.BitString.card_shortWords_lt`: in particular fewer than `2 ^ (L + 1)`.
-/

@[expose] public section

namespace Cslib.BitString

open Finset

/-- The binary words of length at most `L`. -/
noncomputable def shortWords (L : ℕ) : Finset (List Bool) :=
  (List.finite_length_le Bool L).toFinset

@[simp]
theorem mem_shortWords {L : ℕ} {w : List Bool} : w ∈ shortWords L ↔ w.length ≤ L := by
  simp [shortWords]

theorem nil_mem_shortWords (L : ℕ) : [] ∈ shortWords L := by simp

/-- The binary words of length at most `L` are the words `List.ofFn r` for `r : Fin m → Bool` and
`m ≤ L`. -/
theorem shortWords_eq_biUnion (L : ℕ) :
    shortWords L =
      (range (L + 1)).biUnion fun m => univ.image (List.ofFn : (Fin m → Bool) → _) := by
  ext w
  simp only [mem_shortWords, mem_biUnion, mem_range, mem_image, mem_univ, true_and]
  refine ⟨fun hw => ⟨w.length, by omega, w.get, List.ofFn_get w⟩, ?_⟩
  rintro ⟨m, hm, r, rfl⟩
  rw [List.length_ofFn]
  omega

/-- There are `2 ^ (L + 1) - 1` binary words of length at most `L`. -/
theorem card_shortWords (L : ℕ) : #(shortWords L) = 2 ^ (L + 1) - 1 := by
  rw [shortWords_eq_biUnion, card_biUnion]
  · simp_rw [card_image_of_injective _ List.ofFn_injective, card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
    rw [Nat.geomSum_eq le_rfl, Nat.div_one]
  · intro m _ m' _ hmm'
    refine disjoint_left.2 fun w hw hw' => hmm' ?_
    obtain ⟨r, -, rfl⟩ := mem_image.1 hw
    obtain ⟨r', -, hr'⟩ := mem_image.1 hw'
    simpa using congrArg List.length hr'.symm

/-- There are fewer than `2 ^ (L + 1)` binary words of length at most `L`. -/
theorem card_shortWords_lt (L : ℕ) : #(shortWords L) < 2 ^ (L + 1) := by
  rw [card_shortWords]
  exact Nat.sub_lt (Nat.two_pow_pos _) one_pos

end Cslib.BitString
