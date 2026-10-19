/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (local addition beside the vendored `Turing.MultiTapeTM.Universal` files)

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Machine
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
-- `Cslib.Complexity.Diagonal.universal_bounds_le` belongs beside `runBound`; it is proved with
-- the time hierarchy for now
import Complexity.Computability.Complexity.Classes.Hierarchy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# The universal function with a unary clock in polynomial time

The universal function `Turing.MultiTapeTM.Universal.universal` runs a described machine on an
input for a given number of steps. Its time and space are polynomial in the length of the
description, of the input and of the number of steps written in unary
(`Turing.MultiTapeTM.Universal.universal_bounds_unary`), so it is tidily computable in polynomial
time when the number of steps is written in unary
(`Turing.MultiTapeTM.Universal.computableTidilyInPolyTime_universal`). Written in binary, the
number of steps would be exponential in its length.

## Main results

* `Turing.MultiTapeTM.Universal.runBound_mono`: the space bound grows with the number of steps.
* `Turing.MultiTapeTM.Universal.universal_bounds_unary`: the time and space of the universal
  function, polynomially in the length of its input with the number of steps in unary.
* `Turing.MultiTapeTM.Universal.computableTidilyInPolyTime_universal`: the universal function,
  with its number of steps in unary, is polynomial-time.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeTM.Universal

open ComputableTidilyInPolyTime

theorem runBound_mono {D N t t' : ℕ} (h : t ≤ t') : runBound D N t ≤ runBound D N t' := by
  unfold runBound ctxBound cfgBound tapeBound
  gcongr

/-- The time and space of the universal function, polynomially in the length of its input with
the number of steps in unary. -/
theorem universal_bounds_unary (i : Desc × List ℕ × ℕ) :
    (i.2.2 + 1) * (stepBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
        runBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
          ((encNat i.2.2).length + 1) ^ 2) + ((eIn i).length + 1) ^ 2 ≤
      100025 * ((encPair eDesc (encPair (encList encUnary) encUnary) i).length + 1) ^ 8 ∧
    runBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 + (eIn i).length ≤
      205 * ((encPair eDesc (encPair (encList encUnary) encUnary) i).length + 1) ^ 3 := by
  obtain ⟨d, x, t⟩ := i
  set n := (encPair eDesc (encPair (encList encUnary) encUnary) (d, x, t)).length with hn
  have hlen : n = 2 * descLen d + 1 + (2 * (encList encUnary x).length + 1 + t) := by
    simp [hn, descLen]
  have hL := length_encNat_le t
  have hIn : (eIn (d, x, t)).length ≤ 5 * n + 2 := by
    simp only [eIn, length_encPair]
    simp only [descLen] at hlen
    omega
  obtain ⟨h₁, h₂⟩ := Cslib.Complexity.Diagonal.universal_bounds_le (D := descLen d)
    (N := (encList encUnary x).length) (J := t + 1) (B := n) (L := (encNat t).length)
    (by omega) (by omega) (by omega) (by omega)
  have hstep := stepBound_mono (D := descLen d) (N := (encList encUnary x).length) le_rfl le_rfl
    (Nat.le_add_right t 1)
  have hrun := runBound_mono (D := descLen d) (N := (encList encUnary x).length)
    (Nat.le_add_right t 1)
  have ht : t + 1 ≤ n + 1 := by omega
  have hpow : (t + 1) ^ 3 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_left ht 3
  simp only at h₁ h₂ hstep hrun ⊢
  constructor
  · have hA : (t + 1) * (stepBound (descLen d) (encList encUnary x).length t +
        runBound (descLen d) (encList encUnary x).length t + ((encNat t).length + 1) ^ 2) ≤
        100000 * (n + 1) ^ 5 * (n + 1) ^ 3 :=
      calc _ ≤ (t + 1 + 1) * (stepBound (descLen d) (encList encUnary x).length (t + 1) +
            runBound (descLen d) (encList encUnary x).length (t + 1) +
              ((encNat t).length + 1) ^ 2) := Nat.mul_le_mul (by omega) (by omega)
        _ ≤ _ := h₁
        _ ≤ _ := Nat.mul_le_mul_left _ hpow
    have hB : ((eIn (d, x, t)).length + 1) ^ 2 ≤ 25 * (n + 1) ^ 8 := by
      calc _ ≤ (5 * (n + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 25 * (n + 1) ^ 2 := by ring
        _ ≤ 25 * (n + 1) ^ 8 := Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right (by omega) (by omega))
    have : 100000 * (n + 1) ^ 5 * (n + 1) ^ 3 = 100000 * (n + 1) ^ 8 := by ring
    omega
  · have hA : runBound (descLen d) (encList encUnary x).length t ≤ 200 * (n + 1) ^ 3 :=
      calc _ ≤ _ := hrun
        _ ≤ 200 * (n + 1) ^ 2 * (t + 1) := h₂
        _ ≤ 200 * (n + 1) ^ 2 * (n + 1) := Nat.mul_le_mul_left _ ht
        _ = 200 * (n + 1) ^ 3 := by ring
    have hB : 5 * n + 2 ≤ 5 * (n + 1) ^ 3 := by
      have : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by omega) _
      omega
    omega

/-- **The universal function with a unary clock is polynomial-time**: written in unary, the number
of steps counts towards the length of the input. -/
@[fun_prop]
theorem computableTidilyInPolyTime_universal :
    ComputableTidilyInPolyTime universal
      (encPair eDesc (encPair (encList encUnary) encUnary)) eOut := by
  have hconv : ComputableTidilyInPolyTime (fun i : Desc × List ℕ × ℕ => i)
      (encPair eDesc (encPair (encList encUnary) encUnary)) eIn := by
    have : (fun i : Desc × List ℕ × ℕ => i) = fun i => (i.1, i.2.1, i.2.2) := rfl
    rw [this]
    fun_prop
  obtain ⟨d, e, hdeg⟩ := hconv.exists_degree
  exact (computableTidilyInO_universal.comp hdeg.inO).computableTidilyInPolyTime
    ((PolyBounded.of_forall_le 1 d fun _ => by simp).add
      (PolyBounded.of_forall_le 100025 8 fun i => (universal_bounds_unary i).1))
    ((PolyBounded.of_forall_le 1 d fun _ => by simp).add
      (PolyBounded.of_forall_le 205 3 fun i => (universal_bounds_unary i).2))

end Turing.MultiTapeTM.Universal
