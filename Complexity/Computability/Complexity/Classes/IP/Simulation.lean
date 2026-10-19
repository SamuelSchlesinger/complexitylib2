/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.IP.CoinFixing
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Configuration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Data.Nat.Size

/-!
# Counting the accepting coins in polynomial space

This file computes, for a verifier machine, the number of coin values whose programs accept after
a history (`Cslib.Complexity.Interaction.accepted`), within space polynomial in the input and the
history, and in exponential time.

* A replay keeping only whether it is still live
  (`Cslib.Complexity.Interaction.aliveStep`) decides whether the program of given coins accepts
  after a history (`Cslib.Complexity.Interaction.accepts_eq_true_iff`), in polynomial time
  (`Cslib.Complexity.Interaction.computableTidilyInPolyTime_accepts`): it folds one instruction per
  coin over the configuration of the machine, whose storage grows by a bounded amount per
  instruction.
* The coin values are enumerated by a binary counter, and the accepting ones are counted with a
  binary accumulator (`Cslib.Complexity.Interaction.countAccepts`,
  `Cslib.Complexity.Interaction.countAccepts_eq_accepted`), in polynomial space
  (`Cslib.Complexity.Interaction.computableTidilyInPolySpace_countAccepts`).

`Cslib.Complexity.ComputableTidilyInPolySpace` packages tidy computability within polynomial space
and some time, with its closure under composition, pairing, case distinction and iteration
(`Cslib.Complexity.ComputableTidilyInPolySpace.iterate`).

## Main definitions

* `Cslib.Complexity.ComputableTidilyInPolySpace`: computability within polynomial space.
* `Cslib.Complexity.Interaction.accepts`: whether the program of given coins accepts.
* `Cslib.Complexity.Interaction.countAccepts`: the number of accepting coin values.

## Main results

* `Cslib.Complexity.ComputableTidilyInPolySpace.iterate`: iteration within polynomial space.
* `Cslib.Complexity.Interaction.computableTidilyInPolyTime_accepts`: acceptance in polynomial time.
* `Cslib.Complexity.Interaction.countAccepts_eq_accepted`: the count of accepting coin values.
* `Cslib.Complexity.Interaction.computableTidilyInPolySpace_countAccepts`: the count in polynomial
  space.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

/-! ### Polynomial space -/

/-- `f` is tidily computable within some time and within space polynomially bounded in the length
of the encoded input. -/
def ComputableTidilyInPolySpace {α β : Type} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) : Prop :=
  ∃ T S, PolyBounded (fun a => (encIn a).length) S ∧ ComputableTidilyInO f encIn encOut T S

namespace ComputableTidilyInPolySpace

variable {α β γ δ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool} {encD : δ ↪ List Bool}

/-- Polynomial time is within polynomial space. -/
theorem of_polyTime {f : α → β} (h : ComputableTidilyInPolyTime f encIn encMid) :
    ComputableTidilyInPolySpace f encIn encMid := by
  obtain ⟨d, _, h⟩ := h.exists_degree
  exact ⟨_, _, PolyBounded.of_forall_le (u := fun a => ((encIn a).length + 1) ^ d) 1 d
    fun a => by simp, h.inO⟩

/-- The encoded values have polynomial length. -/
theorem polyBounded_length {f : α → β} (h : ComputableTidilyInPolySpace f encIn encMid) :
    PolyBounded (fun a => (encIn a).length) fun a => (encMid (f a)).length := by
  obtain ⟨T, S, hS, h⟩ := h
  obtain ⟨c, hc⟩ := h.length_le
  exact ((PolyBounded.const c).mul (hS.add (.const 1))).mono hc

/-- Composition. -/
theorem comp {f : β → γ} {g : α → β} (hf : ComputableTidilyInPolySpace f encMid encOut)
    (hg : ComputableTidilyInPolySpace g encIn encMid) :
    ComputableTidilyInPolySpace (fun a => f (g a)) encIn encOut := by
  have hlen := hg.polyBounded_length
  obtain ⟨Tf, Sf, hSf, hf'⟩ := hf
  obtain ⟨Tg, Sg, hSg, hg'⟩ := hg
  exact ⟨_, _, hSg.add (hSf.comp hlen), hf'.comp hg'⟩

/-- Pairing. -/
theorem prod {f : α → β} {g : α → δ} (hf : ComputableTidilyInPolySpace f encIn encMid)
    (hg : ComputableTidilyInPolySpace g encIn encD) :
    ComputableTidilyInPolySpace (fun a => (f a, g a)) encIn (encPair encMid encD) := by
  obtain ⟨Tf, Sf, hSf, hf⟩ := hf
  obtain ⟨Tg, Sg, hSg, hg⟩ := hg
  exact ⟨_, _, hSf.add hSg, hf.prod hg⟩

/-- Case distinction. -/
theorem ite {c : α → Bool} {f g : α → β} (hc : ComputableTidilyInPolySpace c encIn encBool)
    (hf : ComputableTidilyInPolySpace f encIn encMid)
    (hg : ComputableTidilyInPolySpace g encIn encMid) :
    ComputableTidilyInPolySpace (fun a => if c a then f a else g a) encIn encMid := by
  obtain ⟨Tc, Sc, hSc, hc⟩ := hc
  obtain ⟨Tf, Sf, hSf, hf⟩ := hf
  obtain ⟨Tg, Sg, hSg, hg⟩ := hg
  refine ⟨_, _, (hSc.add (hSf.add hSg)).mono fun a => ?_, hc.ite hf hg⟩
  split_ifs <;> lia

/-- Agreement with a computable function. -/
theorem congr {f g : α → β} (h : ComputableTidilyInPolySpace f encIn encMid)
    (hfg : ∀ a, f a = g a) : ComputableTidilyInPolySpace g encIn encMid := by
  rwa [show g = f from funext fun a => (hfg a).symm]

/-- **Iteration within polynomial space**: iterating a step computable within polynomial space a
number of times computed in polynomial time in binary, from a start computable within polynomial
space, is within polynomial space when all the states along the way have polynomial length. -/
theorem iterate [Inhabited β] {n : α → ℕ} {init : α → β} {step : β → β}
    (hn : ComputableTidilyInPolyTime n encIn encNat)
    (hinit : ComputableTidilyInPolySpace init encIn encMid)
    (hstep : ComputableTidilyInPolySpace step encMid encMid) {B : α → ℕ}
    (hB : PolyBounded (fun a => (encIn a).length) B)
    (hstate : ∀ a, ∀ k ≤ n a, (encMid (step^[k] (init a))).length ≤ B a) :
    ComputableTidilyInPolySpace (fun a => step^[n a] (init a)) encIn encMid := by
  obtain ⟨dn, _, hn'⟩ := hn.exists_degree
  obtain ⟨Ti, Si, hSi, hinit⟩ := hinit
  obtain ⟨Ts, Ss, hSs, hstep⟩ := hstep
  obtain ⟨cs, ds, hSs⟩ := hSs.exists_le
  have hit := ComputableTidilyInO.iterate hn'.inO hinit hstep
    (R := fun a => (Finset.range (n a + 1)).sup fun k => Ts (step^[k] (init a)))
    (Q := fun a => cs * (B a + 1) ^ ds) (B := B)
    (fun a k hk => Finset.le_sup (f := fun k => Ts (step^[k] (init a)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
    (fun a k hk => (hSs _).trans (Nat.mul_le_mul_left cs
      (Nat.pow_le_pow_left (Nat.add_le_add_right (hstate a k hk) 1) ds)))
    hstate
  refine ⟨_, _, ?_, hit⟩
  have hQ : PolyBounded (fun a => (encIn a).length) fun a => cs * (B a + 1) ^ ds :=
    PolyBounded.comp (size' := id) (v := fun m => cs * (m + 1) ^ ds)
      (PolyBounded.of_forall_le cs ds fun _ => le_rfl) hB
  exact ((((PolyBounded.of_forall_le (u := fun a => ((encIn a).length + 1) ^ dn) 1 dn
    fun a => by simp).add hSi).add hQ).add hB).add hn.polyBounded_length

end ComputableTidilyInPolySpace

namespace Interaction

/-! ### A binary counter -/

/-- Binary increment, least significant bit first, discarding the final carry. -/
def incrementBits : List Bool → List Bool
  | [] => []
  | false :: w => true :: w
  | true :: w => false :: incrementBits w

/-- The value of a word in binary, least significant bit first. -/
def lsbValue : List Bool → ℕ
  | [] => 0
  | b :: w => b.toNat + 2 * lsbValue w

@[simp] theorem length_incrementBits : ∀ w, (incrementBits w).length = w.length
  | [] => rfl
  | false :: _ => rfl
  | true :: w => by simp [incrementBits, length_incrementBits w]

theorem lsbValue_lt : ∀ w, lsbValue w < 2 ^ w.length
  | [] => by simp [lsbValue]
  | b :: w => by
    have := lsbValue_lt w
    cases b <;> simp [lsbValue, pow_succ] <;> lia

theorem lsbValue_incrementBits : ∀ w, lsbValue w + 1 < 2 ^ w.length →
    lsbValue (incrementBits w) = lsbValue w + 1
  | [] => by simp [lsbValue]
  | false :: w => fun _ => by simp [incrementBits, lsbValue]; lia
  | true :: w => fun h => by
    simp only [lsbValue, List.length_cons, pow_succ, Bool.toNat_true, incrementBits,
      Bool.toNat_false] at h ⊢
    rw [lsbValue_incrementBits w (by lia)]
    lia

theorem lsbValue_injective : ∀ {w w' : List Bool}, w.length = w'.length →
    lsbValue w = lsbValue w' → w = w'
  | [], [], _, _ => rfl
  | b :: w, b' :: w', hl, hv => by
    simp only [lsbValue] at hv
    have hb : b = b' := by
      cases b <;> cases b' <;> first | rfl | (simp at hv; lia)
    subst hb
    exact congrArg _ (lsbValue_injective (by simpa using hl) (by lia))

@[simp] theorem lsbValue_replicate_false : ∀ m, lsbValue (List.replicate m false) = 0
  | 0 => rfl
  | m + 1 => by simp [List.replicate_succ, lsbValue, lsbValue_replicate_false m]

theorem lsbValue_replicate_true : ∀ m, lsbValue (List.replicate m true) + 1 = 2 ^ m
  | 0 => rfl
  | m + 1 => by
    have := lsbValue_replicate_true m
    simp only [List.replicate_succ, lsbValue, Bool.toNat_true, pow_succ]
    lia

/-- The counter counts: the `j`-th iterate from zero has value `j`, below `2 ^ m`. -/
theorem iterate_incrementBits (m : ℕ) : ∀ j < 2 ^ m,
    lsbValue (incrementBits^[j] (List.replicate m false)) = j ∧
      (incrementBits^[j] (List.replicate m false)).length = m
  | 0, _ => ⟨lsbValue_replicate_false m, List.length_replicate⟩
  | j + 1, hj => by
    obtain ⟨hv, hl⟩ := iterate_incrementBits m j (by lia)
    rw [Function.iterate_succ_apply', length_incrementBits,
      lsbValue_incrementBits _ (by rw [hv, hl]; lia), hv]
    exact ⟨rfl, hl⟩

/-- Every word is reached by counting up to its value. -/
theorem iterate_incrementBits_lsbValue (u : List Bool) :
    incrementBits^[lsbValue u] (List.replicate u.length false) = u :=
  let h := iterate_incrementBits u.length (lsbValue u) (lsbValue_lt u)
  lsbValue_injective h.2 h.1

/-- Increment by a two-state transducer, the state being the carry. -/
private def incrementT : Transducer Bool Bool where
  q₀ := true
  step c b := (c && b, [b ^^ c])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private theorem incrementT_run_false (w : List Bool) : incrementT.run false w = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [Transducer.run_cons]
    change [b ^^ false] ++ incrementT.run (false && b) w = b :: w
    rw [Bool.false_and, ih, Bool.xor_false]
    rfl

private theorem incrementT_run (w : List Bool) : incrementT.run true w = incrementBits w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [Transducer.run_cons]
    change [b ^^ true] ++ incrementT.run (true && b) w = incrementBits (b :: w)
    cases b
    · rw [Bool.true_and, incrementT_run_false]
      rfl
    · rw [Bool.true_and, ih]
      rfl

/-- Binary increment is polynomial-time. -/
theorem computableTidilyInPolyTime_incrementBits :
    ComputableTidilyInPolyTime incrementBits encBits encBits :=
  .of_linear (incrementT.computableTidilyInLinearTimeAndSpace fun w => by
    rw [show incrementT.q₀ = true from rfl, incrementT_run]; rfl)

end Interaction

end Cslib.Complexity
