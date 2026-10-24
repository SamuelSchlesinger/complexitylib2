/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Foundations.Data.BitString.Counter
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Polynomial-space functions

`ComputableInPolySpace` charges both work space and encoded output to one polynomial in the
encoded input length, with no time bound. Composition and binary-counted iteration preserve
that contract; the count may be exponentially large while every encoded state stays bounded.
Finite state and alphabet choices are uniform across the inputs of each certificate.

The old raw `ComputableTidilyInPolySpace` predicate below remains an explicit staged dependency
for the central S1 internalization. Public provider operations here use the plain predicate;
proofs use one shared raw witness normalization, retaining its encoded-output bound.

## Main results

* `ComputableInPolySpace.of_polyTime`: polynomial time is within polynomial space.
* `ComputableInPolySpace.comp`, `.prod`, `.ite`: output-charged closure rules.
* `ComputableInPolySpace.iterate`: binary-counted iteration with polynomially bounded states.
* `ComputableInDegree.increment`, `ComputableInPolyTime.increment`: the binary word counter.
-/

@[expose] public section

namespace Turing.MultiTapeTM

-- Staged raw predicate: central internalization is owned by the S1 integration, not this batch.
/-- `f` is tidily computable within some time and within space polynomially bounded in the length
of the encoded input. -/
def ComputableTidilyInPolySpace {α β : Type} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) : Prop :=
  ∃ T S, PolyBounded (fun a => (encIn a).length) S ∧ ComputableTidilyInO f encIn encOut T S

private theorem rawPolySpace {α β : Type} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (h : ComputableInPolySpace f encIn encOut) :
    ComputableTidilyInPolySpace f encIn encOut := by
  obtain ⟨t, s, hs, h, hl⟩ := Internal.normalizePolySpace h
  exact ⟨t, fun a => s (encIn a).length, .of_polynomiallyBounded _ hs, 1,
    h.mono (fun _ => by simp) (fun _ => by simp), fun a => (hl a).trans (by simp)⟩

-- The existing thin witness repackaging, moved from the legacy Plain module without a new model.
private theorem plainPolySpace {α β : Type} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    (h : ComputableTidilyInPolySpace f encIn encOut) :
    ComputableInPolySpace f encIn encOut := by
  obtain ⟨T, S, ⟨b, hb, hS⟩, c, hc, hl⟩ := h
  have hcS (a : α) : c * (S a + 1) ≤ c * (b (encIn a).length + 1) :=
    Nat.mul_le_mul_left c (Nat.add_le_add_right (hS a) 1)
  exact ⟨_, fun n => c * (b n + 1), by fun_prop,
    hc.computableInTimeAndSpace.mono (fun _ => le_rfl) hcS, fun a => (hl a).trans (hcS a)⟩

attribute [fun_prop] ComputableInPolySpace

namespace ComputableInPolySpace

variable {α β : Type} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
  {γ δ : Type} {encMid : β ↪ List Bool} {encD : δ ↪ List Bool}

/-- Polynomial time is within polynomial space, charging the encoded output as well as work. -/
@[fun_prop]
theorem of_polyTime (h : ComputableInPolyTime f encIn encOut) :
    ComputableInPolySpace f encIn encOut := by
  obtain ⟨t, s, ht, hs, h⟩ := h
  exact ⟨_, fun n => s n + t n, hs.add ht,
    h.mono (fun _ => le_rfl) (fun a => Nat.le_add_right _ _),
    fun a => (h.length_le a).trans (Nat.le_add_left _ _)⟩

/-- The encoded values have polynomial length, independently of the running time. -/
theorem polyBounded_length (h : ComputableInPolySpace f encIn encOut) :
    PolyBounded (fun a => (encIn a).length) fun a => (encOut (f a)).length := by
  obtain ⟨_, s, hs, _, hl⟩ := h
  exact (PolyBounded.of_polynomiallyBounded _ hs).mono hl

/-- Composition, preserving the established canonical plain statement. -/
theorem comp {f : β → γ} {g : α → β} {encOut : γ ↪ List Bool}
    (hf : ComputableInPolySpace f encMid encOut) (hg : ComputableInPolySpace g encIn encMid) :
    ComputableInPolySpace (fun a => f (g a)) encIn encOut := by
  have hlen := hg.polyBounded_length
  obtain ⟨Tf, Sf, hSf, hf'⟩ := rawPolySpace hf
  obtain ⟨Tg, Sg, hSg, hg'⟩ := rawPolySpace hg
  exact plainPolySpace ⟨_, _, hSg.add (hSf.comp hlen), hf'.comp hg'⟩

/-- The identity. -/
@[fun_prop]
theorem id' : ComputableInPolySpace (fun a : α => a) encIn encIn :=
  of_polyTime ComputableInPolyTime.id'

/-- Pairing charges both complete encoded results. -/
@[fun_prop]
theorem prod {g : α → δ} (hf : ComputableInPolySpace f encIn encOut)
    (hg : ComputableInPolySpace g encIn encD) :
    ComputableInPolySpace (fun a => (f a, g a)) encIn (encPair encOut encD) := by
  obtain ⟨Tf, Sf, hSf, hf⟩ := rawPolySpace hf
  obtain ⟨Tg, Sg, hSg, hg⟩ := rawPolySpace hg
  exact plainPolySpace ⟨_, _, hSf.add hSg, hf.prod hg⟩

/-- A case distinction charges the guard and the selected encoded result. -/
@[fun_prop]
theorem ite {c : α → Bool} {g : α → β} (hc : ComputableInPolySpace c encIn encBool)
    (hf : ComputableInPolySpace f encIn encOut) (hg : ComputableInPolySpace g encIn encOut) :
    ComputableInPolySpace (fun a => if c a then f a else g a) encIn encOut := by
  obtain ⟨Tc, Sc, hSc, hc⟩ := rawPolySpace hc
  obtain ⟨Tf, Sf, hSf, hf⟩ := rawPolySpace hf
  obtain ⟨Tg, Sg, hSg, hg⟩ := rawPolySpace hg
  apply plainPolySpace
  refine ⟨_, _, (hSc.add (hSf.add hSg)).mono fun a => ?_, hc.ite hf hg⟩
  split_ifs <;> lia

/-- Agreement with a polynomial-space function. -/
theorem congr {f g : α → β} (h : ComputableInPolySpace f encIn encOut)
    (hfg : ∀ a, f a = g a) : ComputableInPolySpace g encIn encOut := by
  rwa [show g = f from funext fun a => (hfg a).symm]

/-- **Iteration within polynomial space**: iterating a step computable within polynomial space a
number of times computed in polynomial time in binary, from a start computable within polynomial
space, is within polynomial space when all the states along the way have polynomial length. -/
theorem iterate [Inhabited β] {n : α → ℕ} {init : α → β} {step : β → β}
    (hn : ComputableInPolyTime n encIn encNat)
    (hinit : ComputableInPolySpace init encIn encOut)
    (hstep : ComputableInPolySpace step encOut encOut) {B : α → ℕ}
    (hB : PolyBounded (fun a => (encIn a).length) B)
    (hstate : ∀ a, ∀ k ≤ n a, (encOut (step^[k] (init a))).length ≤ B a) :
    ComputableInPolySpace (fun a => step^[n a] (init a)) encIn encOut := by
  obtain ⟨dn, _, hn'⟩ := hn.exists_degree
  have hn' : ComputableInDegree _ _ _ _ _ := Internal.normalizeDegree hn'
  obtain ⟨Ti, Si, hSi, hinit⟩ := rawPolySpace hinit
  obtain ⟨Ts, Ss, hSs, hstep⟩ := rawPolySpace hstep
  obtain ⟨cs, ds, hSs⟩ := hSs.exists_le
  have hit := ComputableTidilyInO.iterate hn'.inO hinit hstep
    (R := fun a => (Finset.range (n a + 1)).sup fun k => Ts (step^[k] (init a)))
    (Q := fun a => cs * (B a + 1) ^ ds) (B := B)
    (fun a k hk => Finset.le_sup (f := fun k => Ts (step^[k] (init a)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
    (fun a k hk => (hSs _).trans (Nat.mul_le_mul_left cs
      (Nat.pow_le_pow_left (Nat.add_le_add_right (hstate a k hk) 1) ds)))
    hstate
  apply plainPolySpace
  refine ⟨_, _, ?_, hit⟩
  have hQ : PolyBounded (fun a => (encIn a).length) fun a => cs * (B a + 1) ^ ds :=
    PolyBounded.comp (size' := id) (v := fun m => cs * (m + 1) ^ ds)
      (PolyBounded.of_forall_le cs ds fun _ => le_rfl) hB
  exact ((((PolyBounded.of_forall_le (u := fun a => ((encIn a).length + 1) ^ dn) 1 dn
    fun a => by simp).add hSi).add hQ).add hB).add hn.polyBounded_length

/-- Composition, in the form consumed by `fun_prop`. -/
@[fun_prop]
theorem comp' {f : β → γ} {g : α → β} {encOut : γ ↪ List Bool}
    (hf : ComputableInPolySpace f encMid encOut) (hg : ComputableInPolySpace g encIn encMid) :
    ComputableInPolySpace (fun a => f (g a)) encIn encOut :=
  hf.comp hg

end ComputableInPolySpace

/-! ### The binary counter -/

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

private theorem incrementT_run (w : List Bool) :
    incrementT.run true w = Cslib.BitString.increment w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [Transducer.run_cons]
    change [b ^^ true] ++ incrementT.run (true && b) w = Cslib.BitString.increment (b :: w)
    cases b
    · rw [Bool.true_and, incrementT_run_false]
      rfl
    · rw [Bool.true_and, ih]
      rfl

/-- **The binary counter in linear time.** -/
theorem ComputableInDegree.increment :
    ComputableInDegree Cslib.BitString.increment encBits encBits 1 1 :=
  ComputableInDegree.of_linear
    (incrementT.computableInLinearTimeAndSpace fun w => by
    rw [show incrementT.q₀ = true from rfl, incrementT_run]; rfl)

/-- The binary counter in polynomial time. -/
@[fun_prop]
theorem ComputableInPolyTime.increment :
    ComputableInPolyTime Cslib.BitString.increment encBits encBits :=
  ComputableInDegree.increment.computableInPolyTime

end Turing.MultiTapeTM
