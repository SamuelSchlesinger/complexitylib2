/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Comp
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile
import all Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Left folds are tidily computable

If `list` and `init` are tidily computable from a common input, and `step` is tidily computable
on pairs, then `fun x => (list x).foldl step (init x)` is tidily computable, relative to encodings
of pairs, options and lists as in `Turing.MultiTapeTM.PairEncoding`,
`Turing.MultiTapeTM.OptionEncoding` and `Turing.MultiTapeTM.ListEncoding`.

The fold is computed by `Turing.MultiTapeTM.iterateWhile` on the state `some (l, b)`, holding the
rest `l` of the list and the accumulator `b`: one round replaces it by `some (l.tail, step b a)`,
where `a` is the head of `l`, or by `none` once `l` is empty. The case distinction is made by
`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.ite`.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl`: left folds are tidily computable.
-/

namespace Turing.MultiTapeTM

universe u

/-- Assemble a tidy pair from two tidy computations through the plain encoding interface.
The time and work-space budgets remain independent, up to one existential constant; only the
encoded pair is charged to the resulting space. No encoded-length premise is added to either
input computation. This raw construction theorem has no automatic registration. -/
public theorem ComputableTidilyInTimeAndSpace.pair {α β γ : Type u}
    {encIn : α ↪ List Bool} {enc₁ : β ↪ List Bool} {enc₂ : γ ↪ List Bool}
    {enc : β × γ ↪ List Bool} [PairEncoding enc₁ enc₂ enc]
    {f : α → β} {g : α → γ} {t₁ s₁ t₂ s₂ : α → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encIn enc₁ t₁ s₁)
    (hg : ComputableTidilyInTimeAndSpace g encIn enc₂ t₂ s₂) :
    ∃ c, ComputableTidilyInTimeAndSpace (fun a => (f a, g a)) encIn enc
      (fun a => c * (t₁ a + t₂ a + 1))
      (fun a => c * (s₁ a + s₂ a + (enc (f a, g a)).length + 1)) := by
  obtain ⟨c, h⟩ := PairEncoding.pair_mono (enc := enc)
    hf.computableInTimeAndSpace hg.computableInTimeAndSpace
  exact Internal.normalizeBigO ⟨c, h⟩

namespace Foldl

section BigO

variable {α β γ δ : Type*}

/-! ### Bounds up to a constant factor -/

/-- `f` is tidily computable within a constant factor of `t + 1` steps and `s + 1` cells. -/
def BigO (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (t s : α → ℕ) : Prop :=
  ∃ c, ComputableTidilyInTimeAndSpace f encIn encOut
    (fun a => c * (t a + 1)) (fun a => c * (s a + 1))

variable {f : β → δ} {g : α → β} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : δ ↪ List Bool} {t s t' s' : α → ℕ}

lemma BigO.of_computable {f : α → β} {encOut : β ↪ List Bool}
    (h : ComputableTidilyInTimeAndSpace f encIn encOut t s) : BigO f encIn encOut t s :=
  ⟨1, h.mono (fun a => by omega) (fun a => by omega)⟩

/-- Bounds can be weakened up to a constant factor. -/
lemma BigO.mono {f : α → β} {encOut : β ↪ List Bool} (h : BigO f encIn encOut t s) (c : ℕ)
    (ht : ∀ a, t a ≤ c * (t' a + 1)) (hs : ∀ a, s a ≤ c * (s' a + 1)) :
    BigO f encIn encOut t' s' := by
  obtain ⟨c₀, h₀⟩ := h
  refine ⟨c₀ * (c + 1), h₀.mono (fun a => ?_) (fun a => ?_)⟩
  · nlinarith [ht a]
  · nlinarith [hs a]

lemma BigO.length_le {f : α → β} {encOut : β ↪ List Bool} (h : BigO f encIn encOut t s) :
    ∃ c, ∀ a, (encOut (f a)).length ≤ c * (t a + 1) :=
  let ⟨c, hc⟩ := h
  ⟨c, hc.length_le⟩

/-- Composition, given a bound `m` on the length of the intermediate word. -/
lemma BigO.comp {t₂ s₂ : β → ℕ} (hf : BigO f encMid encOut t₂ s₂) (hg : BigO g encIn encMid t s)
    {m : α → ℕ} (hm : ∀ a, (encMid (g a)).length ≤ m a) :
    BigO (f ∘ g) encIn encOut (fun a => t a + t₂ (g a) + m a) (fun a => s a + s₂ (g a) + m a) := by
  obtain ⟨c₁, h₁⟩ := hg
  obtain ⟨c₂, h₂⟩ := hf
  -- vendored: crei's `comp` is `comp_linear` here, as cslib #1111 restates `comp`
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.comp_linear h₂ h₁
  refine ⟨c₁ + c₂ + c, h.mono (fun a => ?_) (fun a => ?_)⟩ <;> nlinarith [hm a]

/-- Pairing, with space for the encoded pair. -/
lemma BigO.pair {α α₁ α₂ : Type u} {encIn : α ↪ List Bool} {t s : α → ℕ}
    {enc₁ : α₁ ↪ List Bool} {enc₂ : α₂ ↪ List Bool}
    {enc : α₁ × α₂ ↪ List Bool} (hP : PairEncoding enc₁ enc₂ enc) {f₁ : α → α₁} {f₂ : α → α₂}
    (h₁ : BigO f₁ encIn enc₁ t s) (h₂ : BigO f₂ encIn enc₂ t s) :
    BigO (fun a => (f₁ a, f₂ a)) encIn enc t (fun a => s a + (enc (f₁ a, f₂ a)).length) := by
  obtain ⟨c₁, h₁⟩ := h₁
  obtain ⟨c₂, h₂⟩ := h₂
  let _ : PairEncoding enc₁ enc₂ enc := hP
  obtain ⟨c, hc⟩ := ComputableTidilyInTimeAndSpace.pair (enc := enc) h₁ h₂
  refine ⟨c * (c₁ + c₂ + 1), hc.mono (fun a => ?_) (fun a => ?_)⟩ <;>
  · ring_nf
    omega

/-- A function tidily computable in linear time and space. -/
lemma BigO.of_linear {f : α → β} {encOut : β ↪ List Bool}
    (h : ComputableInLinearTimeAndSpace f encIn encOut) :
    BigO f encIn encOut (fun a => (encIn a).length) (fun a => (encIn a).length) :=
  Internal.normalizeLinear h

end BigO

/-! ### One round of the fold -/

section Round

variable {α β : Type u} (step : β → α → β) (a₀ : α) (b₀ : β)

/-- The argument of `step` in a round: the accumulator and the head of the rest of the list. -/
def arg (o : Option (List α × β)) : β × α :=
  ((o.getD ([], b₀)).2, (o.getD ([], b₀)).1.headD a₀)

/-- The state after a round: the tail of the rest of the list, and the new accumulator. -/
def next (o : Option (List α × β)) : List α × β :=
  ((o.getD ([], b₀)).1.tail, step (arg a₀ b₀ o).1 (arg a₀ b₀ o).2)

/-- One round of the fold on the state `some (l, b)`: `some (l.tail, step b a)` for the head `a` of
`l`, or `none` if `l` is empty. Defaults `a₀` and `b₀` make it total. -/
def foldStep (o : Option (List α × β)) : Option (List α × β) :=
  if (o.getD ([], b₀)).1.isEmpty then none else some (next step a₀ b₀ o)

@[simp]
lemma foldStep_none : foldStep step a₀ b₀ none = none := by
  simp [foldStep]

@[simp]
lemma foldStep_cons (a : α) (l : List α) (b : β) :
    foldStep step a₀ b₀ (some (a :: l, b)) = some (l, step b a) := by
  simp [foldStep, next, arg]

lemma iterate_foldStep (l : List α) (b : β) {n : ℕ} (hn : n ≤ l.length) :
    (foldStep step a₀ b₀)^[n] (some (l, b)) = some (l.drop n, (l.take n).foldl step b) := by
  induction n generalizing l b with
  | zero => simp
  | succ n ih =>
    cases l with
    | nil => simp at hn
    | cons a l =>
      rw [Function.iterate_succ_apply, foldStep_cons, ih l (step b a) (by simpa using hn)]
      simp

/-- The number of rounds of the fold on a state. -/
def rounds (o : Option (List α × β)) : ℕ := o.elim 0 fun p => p.1.length

lemma isLeast_rounds {enc₁ : List α × β ↪ List Bool} {enc : Option (List α × β) ↪ List Bool}
    (h : OptionEncoding enc₁ enc) (o : Option (List α × β)) :
    IsLeast {n | enc ((foldStep step a₀ b₀)^[n + 1] o) = []} (rounds o) := by
  have hnone (x : Option (List α × β)) : enc x = [] ↔ x = none := by
    rw [← h.none_eq, enc.injective.eq_iff]
  simp only [IsLeast, lowerBounds, Set.mem_ofPred_eq, hnone]
  rcases o with _ | ⟨l, b⟩
  · exact ⟨Function.iterate_fixed (foldStep_none step a₀ b₀) _, fun _ _ => Nat.zero_le _⟩
  · refine ⟨?_, fun n hn => ?_⟩
    · rw [rounds, Option.elim_some, Function.iterate_succ_apply',
        iterate_foldStep step a₀ b₀ l b le_rfl]
      simp [foldStep]
    · by_contra hlt
      rw [iterate_foldStep step a₀ b₀ l b (by simp only [rounds, Option.elim_some] at hlt; omega)]
        at hn
      exact Option.some_ne_none _ hn

/-- The cost of a round beyond reading the state: `u` of the argument of `step` plus the length of
the next state, unless the list is empty. -/
def roundCost (encS : List α × β ↪ List Bool) (u : β × α → ℕ) (o : Option (List α × β)) : ℕ :=
  if (o.getD ([], b₀)).1.isEmpty then 0 else u (arg a₀ b₀ o) + (encS (next step a₀ b₀ o)).length

variable {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encL : List α ↪ List Bool}
  {encBA : β × α ↪ List Bool} {encS : List α × β ↪ List Bool}
  {encO : Option (List α × β) ↪ List Bool}

/-- One round costs time linear in the length of the state, plus, unless the list is empty, the
time of `step` and the length of the next state; similarly for space. -/
lemma bigO_foldStep (hLE : ListEncoding encA encL) (hBA : PairEncoding encB encA encBA)
    (hSE : PairEncoding encL encB encS) (hOE : OptionEncoding encS encO) {ts ss : β × α → ℕ}
    (hstep : ComputableTidilyInTimeAndSpace (fun p : β × α => step p.1 p.2) encBA encB ts ss) :
    BigO (foldStep step a₀ b₀) encO encO
      (fun o => (encO o).length + roundCost step a₀ b₀ encS ts o)
      (fun o => (encO o).length + roundCost step a₀ b₀ encS ss o) := by
  have hfst : ComputableInLinearTimeAndSpace _ _ _ :=
    (hSE.fst)
  have hsnd : ComputableInLinearTimeAndSpace _ _ _ :=
    (hSE.snd)
  have hsomeLinear : ComputableInLinearTimeAndSpace _ _ _ :=
    (hOE.some)
  have htailLinear : ComputableInLinearTimeAndSpace _ _ _ :=
    (hLE.tail)
  have hisEmptyLinear : ComputableInLinearTimeAndSpace _ _ _ :=
    (hLE.isEmpty)
  have hheadLinear : ComputableInLinearTimeAndSpace _ _ _ :=
    (hLE.headD a₀)
  have hgetLinear : ComputableInLinearTimeAndSpace _ _ _ :=
    (hOE.getD ([], b₀))
  -- the operations on the state, all in linear time and space
  have hlist := hfst.comp (hgetLinear)
  have htail := BigO.of_linear (htailLinear.comp hlist)
  obtain ⟨c₁, h₁⟩ := Internal.normalizeLinear (hisEmptyLinear.comp hlist)
  -- the argument of `step`, the next state, and the next state wrapped in `some`
  have harg := BigO.pair hBA (.of_linear (hsnd.comp (hgetLinear)))
    (.of_linear ((hheadLinear).comp hlist))
  obtain ⟨c, hc⟩ := harg.length_le
  have hstepArg := ((BigO.of_computable hstep).comp harg hc).mono (2 * c + 2)
    (t' := fun o => (encO o).length + ts (arg a₀ b₀ o))
    (s' := fun o => (encO o).length + ss (arg a₀ b₀ o))
    (fun o => by simp only [Function.comp_apply, arg]; ring_nf; omega)
    (fun o => by have := hc o; simp only [Function.comp_apply, arg] at *; ring_nf at *; omega)
  have hnext := BigO.pair hSE (htail.mono 1 (fun o => by omega) (fun o => by omega)) hstepArg
  have hsome := ((BigO.of_linear hsomeLinear).comp hnext
    (m := fun o => (encS (next step a₀ b₀ o)).length)
    fun o => le_rfl).mono 3
    (t' := fun o => (encO o).length + ts (arg a₀ b₀ o) + (encS (next step a₀ b₀ o)).length)
    (s' := fun o => (encO o).length + ss (arg a₀ b₀ o) + (encS (next step a₀ b₀ o)).length)
    (fun o => by simp only [Function.comp_apply, next, arg]; omega)
    (fun o => by simp only [Function.comp_apply, next, arg]; omega)
  obtain ⟨c₂, h₂⟩ := Internal.normalizeLinear
    (ComputableInLinearTimeAndSpace.const (encIn := encO) (encMid := encO)
      (none : Option (List α × β)))
  obtain ⟨c₃, h₃⟩ := hsome
  obtain ⟨k, hk⟩ := ComputableTidilyInTimeAndSpace.ite h₁ (h₂.restrict _) (h₃.restrict _)
  refine ⟨c₁ + c₂ + c₃ + k, hk.mono (fun o => ?_) (fun o => ?_)⟩ <;>
  · cases h : (o.getD ([], b₀)).1.isEmpty <;>
      simp only [Function.comp_apply, roundCost, h, Bool.false_eq_true, ↓reduceIte] <;>
      ring_nf <;> omega

end Round

end Foldl

/-! ### Left folds -/

open Foldl in
/-- If `list` and `init` are tidily computable from a common input and `step` is tidily computable
on pairs, then `fun x => (list x).foldl step (init x)` is tidily computable. Each of the
`(list x).length` steps is bounded by `tMax x` steps and `sMax x` cells, and the encodings of the
intermediate states `((list x).drop i, ((list x).take i).foldl step (init x))` by `lMax x`. -/
public theorem ComputableTidilyInTimeAndSpace.foldl {γ α β : Type u} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encL : List α ↪ List Bool}
    {encBA : β × α ↪ List Bool} {encS : List α × β ↪ List Bool}
    {encO : Option (List α × β) ↪ List Bool}
    [hLE : ListEncoding encA encL] [hBA : PairEncoding encB encA encBA]
    [hSE : PairEncoding encL encB encS] [hOE : OptionEncoding encS encO]
    {list : γ → List α} {init : γ → β} {step : β → α → β}
    {t s : γ → ℕ} {tStep sStep : β × α → ℕ} {tMax sMax lMax : γ → ℕ}
    (hlist : ComputableTidilyInTimeAndSpace list encIn encL t s)
    (hinit : ComputableTidilyInTimeAndSpace init encIn encB t s)
    (hstep : ComputableTidilyInTimeAndSpace (fun p : β × α => step p.1 p.2) encBA encB tStep sStep)
    (htMax : ∀ x i (hi : i < (list x).length),
      tStep (((list x).take i).foldl step (init x), (list x)[i]) ≤ tMax x)
    (hsMax : ∀ x i (hi : i < (list x).length),
      sStep (((list x).take i).foldl step (init x), (list x)[i]) ≤ sMax x)
    (hlMax : ∀ x, ∀ i ≤ (list x).length,
      (encS ((list x).drop i, ((list x).take i).foldl step (init x))).length ≤ lMax x) :
    ∃ c, ComputableTidilyInTimeAndSpace (fun x => (list x).foldl step (init x)) encIn encB
      (fun x => c * (t x + ((list x).length + 1) * (tMax x + lMax x + 1)))
      (fun x => c * (s x + sMax x + lMax x + 1)) := by
  rcases isEmpty_or_nonempty γ with hγ | ⟨⟨x₀⟩⟩
  · exact ⟨0, 0, _, inferInstance, tidyCopy Bool, isEmptyElim⟩
  rcases isEmpty_or_nonempty α with hα | ⟨⟨a₀⟩⟩
  · -- every list is empty, so the fold is `init`
    have heq : (fun x => (list x).foldl step (init x)) = init := funext fun x => by
      rw [Subsingleton.elim (list x) [], List.foldl_nil]
    rw [heq]
    exact ⟨1, hinit.mono (fun x => by omega) (fun x => by omega)⟩
  -- one round, and the loop
  obtain ⟨cF, hF⟩ := bigO_foldStep step a₀ (init x₀) hLE hBA hSE hOE hstep
  obtain ⟨ci, hiter⟩ := hF.iterateWhile (r := rounds) (isLeast_rounds step a₀ (init x₀) hOE)
  -- the largest cost of a step and the longest state along the run from a state
  set g := foldStep step a₀ (init x₀)
  obtain ⟨tAlong, htAlong⟩ : ∃ tAlong : Option (List α × β) → ℕ, ∀ o,
      tAlong o = (Finset.Iic (rounds o)).sup
      fun n => roundCost step a₀ (init x₀) encS tStep (g^[n] o) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨sAlong, hsAlong⟩ : ∃ sAlong : Option (List α × β) → ℕ, ∀ o,
      sAlong o = (Finset.Iic (rounds o)).sup
      fun n => roundCost step a₀ (init x₀) encS sStep (g^[n] o) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨lAlong, hlAlong⟩ : ∃ lAlong : Option (List α × β) → ℕ, ∀ o,
      lAlong o = (Finset.Iic (rounds o)).sup fun n => (encO (g^[n] o)).length := ⟨_, fun _ => rfl⟩
  have hloop := hiter.mono (t' := fun o => (cF + ci) * ((rounds o + 1) * (tAlong o + lAlong o + 1)))
    (s' := fun o => (ci * (cF + 1) + 1) * (sAlong o + lAlong o + 1)) (fun o => ?_) (fun o => ?_)
  rotate_left
  · have hsup := Nat.mul_le_mul_left (rounds o + 1) (Nat.add_le_add
      (Finset.sup_le (s := Finset.Iic (rounds o)) (a := cF * (lAlong o + tAlong o + 1)) fun n hn =>
        Nat.mul_le_mul_left cF (Nat.add_le_add_right (Nat.add_le_add
          (hlAlong o ▸ Finset.le_sup (f := fun n => (encO (g^[n] o)).length) hn)
          (htAlong o ▸ Finset.le_sup
            (f := fun n => roundCost step a₀ (init x₀) encS tStep (g^[n] o)) hn)) 1))
      (Nat.mul_le_mul_left ci (Nat.add_le_add_right (hlAlong o).ge 1)))
    ring_nf at hsup ⊢
    omega
  · have hsup := Nat.add_le_add (Finset.sup_le (s := Finset.Iic (rounds o))
        (a := cF * (lAlong o + sAlong o + 1)) fun n hn =>
        Nat.mul_le_mul_left cF (Nat.add_le_add_right (Nat.add_le_add
          (hlAlong o ▸ Finset.le_sup (f := fun n => (encO (g^[n] o)).length) hn)
          (hsAlong o ▸ Finset.le_sup
            (f := fun n => roundCost step a₀ (init x₀) encS sStep (g^[n] o)) hn)) 1))
      (hlAlong o).ge
    have := Nat.mul_le_mul_left ci (Nat.add_le_add_right hsup 1)
    ring_nf at this ⊢
    omega
  have hsomeLinear : ComputableInLinearTimeAndSpace _ _ _ :=
    hOE.some
  have hsnd : ComputableInLinearTimeAndSpace _ _ _ :=
    hSE.snd
  have hgetInitLinear : ComputableInLinearTimeAndSpace _ _ _ :=
    (hOE.getD ([], init x₀))
  -- the initial state
  have hstart := (BigO.of_linear hsomeLinear).comp
    (BigO.pair hSE (.of_computable hlist) (.of_computable hinit)) (m := lMax)
    (fun x => by simpa using hlMax x 0 (Nat.zero_le _))
  obtain ⟨cs, hcs⟩ := (BigO.of_linear hsomeLinear).length_le
  have hrun := (BigO.of_computable hloop).comp hstart (m := fun x => cs * (lMax x + 1))
    (fun x => (hcs _).trans (Nat.mul_le_mul_left cs (by simpa using hlMax x 0 (Nat.zero_le _))))
  -- the final state, and its accumulator
  have hfinal (x : γ) : g^[rounds (some (list x, init x))]
      (some (list x, init x)) = some ([], (list x).foldl step (init x)) := by
    rw [rounds, Option.elim_some, iterate_foldStep step a₀ (init x₀) _ _ le_rfl]
    simp
  have hall := (BigO.of_linear (hsnd.comp (hgetInitLinear))).comp hrun
    (m := fun x => cs * (lMax x + 1)) (fun x => by
      simp only [Function.comp_apply, hfinal]
      exact (hcs _).trans (Nat.mul_le_mul_left cs (by simpa using hlMax x _ le_rfl)))
  have heq : (Prod.snd ∘ fun o => o.getD ([], init x₀)) ∘
      ((fun o => g^[rounds o] o) ∘
        (some ∘ fun x => (list x, init x))) = fun x => (list x).foldl step (init x) := by
    funext x
    simp [hfinal]
  rw [heq] at hall
  -- the run from the initial state
  have hrounds (x : γ) : rounds (some (list x, init x)) = (list x).length := rfl
  have hstate (x : γ) {i : ℕ} (hi : i ≤ (list x).length) : g^[i] (some (list x, init x)) =
      some ((list x).drop i, ((list x).take i).foldl step (init x)) :=
    iterate_foldStep step a₀ (init x₀) _ _ hi
  have hstep_le (x : γ) {u : β × α → ℕ} {U : ℕ}
      (hu : ∀ i (hi : i < (list x).length),
        u (((list x).take i).foldl step (init x), (list x)[i]) ≤ U)
      {i : ℕ} (hi : i ≤ (list x).length) :
      roundCost step a₀ (init x₀) encS u (g^[i] (some (list x, init x))) ≤ U + lMax x := by
    rw [roundCost, hstate x hi, Option.getD_some]
    split_ifs with h
    · exact Nat.zero_le _
    · have hi' : i < (list x).length := by
        by_contra hc
        simp [List.drop_eq_nil_of_le (by omega : (list x).length ≤ i)] at h
      have hdrop := List.drop_eq_getElem_cons hi'
      refine Nat.add_le_add ?_ ?_
      · simp only [arg, Option.getD_some, hdrop, List.headD_cons]
        exact hu i hi'
      · have := hlMax x (i + 1) hi'
        simp only [next, arg, Option.getD_some, hdrop, List.tail_cons, List.headD_cons]
        rwa [List.take_succ_eq_append_getElem hi', List.foldl_append, List.foldl_cons,
          List.foldl_nil] at this
  have htx (x : γ) : tAlong (some (list x, init x)) ≤ tMax x + lMax x := by
    rw [htAlong]
    exact Finset.sup_le fun i hi => hstep_le x (htMax x) (by rwa [Finset.mem_Iic, hrounds] at hi)
  have hsx (x : γ) : sAlong (some (list x, init x)) ≤ sMax x + lMax x := by
    rw [hsAlong]
    exact Finset.sup_le fun i hi => hstep_le x (hsMax x) (by rwa [Finset.mem_Iic, hrounds] at hi)
  have hlen (x : γ) {i : ℕ} (hi : i ≤ (list x).length) :
      (encO (g^[i] (some (list x, init x)))).length ≤ cs * (lMax x + 1) := by
    rw [hstate x hi]
    exact (hcs _).trans (Nat.mul_le_mul_left cs (Nat.add_le_add_right (hlMax x i hi) 1))
  have hlx (x : γ) : lAlong (some (list x, init x)) ≤ cs * (lMax x + 1) := by
    rw [hlAlong]
    exact Finset.sup_le fun i hi => hlen x (by rwa [Finset.mem_Iic, hrounds] at hi)
  have hm (x : γ) : lMax x + 1 ≤ ((list x).length + 1) * (tMax x + lMax x + 1) :=
    (show lMax x + 1 ≤ tMax x + lMax x + 1 by omega).trans (Nat.le_mul_of_pos_left _ (by omega))
  -- collect the bounds
  obtain ⟨c, hc⟩ := hall
  refine ⟨c * ((cF + ci) * (cs + 1) + (ci * (cF + 1) + 1) * (cs + 1) + 5 * cs + 5),
    hc.mono (fun x => ?_) (fun x => ?_)⟩
  · simp only [Function.comp_apply, hrounds]
    have h₁ : (cF + ci) * (((list x).length + 1) *
        (tAlong (some (list x, init x)) + lAlong (some (list x, init x)) + 1)) ≤
        (cF + ci) * (cs + 1) * (((list x).length + 1) * (tMax x + lMax x + 1)) := by
      rw [Nat.mul_assoc, Nat.mul_left_comm (cs + 1)]
      refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ?_)
      have := htx x
      have := hlx x
      ring_nf at *
      omega
    have h₂ : (encS (list x, init x)).length ≤ lMax x := by simpa using hlMax x 0 (Nat.zero_le _)
    have h₃ := hlen x (le_refl (list x).length)
    have h₄ := Nat.mul_le_mul_left cs (hm x)
    have h₆ := hm x
    generalize ((list x).length + 1) * (tMax x + lMax x + 1) = m at *
    generalize (cF + ci) * (((list x).length + 1) *
      (tAlong (some (list x, init x)) + lAlong (some (list x, init x)) + 1)) = q at *
    have key : t x + (encS (list x, init x)).length + lMax x + q +
        cs * (lMax x + 1) + (encO (g^[(list x).length] (some (list x, init x)))).length +
        cs * (lMax x + 1) + 1 ≤
        ((cF + ci) * (cs + 1) + (ci * (cF + 1) + 1) * (cs + 1) + 5 * cs + 5) *
          (t x + m) := by
      ring_nf at *
      omega
    have := Nat.mul_le_mul_left c key
    ring_nf at this ⊢
    omega
  · simp only [Function.comp_apply, hrounds]
    have h₁ : (ci * (cF + 1) + 1) *
        (sAlong (some (list x, init x)) + lAlong (some (list x, init x)) + 1) ≤
        (ci * (cF + 1) + 1) * ((cs + 1) * (sMax x + lMax x + 1)) := by
      refine Nat.mul_le_mul_left _ ?_
      have := hsx x
      have := hlx x
      ring_nf at *
      omega
    have h₂ : (encS (list x, init x)).length ≤ lMax x := by simpa using hlMax x 0 (Nat.zero_le _)
    have h₃ := hlen x (le_refl (list x).length)
    generalize (ci * (cF + 1) + 1) *
      (sAlong (some (list x, init x)) + lAlong (some (list x, init x)) + 1) = q at *
    have key : s x + (encS (list x, init x)).length + (encS (list x, init x)).length + lMax x +
        q + cs * (lMax x + 1) +
        ((encO (g^[(list x).length] (some (list x, init x)))).length +
          (encO (g^[(list x).length] (some (list x, init x)))).length) + cs * (lMax x + 1) + 1 ≤
        ((cF + ci) * (cs + 1) + (ci * (cF + 1) + 1) * (cs + 1) + 5 * cs + 5) *
          (s x + sMax x + lMax x + 1) := by
      ring_nf at *
      omega
    have := Nat.mul_le_mul_left c key
    ring_nf at this ⊢
    omega

end Turing.MultiTapeTM
