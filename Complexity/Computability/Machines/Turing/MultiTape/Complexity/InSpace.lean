/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith

/-!
# Computability within a space bound

`ComputableInSpace f encIn encOut S` says that `f` is computable within space `O(S)`,
with values of length `O(S)`, in some time. For space-bounded algorithms only the work space
matters, and this calculus tracks it alone: composition, pairs, conditionals and loops keep the
work space explicit and leave the time to be whatever it is. In loops, the time of a round is the
largest over the rounds actually run.

## Main definitions

* `Turing.MultiTapeTM.ComputableInSpace`: computability within a space bound.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.exists_inO`: expose an unspecified time bound.
* `Turing.MultiTapeTM.ComputableInSpace.comp`, `.prod`, `.ite`: closure properties.
* `Turing.MultiTapeTM.ComputableInSpace.iterate`, `.foldl`: loops.
-/

@[expose] public section

namespace Turing.MultiTapeTM



namespace ComputableInSpace

variable {α β γ δ : Type} {encIn : α ↪ List Bool} {encB : β ↪ List Bool}
  {encC : γ ↪ List Bool} {encD : δ ↪ List Bool} {S S₁ S₂ : α → ℕ}

/-- Recover a time bound for one existing plain realization. Enlarging the shared constant
changes no space budget or output requirement; the time remains unrestricted. -/
theorem exists_inO {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {S : α → ℕ}
    (h : ComputableInSpace f encIn encOut S) : ∃ T, ComputableInO f encIn encOut T S := by
  obtain ⟨t, c, h, hl⟩ := h
  refine ⟨t, c + 1, h.mono (fun a => ?_) (fun a => ?_), fun a => (hl a).trans ?_⟩
  · nlinarith [Nat.zero_le (c * t a)]
  · exact Nat.mul_le_mul_right _ (Nat.le_succ c)
  · exact Nat.mul_le_mul_right _ (Nat.le_succ c)

theorem of_inO {f : α → β} {T : α → ℕ} (h : ComputableInO f encIn encB T S) :
    ComputableInSpace f encIn encB S :=
  let ⟨c, hc, hl⟩ := h
  ⟨_, c, hc, hl⟩

theorem weaken {f : α → β} (h : ComputableInSpace f encIn encB S) (hS : S ≼ S₁) :
    ComputableInSpace f encIn encB S₁ := by
  obtain ⟨_, hT⟩ := exists_inO h
  exact of_inO (hT.weaken (.refl _) hS)

theorem mono_le {f : α → β} (h : ComputableInSpace f encIn encB S)
    (hS : ∀ a, S a ≤ S₁ a) : ComputableInSpace f encIn encB S₁ :=
  h.weaken (.of_le hS)

theorem length_le {f : α → β} (h : ComputableInSpace f encIn encB S) :
    (fun a => (encB (f a)).length) ≼ S :=
  let ⟨_, c, _, hl⟩ := h
  ⟨c, hl⟩

theorem of_enc_eq {f : α → β} {g : α → γ} (h : ComputableInSpace f encIn encB S)
    (he : ∀ a, encC (g a) = encB (f a)) : ComputableInSpace g encIn encC S := by
  obtain ⟨_, hT⟩ := exists_inO h
  exact of_inO (hT.of_enc_eq he)

theorem of_encIn_eq {α' : Type} {encIn' : α' ↪ List Bool} {f : α → β} (e : α' → α)
    (h : ComputableInSpace f encIn encB S) (he : ∀ a, encIn' a = encIn (e a)) :
    ComputableInSpace (fun a => f (e a)) encIn' encB fun a => S (e a) := by
  obtain ⟨_, hT⟩ := exists_inO h
  exact of_inO (hT.of_encIn_eq e he)

theorem comp {f : α → β} {g : β → γ} {S₂ : β → ℕ} (hg : ComputableInSpace g encB encC S₂)
    (hf : ComputableInSpace f encIn encB S₁) :
    ComputableInSpace (fun a => g (f a)) encIn encC fun a => S₁ a + S₂ (f a) := by
  obtain ⟨_, hg⟩ := exists_inO hg
  obtain ⟨_, hf⟩ := exists_inO hf
  exact of_inO (hg.comp hf)

theorem prod {f : α → β} {g : α → γ} (hf : ComputableInSpace f encIn encB S₁)
    (hg : ComputableInSpace g encIn encC S₂) :
    ComputableInSpace (fun a => (f a, g a)) encIn (encPair encB encC)
      fun a => S₁ a + S₂ a := by
  obtain ⟨_, hf⟩ := exists_inO hf
  obtain ⟨_, hg⟩ := exists_inO hg
  exact of_inO (hf.prod hg)

theorem append {f₁ : α → β} {f₂ : α → γ} {g : α → δ} {encD : δ ↪ List Bool}
    (h₁ : ComputableInSpace f₁ encIn encB S₁) (h₂ : ComputableInSpace f₂ encIn encC S₂)
    (hg : ∀ x, encD (g x) = encB (f₁ x) ++ encC (f₂ x)) :
    ComputableInSpace g encIn encD fun x => S₁ x + S₂ x := by
  obtain ⟨_, h₁⟩ := exists_inO h₁
  obtain ⟨_, h₂⟩ := exists_inO h₂
  exact of_inO (h₁.append h₂ hg)

theorem ite {c : α → Bool} {f g : α → β} {Sc : α → ℕ}
    (hc : ComputableInSpace c encIn encBool Sc) (hf : ComputableInSpace f encIn encB S₁)
    (hg : ComputableInSpace g encIn encB S₂) :
    ComputableInSpace (fun a => if c a then f a else g a) encIn encB
      fun a => Sc a + if c a then S₁ a else S₂ a := by
  obtain ⟨_, hc⟩ := exists_inO hc
  obtain ⟨_, hf⟩ := exists_inO hf
  obtain ⟨_, hg⟩ := exists_inO hg
  exact of_inO (hc.ite hf hg)

theorem const (b : β) :
    ComputableInSpace (fun _ : α => b) encIn encB fun a => (encIn a).length :=
  of_inO (ComputableInO.const b)

theorem fst (enc₁ : β ↪ List Bool) (enc₂ : γ ↪ List Bool) :
    ComputableInSpace Prod.fst (encPair enc₁ enc₂) enc₁
      fun p => (encPair enc₁ enc₂ p).length :=
  of_inO (ComputableInO.fst enc₁ enc₂)

theorem snd (enc₁ : β ↪ List Bool) (enc₂ : γ ↪ List Bool) :
    ComputableInSpace Prod.snd (encPair enc₁ enc₂) enc₂
      fun p => (encPair enc₁ enc₂ p).length :=
  of_inO (ComputableInO.snd enc₁ enc₂)

theorem fst' {f : α → β × γ} (h : ComputableInSpace f encIn (encPair encB encC) S) :
    ComputableInSpace (fun a => (f a).1) encIn encB S := by
  obtain ⟨_, h⟩ := exists_inO h
  exact of_inO (ComputableInO.fst' h)

theorem snd' {f : α → β × γ} (h : ComputableInSpace f encIn (encPair encB encC) S) :
    ComputableInSpace (fun a => (f a).2) encIn encC S := by
  obtain ⟨_, h⟩ := exists_inO h
  exact of_inO (ComputableInO.snd' h)

theorem of_finite [Finite α] (f : α → β) :
    ComputableInSpace f encIn encB fun a => (encIn a).length :=
  of_inO (ComputableInDegree.of_finite f).inO_one

/-- **Iterating a step a computed number of times**, within the space of the counter, of the
initial state, of a round and of the states. -/
theorem iterate [Inhabited β] {n : α → ℕ} {init : α → β} {step : β → β} {Sn Si Q B : α → ℕ}
    {Ss : β → ℕ} (hn : ComputableInSpace n encIn encNat Sn)
    (hinit : ComputableInSpace init encIn encB Si)
    (hstep : ComputableInSpace step encB encB Ss)
    (hspace : ∀ x, ∀ k ≤ n x, Ss (step^[k] (init x)) ≤ Q x)
    (hstate : ∀ x, ∀ k ≤ n x, (encB (step^[k] (init x))).length ≤ B x) :
    ComputableInSpace (fun x => step^[n x] (init x)) encIn encB
      fun x => Sn x + Si x + Q x + B x + (encNat (n x)).length := by
  obtain ⟨_, hn⟩ := exists_inO hn
  obtain ⟨_, hinit⟩ := exists_inO hinit
  obtain ⟨Ts, hstep⟩ := exists_inO hstep
  exact of_inO (ComputableInO.iterate hn hinit hstep
    (R := fun x => listMax (fun k => Ts (step^[k] (init x))) (List.range (n x + 1)))
    (fun x k hk => le_listMax (f := fun k => Ts (step^[k] (init x)))
      (List.mem_range.mpr (Nat.lt_succ_of_le hk))) hspace hstate)

/-- **Left folds**, within the space of the list, of the initial state, of a round and of the
states. -/
theorem foldl {encA : δ ↪ List Bool} {encL : List δ ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] {list : α → List δ} {init : α → β} {step : β → δ → β}
    {Sl Si Q B : α → ℕ} {Ss : β × δ → ℕ}
    (hlist : ComputableInSpace list encIn encL Sl)
    (hinit : ComputableInSpace init encIn encB Si)
    (hstep : ComputableInSpace (fun p : β × δ => step p.1 p.2) (encPair encB encA) encB Ss)
    (hspace : ∀ x i (hi : i < (list x).length),
      Ss (((list x).take i).foldl step (init x), (list x)[i]) ≤ Q x)
    (hstate : ∀ x, ∀ i ≤ (list x).length,
      (encB (((list x).take i).foldl step (init x))).length ≤ B x) :
    ComputableInSpace (fun x => (list x).foldl step (init x)) encIn encB
      fun x => Sl x + Si x + Q x + B x + (encL (list x)).length := by
  obtain ⟨_, hlist⟩ := exists_inO hlist
  obtain ⟨_, hinit⟩ := exists_inO hinit
  obtain ⟨Ts, hstep⟩ := exists_inO hstep
  exact of_inO (ComputableInO.foldl hlist hinit hstep
    (R := fun x => listMax (fun i => ((list x)[i]?).elim 0 fun a =>
      Ts (((list x).take i).foldl step (init x), a)) (List.range (list x).length))
    (fun x i hi => by
      have := le_listMax (f := fun i => ((list x)[i]?).elim 0 fun a =>
        Ts (((list x).take i).foldl step (init x), a)) (List.mem_range.mpr hi)
      simpa [List.getElem?_eq_getElem hi] using this) hspace hstate)

end ComputableInSpace



end Turing.MultiTapeTM
