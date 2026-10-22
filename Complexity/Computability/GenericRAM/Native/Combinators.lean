/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Native
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum

/-!
# Compositional combinators for native resource certificates

These combinators assemble `NativeCertificate` witnesses for tuples, branches, retained-input
option elimination, and sum tags while tracking arbitrary input-dependent time and space bounds.
Linear postprocessing is absorbed into the producer's bounds via its output-length guarantee;
no polynomiality assumption or `ofPolyTime` selection is used.

## Main definitions

* `NativeCertificate.linear`, `.const`, `.prod`, `.post`: basic linear, literal, pair, and
  postprocessing combinators.
* `NativeCertificate.branch`, `.option`: selected-branch conditional and retained-input option
  elimination.
* `NativeCertificate.fst`, `.snd`, `.some`, `.inl`, `.inr`, `.congr`, `.pull`, `.payload`:
  projections, constructors, and retained-input helpers.

## References

Uses Christian Reitwiessner's native machine calculus and the parameterized option/sum resource
lemmas.
-/

@[expose] public section

namespace Cslib.GenericRAM.NativeCertificate

open Turing.MultiTapeTM

variable {α β γ δ : Type} {ei : α ↪ List Bool} {em : β ↪ List Bool}
  {eo : γ ↪ List Bool} {ed : δ ↪ List Bool} {f : α → β} {g : α → γ}

@[simp] theorem comp_time {g : β → γ} (d : NativeCertificate g em eo)
    (c : NativeCertificate f ei em) (a : α) :
    (d.comp c).time a = c.time a + d.time (f a) := rfl

@[simp] theorem comp_space {g : β → γ} (d : NativeCertificate g em eo)
    (c : NativeCertificate f ei em) (a : α) :
    (d.comp c).space a = c.space a + d.space (f a) := rfl

/-- Package a native linear-time/space implementation with its explicit input-length bound. -/
def linear (h : ComputableTidilyInO f ei em
    (fun a => (ei a).length) (fun a => (ei a).length)) : NativeCertificate f ei em :=
  ⟨fun a => (ei a).length, fun a => (ei a).length, h⟩

@[simp] theorem linear_time (h : ComputableTidilyInO f ei em
    (fun a => (ei a).length) (fun a => (ei a).length)) (a : α) :
    (linear h).time a = (ei a).length := rfl

@[simp] theorem linear_space (h : ComputableTidilyInO f ei em
    (fun a => (ei a).length) (fun a => (ei a).length)) (a : α) :
    (linear h).space a = (ei a).length := rfl

/-- A fixed literal, charged by the full input length. -/
def const (b : β) : NativeCertificate (fun _ : α => b) ei em :=
  linear (ComputableTidilyInO.const b)

@[simp] theorem const_time (b : β) (a : α) :
    (const (ei := ei) (em := em) b).time a = (ei a).length := rfl

@[simp] theorem const_space (b : β) (a : α) :
    (const (ei := ei) (em := em) b).space a = (ei a).length := rfl

/-- Construct a framed pair, adding the two producer bounds. -/
def prod (c : NativeCertificate f ei em) (d : NativeCertificate g ei eo) :
    NativeCertificate (fun a => (f a, g a)) ei (encPair em eo) :=
  ⟨fun a => c.time a + d.time a, fun a => c.space a + d.space a,
    c.computes.prod d.computes⟩

@[simp] theorem prod_time (c : NativeCertificate f ei em) (d : NativeCertificate g ei eo) (a : α) :
    (prod c d).time a = c.time a + d.time a := rfl

@[simp] theorem prod_space (c : NativeCertificate f ei em) (d : NativeCertificate g ei eo) (a : α) :
    (prod c d).space a = c.space a + d.space a := rfl

/-- Linear postprocessing is absorbed using the producer output-length guarantee. -/
def post {g : β → γ} (c : NativeCertificate f ei em)
    (h : ComputableTidilyInO g em eo
      (fun b => (em b).length) (fun b => (em b).length)) :
    NativeCertificate (g ∘ f) ei eo :=
  ⟨c.time, c.space, h.comp_linear c.computes⟩

@[simp] theorem post_time {g : β → γ} (c : NativeCertificate f ei em)
    (h : ComputableTidilyInO g em eo
      (fun b => (em b).length) (fun b => (em b).length)) :
    (post c h).time = c.time := rfl

@[simp] theorem post_space {g : β → γ} (c : NativeCertificate f ei em)
    (h : ComputableTidilyInO g em eo
      (fun b => (em b).length) (fun b => (em b).length)) :
    (post c h).space = c.space := rfl

/-- Charge the Boolean test and only the selected branch. -/
def branch {condition : α → Bool} {f g : α → β}
    (test : NativeCertificate condition ei encBool)
    (yes : NativeCertificate f ei em) (no : NativeCertificate g ei em) :
    NativeCertificate (fun a => if condition a then f a else g a) ei em :=
  ⟨fun a => test.time a + if condition a then yes.time a else no.time a,
    fun a => test.space a + if condition a then yes.space a else no.space a,
    test.computes.ite yes.computes no.computes⟩

@[simp] theorem branch_time {condition : α → Bool} {f g : α → β}
    (test : NativeCertificate condition ei encBool)
    (yes : NativeCertificate f ei em) (no : NativeCertificate g ei em) (a : α) :
    (branch test yes no).time a =
      test.time a + if condition a then yes.time a else no.time a := rfl

@[simp] theorem branch_space {condition : α → Bool} {f g : α → β}
    (test : NativeCertificate condition ei encBool)
    (yes : NativeCertificate f ei em) (no : NativeCertificate g ei em) (a : α) :
    (branch test yes no).space a =
      test.space a + if condition a then yes.space a else no.space a := rfl

/-- Retain the original input across option elimination; charge duplication and selected branch. -/
def option {value : α → Option β} {fallback : α → γ} {body : α × β → γ}
    (c : NativeCertificate value ei (encOption em))
    (no : NativeCertificate fallback ei eo)
    (yes : NativeCertificate body (encPair ei em) eo) :
    NativeCertificate (fun a => (value a).elim (fallback a) (fun b => body (a, b))) ei eo :=
  ⟨fun a => 2 * c.time a + (ei a).length +
      (value a).elim (no.time a) (fun b => yes.time (a, b)),
    fun a => 2 * c.space a + (ei a).length +
      (value a).elim (no.space a) (fun b => yes.space (a, b)),
    ComputableTidilyInO.optionElimWithInput (body := fun a b => body (a, b))
      c.computes no.computes yes.computes⟩

@[simp] theorem option_time {value : α → Option β} {fallback : α → γ} {body : α × β → γ}
    (c : NativeCertificate value ei (encOption em))
    (no : NativeCertificate fallback ei eo)
    (yes : NativeCertificate body (encPair ei em) eo) (a : α) :
    (option c no yes).time a = 2 * c.time a + (ei a).length +
      (value a).elim (no.time a) (fun b => yes.time (a, b)) := rfl

@[simp] theorem option_space {value : α → Option β} {fallback : α → γ} {body : α × β → γ}
    (c : NativeCertificate value ei (encOption em))
    (no : NativeCertificate fallback ei eo)
    (yes : NativeCertificate body (encPair ei em) eo) (a : α) :
    (option c no yes).space a = 2 * c.space a + (ei a).length +
      (value a).elim (no.space a) (fun b => yes.space (a, b)) := rfl

/-- Project the first field, absorbing linear work in the producer bounds. -/
def fst {f : α → β × γ} (c : NativeCertificate f ei (encPair em eo)) :
    NativeCertificate (fun a => (f a).1) ei em :=
  post c (ComputableTidilyInO.fst em eo)

@[simp] theorem fst_time {f : α → β × γ} (c : NativeCertificate f ei (encPair em eo)) :
    (fst c).time = c.time := rfl

@[simp] theorem fst_space {f : α → β × γ} (c : NativeCertificate f ei (encPair em eo)) :
    (fst c).space = c.space := rfl

/-- Project the second field, absorbing linear work in the producer bounds. -/
def snd {f : α → β × γ} (c : NativeCertificate f ei (encPair em eo)) :
    NativeCertificate (fun a => (f a).2) ei eo :=
  post c (ComputableTidilyInO.snd em eo)

@[simp] theorem snd_time {f : α → β × γ} (c : NativeCertificate f ei (encPair em eo)) :
    (snd c).time = c.time := rfl

@[simp] theorem snd_space {f : α → β × γ} (c : NativeCertificate f ei (encPair em eo)) :
    (snd c).space = c.space := rfl

/-- Add an option tag, absorbing linear work in the producer bounds. -/
def some (c : NativeCertificate f ei em) :
    NativeCertificate (fun a => Option.some (f a)) ei (encOption em) :=
  post c ComputableTidilyInDegree.optionSome.inO_one

@[simp] theorem some_time (c : NativeCertificate f ei em) :
    (some c).time = c.time := rfl

@[simp] theorem some_space (c : NativeCertificate f ei em) :
    (some c).space = c.space := rfl

/-- Add a left sum tag, absorbing linear work in the producer bounds. -/
def inl (c : NativeCertificate f ei em) (right : γ ↪ List Bool) :
    NativeCertificate (fun a => Sum.inl (f a)) ei (encSum em right) :=
  post c (ComputableTidilyInO.inl em right)

@[simp] theorem inl_time (c : NativeCertificate f ei em) (right : γ ↪ List Bool) :
    (inl c right).time = c.time := rfl

@[simp] theorem inl_space (c : NativeCertificate f ei em) (right : γ ↪ List Bool) :
    (inl c right).space = c.space := rfl

/-- Add a right sum tag, absorbing linear work in the producer bounds. -/
def inr (left : γ ↪ List Bool) (c : NativeCertificate f ei em) :
    NativeCertificate (fun a => Sum.inr (f a)) ei (encSum left em) :=
  post c (ComputableTidilyInO.inr left em)

@[simp] theorem inr_time (left : γ ↪ List Bool) (c : NativeCertificate f ei em) :
    (inr left c).time = c.time := rfl

@[simp] theorem inr_space (left : γ ↪ List Bool) (c : NativeCertificate f ei em) :
    (inr left c).space = c.space := rfl

/-- Transport along pointwise equality without changing bounds. -/
def congr {g : α → β} (c : NativeCertificate f ei em) (h : ∀ a, f a = g a) :
    NativeCertificate g ei em :=
  ⟨c.time, c.space, c.computes.of_enc_eq (fun a => congrArg em (h a).symm)⟩

@[simp] theorem congr_time {g : α → β} (c : NativeCertificate f ei em) (h : ∀ a, f a = g a) :
    (congr c h).time = c.time := rfl

@[simp] theorem congr_space {g : α → β} (c : NativeCertificate f ei em) (h : ∀ a, f a = g a) :
    (congr c h).space = c.space := rfl

/-- Retain a producer on the first component of an extended input. -/
def pull (c : NativeCertificate f ei em) (other : δ ↪ List Bool) :
    NativeCertificate (fun a : α × δ => f a.1) (encPair ei other) em :=
  c.comp (linear (ComputableTidilyInO.fst ei other))

@[simp] theorem pull_time (c : NativeCertificate f ei em) (other : δ ↪ List Bool) (a : α × δ) :
    (pull c other).time a = (encPair ei other a).length + c.time a.1 := rfl

@[simp] theorem pull_space (c : NativeCertificate f ei em) (other : δ ↪ List Bool) (a : α × δ) :
    (pull c other).space a = (encPair ei other a).length + c.space a.1 := rfl

/-- Extract a retained-input continuation payload in linear time and space. -/
def payload (input : α ↪ List Bool) (out : β ↪ List Bool) :
    NativeCertificate (fun a : α × β => a.2) (encPair input out) out :=
  linear (ComputableTidilyInO.snd input out)

@[simp] theorem payload_time (input : α ↪ List Bool) (out : β ↪ List Bool) (a : α × β) :
    (payload input out).time a = (encPair input out a).length := rfl

@[simp] theorem payload_space (input : α ↪ List Bool) (out : β ↪ List Bool) (a : α × β) :
    (payload input out).space a = (encPair input out a).length := rfl

end Cslib.GenericRAM.NativeCertificate
