/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts

/-!
# Direct degree weakening and polynomial-time consequences

The original three plain rules are moved unchanged from the degree-calculus module to keep
ordinary clients independent of its legacy construction calculus.
-/

@[expose] public section
namespace Turing.MultiTapeTM

namespace ComputableInDegree

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
  {d e d' e' : ℕ}

/-- Increasing either degree retains the same realizing machine. -/
public theorem mono (h : ComputableInDegree f encIn encOut d e)
    (hd : d ≤ d' := by first | decide | omega) (he : e ≤ e' := by first | decide | omega) :
    ComputableInDegree f encIn encOut d' e' :=
  let ⟨⟨t, s, ht, hs, hf⟩, hl⟩ := h
  ⟨⟨t, s, ht.mono_deg hd, hs.mono_deg hd, hf⟩, hl.mono_deg he⟩

/-- Exact time and workspace bounds of degree `d` also bound the output length in degree `d`. -/
public theorem of_bounds {t s : α → ℕ}
    (ht : DegreeBounded (fun a => (encIn a).length) t d)
    (hs : DegreeBounded (fun a => (encIn a).length) s d)
    (hf : ComputableInTimeAndSpace f encIn encOut t s) :
    ComputableInDegree f encIn encOut d d :=
  ⟨⟨t, s, ht, hs, hf⟩, ht.mono hf.length_le⟩

/-- Fixed time and workspace degrees give plain polynomial-time computability, including degree
zero. Encoded output is bounded separately and is not charged to workspace. -/
public theorem computableInPolyTime (h : ComputableInDegree f encIn encOut d e) :
    ComputableInPolyTime f encIn encOut := by
  obtain ⟨⟨_, _, ht, hs, h⟩, _⟩ := h
  obtain ⟨T, hT, ht⟩ := ht.polyBounded
  obtain ⟨S, hS, hs⟩ := hs.polyBounded
  exact ⟨T, S, hT, hS, h.mono ht hs⟩

end ComputableInDegree

end Turing.MultiTapeTM
