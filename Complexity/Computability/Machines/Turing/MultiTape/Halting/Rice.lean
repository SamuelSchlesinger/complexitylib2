/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Halting
public import Complexity.Computability.Machines.Turing.MultiTape.Halting.SMN

/-!
# Rice's theorem
-/

@[expose] public section

namespace Turing.MultiTapeTM

namespace Universal

/-! ### Finding transitions -/

theorem find?_append_of_forall_not {α : Type*} {l₁ l₂ : List α} {p : α → Bool}
    (h : ∀ e ∈ l₁, p e = false) : (l₁ ++ l₂).find? p = l₂.find? p := by
  rw [List.find?_append, List.find?_eq_none.mpr fun e he => by simp [h e he], Option.none_or]

theorem find?_append_of_forall_not' {α : Type*} {l₁ l₂ : List α} {p : α → Bool}
    (h : ∀ e ∈ l₂, p e = false) : (l₁ ++ l₂).find? p = l₁.find? p := by
  have h₂ : l₂.find? p = none := List.find?_eq_none.mpr fun e he => by simp [h e he]
  rw [List.find?_append, h₂, Option.or_none]

section Desc

variable {k : ℕ} {S Y : Type} [Fintype S] [Fintype Y] (eS : S ↪ ℕ) (eY : Y ↪ ℕ)

omit [Fintype S] [Fintype Y] in
theorem key_map_injective : Function.Injective fun e : S × Option Y × (Fin k → Option Y) =>
    key (eS e.1) (e.2.1.map eY) (Option.map eY ∘ e.2.2) := by
  rintro ⟨q, i, w⟩ ⟨q', i', w'⟩ h
  simp only [key, Key.mk.injEq] at h
  rw [eS.injective h.1, Option.map_injective eY.injective h.2.1,
    (Option.map_injective eY.injective).comp_left (List.ofFn_injective h.2.2)]

/-- The transition found in the description of a machine is the renamed transition of the
machine. -/
theorem find?_desc (tm : MultiTapeTM k Y S) (q : S) (inp : Option Y) (work : Fin k → Option Y) :
    (desc eS eY tm).table.find? (·.1 = key (eS q) (inp.map eY) (Option.map eY ∘ work)) =
      some (key (eS q) (inp.map eY) (Option.map eY ∘ work),
        .ofAction ((tm.tr q inp work).map eS eY)) := by
  refine find?_eq_some_of_mem (l := (desc eS eY tm).table)
    (e := (key (eS q) (inp.map eY) (Option.map eY ∘ work),
      .ofAction ((tm.tr q inp work).map eS eY)))
    (List.mem_map.mpr ⟨(q, inp, work), Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩)
    fun e' he' hk => ?_
  obtain ⟨⟨q', i', w'⟩, -, rfl⟩ := List.mem_map.mp he'
  cases key_map_injective eS eY (a₁ := (q', i', w')) (a₂ := (q, inp, work)) hk
  rfl

end Desc

theorem Tape.read_eq_cellAt_head (t : Tape) : t.read = t.cellAt t.head := by
  simp only [Tape.read, Tape.cellAt, le_refl, ↓reduceIte, sub_self, Int.toNat_zero]
  cases t.right <;> rfl

/-- The key read in a well-shaped configuration of the simulation is the key of the configuration
it represents. -/
theorem SCfg.key_eq_key_toCfg {k : ℕ} {x : List ℕ} {s : SCfg} (hs : s.WellShaped k x)
    (out : List ℕ) (q : ℕ) :
    s.key x q =
      Universal.key q (s.toCfg k x out).inputSymbol (s.toCfg k x out).workTapeSymbols := by
  obtain ⟨hk, hp⟩ := hs
  simp only [SCfg.key, Universal.key, Key.mk.injEq, true_and]
  constructor
  · rw [Cfg.inputSymbol_eq_inputAt]
    simp only [SCfg.toCfg, min_eq_left hp, inputSymbol, inputAt, List.head?_drop]
  · refine List.ext_getElem (by simp [hk]) fun i h₁ h₂ => ?_
    have hi : i < s.workTapes.length := by simpa using h₁
    simp [Cfg.workTapeSymbols, SCfg.toCfg, Tape.read_eq_cellAt_head, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi]

/-! ### Dispatching on a computed bit -/

/-- The action on the virtual input tape writing there the symbol `o` emitted by a transition. -/
def outAct (o : Option ℕ) : TapeAct :=
  o.elim (none, .zero) fun s => (some (some s), .pos)

/-- The states of the description `d b` in `Turing.MultiTapeTM.Universal.dispatch`. -/
def dstate (b : Bool) (q : ℕ) : ℕ :=
  4 * q + 2 + b.toNat

namespace Dispatch

variable {k : ℕ} {S : Type} [Fintype S] (eS : S ↪ ℕ) (tm : MultiTapeTM k Bool S)
  (d : Bool → Desc)

/-- The number of work tapes of the two descriptions. -/
def width : ℕ := max (d false).tapes (d true).tapes

/-- What the work tapes after the virtual input tape read before and after the run of `tm`. -/
def rest (k : ℕ) : List (Option ℕ) :=
  List.replicate k none ++ List.replicate (width d) none

/-- Writing the marker, in the state `0`. -/
def markerEntries : List (Key × Act) :=
  bitSyms.map fun r => (⟨0, r, none :: rest d k⟩,
    ⟨.zero, [(some (some marker), .pos)], none, some (4 * eS tm.q₀ + 1)⟩)

/-- The transitions of `tm`, in the states `4 * q + 1`, writing its output on the virtual input
tape, and moving to the state `4` when `tm` halts. -/
noncomputable def runEntries : List (Key × Act) :=
  (desc eS eBit tm).table.map fun e =>
    (⟨4 * e.1.state + 1, e.1.input, none :: (e.1.work ++ List.replicate (width d) none)⟩,
      ⟨e.2.inputTape, outAct e.2.output :: e.2.workTapes, none,
        some (e.2.state.elim 4 fun q => 4 * q + 1)⟩)

/-- Rewinding the virtual input tape, in the state `4`, and branching on its first symbol in the
state `8`: the symbol becomes the marker, and the input head moves onto the blank left of the
input. -/
def branchEntries (k : ℕ) : List (Key × Act) :=
  (bitSyms.flatMap fun r => rewindEntries 4 r (rest d k) 8) ++
    bitSyms.flatMap fun r => [false, true].map fun b => (⟨8, r, some (eBit b) :: rest d k⟩,
      ⟨.neg, [(some (some marker), .pos)], none, some (dstate b (d b).q₀)⟩)

/-- The transitions of `d b`, reading the input from the virtual input tape. -/
def redirectEntries (k : ℕ) (b : Bool) : List (Key × Act) :=
  redirect (dstate b) none (List.replicate k none) (width d - (d b).tapes)
    (List.take (d b).tapes) (d b).table

end Dispatch

open Dispatch in
/-- **Dispatching on a computed bit.** The description runs the machine `tm`, buffering its output
on a new first work tape, the virtual input tape; when `tm` halts with output `b :: v`, it runs the
description `d b` on `v`, reading it from the virtual input tape
(`Turing.MultiTapeTM.Universal.Desc.computes_dispatch`). -/
noncomputable def dispatch {k : ℕ} {S : Type} [Fintype S] (eS : S ↪ ℕ) (tm : MultiTapeTM k Bool S)
    (d : Bool → Desc) : Desc :=
  ⟨k + width d + 1, 0, markerEntries eS tm d ++ runEntries eS tm d ++ branchEntries d k ++
    redirectEntries d k false ++ redirectEntries d k true⟩

end Universal

end Turing.MultiTapeTM
