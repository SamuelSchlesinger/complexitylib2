/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Tactic.Stateful

/-!
# Adaptive resource contracts through two interface implementations

An abstract counter is implemented with a mutable cell, which is implemented using the first
component of a pair. The second component is hidden storage. A client reads the counter and
increments it only when the answer is zero. Costs count the supplied primitive evidence:
reads cost two and writes cost three. No whole-machine runtime bound is asserted.
-/

@[expose] public section

namespace Cslib.Stateful.Tests

/-- A counter supporting reads and increments. -/
abbrev counter : Spec where
  State := Nat
  Op := Bool
  Result _ := Nat
  step s inc := if inc then (s + 1, s + 1) else (s, s)

/-- A mutable natural-number cell. -/
abbrev cell : Spec where
  State := Nat
  Op := Option Nat
  Result _ := Nat
  step s o := match o with
    | none => (s, s)
    | some n => (n, n)

/-- Two independent mutable cells. -/
abbrev storage : Spec := product cell cell

/-- Budget for a counter operation realized with reads and writes. -/
def counterCharge (_ : Nat) (inc : Bool) : Nat := if inc then 5 else 2

/-- Primitive read and write costs. -/
def cellCharge (_ : Nat) : Option Nat → Nat
  | none => 2
  | some _ => 3

/-- Charge the selected component. -/
def storageCharge (s : Nat × Nat) : storage.Op → Nat
  | .inl o => cellCharge s.1 o
  | .inr o => cellCharge s.2 o

/-- Implement increments by reading and writing a cell. -/
def counterModule : Module counter cell where
  methods inc := .liftBind none fun (n : Nat) =>
    if inc then .liftBind (some (n + 1)) fun m => .pure m else .pure n
  rep := Eq
  valid inc hr _ := by subst hr; cases inc <;> trivial
  correct inc hr _ := by subst hr; cases inc <;> exact ⟨rfl, rfl⟩

/-- Represent a cell using the first storage component. -/
def cellModule : Module cell storage where
  methods o := .liftBind (.inl o) fun n => .pure n
  rep s e := s = e.1
  valid _ _ _ := ⟨trivial, trivial⟩
  correct o hr _ := by
    cases o with
    | none => exact ⟨hr.symm, hr⟩
    | some n => exact ⟨rfl, rfl⟩

theorem counter_bound : counterModule.ChargeBound cellCharge counterCharge := by
  intro s e o hr _
  subst hr
  cases o <;> exact Nat.le_refl _

theorem cell_bound : cellModule.ChargeBound storageCharge cellCharge := by
  intro s e o _ _
  cases o <;> exact Nat.le_refl _

/-- Read the counter and increment it only when its value is zero. -/
def ensurePositive : counter.Client Nat :=
  (.liftBind false (fun n => .pure n) : counter.Client Nat).bind fun n =>
    if n = 0 then .liftBind true (fun m => .pure m) else .pure n

theorem read_contract : counter.CostHoare counterCharge (fun _ => True)
    (.liftBind false fun n => .pure n) (fun n s => n = s) (fun s => counterCharge s false) := by
  stateful

theorem continue_contract (n : Nat) : counter.CostHoare counterCharge
    (fun s => n = s)
    (if n = 0 then .liftBind true (fun m => .pure m) else .pure n : counter.Client Nat)
    (fun m s => m = s ∧ 0 < m) (fun _ => 5) := by
  split
  · apply Spec.CostHoare.call
    intro s _
    exact ⟨trivial, rfl, Nat.zero_lt_succ s⟩
  · have hp : counter.CostHoare counterCharge (fun s => n = s) (.pure n)
        (fun m s => m = s ∧ 0 < m) (fun _ => 0) := by
      apply Spec.CostHoare.pure
      intro s hs
      exact ⟨hs, by omega⟩
    exact hp.consequence (fun _ hs => hs) (fun _ _ hs => hs) (fun _ _ => by omega)

/-- The adaptive abstract client satisfies a uniform seven-unit operation budget. -/
theorem ensurePositive_contract : counter.CostHoare counterCharge (fun _ => True)
    ensurePositive (fun n s => n = s ∧ 0 < n) (fun _ => 7) := by
  exact Spec.CostHoare.bind read_contract continue_contract
    (fun _ _ _ _ _ => Nat.le_refl 7)

/-- Two successive interface implementations. -/
def implementation := counterModule.comp cellModule

/-- Both refinement layers preserve the same client contract and quantitative bound. -/
theorem ensurePositive_linked : storage.CostHoare storageCharge
    (fun e => ∃ s, True ∧ implementation.rep s e)
    (link implementation.methods ensurePositive)
    (fun n e => ∃ s, (n = s ∧ 0 < n) ∧ implementation.rep s e) (fun _ => 7) :=
  ensurePositive_contract.link (counter_bound.comp cell_bound) (fun _ => 7)
    (fun _ _ _ _ => Nat.le_refl _)

/-- Primitive evidence records the specified transition and its charged cost. -/
def exec : Execution storage (Nat × Nat) Nat :=
  fun s o a s' t => (s', a) = storage.step s o ∧ t = storageCharge s o

/-- The deterministic primitive semantics realizes the storage interface. -/
def realization : Realization storage exec where
  rep := Eq
  total o hr _ := by subst hr; exact ⟨_, _, _, rfl, rfl⟩
  correct hr _ he := by
    subst hr
    exact ⟨congrArg Prod.snd he.1, (congrArg Prod.fst he.1).symm⟩

theorem native_bound : Bound realization id storageCharge := by
  intro s c o a c' t hr _ he
  subst hr
  exact he.2.le

/-- Every initial counter has a native execution within seven units, with a positive answer. -/
theorem ensurePositive_native (s spare : Nat) :
    ∃ a c' traces, Executes exec (link implementation.methods ensurePositive)
      (s, spare) a c' traces ∧
      (∃ s', realization.rep s' c' ∧
        ∃ n, (a = n ∧ 0 < a) ∧ implementation.rep n s') ∧ total id traces ≤ 7 := by
  exact Spec.CostHoare.exists_executes (s := (s, spare)) native_bound ensurePositive_linked
    ⟨s, trivial, s, rfl, rfl⟩ rfl

-- The zero branch performs a read, another read and a write; the nonzero branch only reads.
example : storage.runClient (0, 99) (link implementation.methods ensurePositive) =
    (1, (1, 99), [.inl none, .inl none, .inl (some 1)]) := rfl

example : storage.runClient (8, 99) (link implementation.methods ensurePositive) =
    (8, (8, 99), [.inl none]) := rfl

example : storage.totalCost storageCharge (0, 99)
    (storage.runClient (0, 99) (link implementation.methods ensurePositive)).2.2 = 7 := rfl

example : storage.totalCost storageCharge (8, 99)
    (storage.runClient (8, 99) (link implementation.methods ensurePositive)).2.2 = 2 := rfl

-- A cost certificate cannot silently drop one of the calls in the zero branch.
example : ¬ counter.CostHoare counterCharge (fun _ => True)
    ensurePositive (fun n s => n = s ∧ 0 < n) (fun _ => 6) := by
  intro h
  have hb := h.2 0 trivial
  change 7 ≤ 6 at hb
  omega

-- Named client contracts can be reused by proof search without expanding the implementation.
attribute [local aesop safe apply (rule_sets := [Stateful])] ensurePositive_contract

example : counter.CostHoare counterCharge (fun _ => True)
    ensurePositive (fun n s => n = s ∧ 0 < n) (fun _ => 7) := by
  stateful

-- State-dependent charges must use the changed state for the second call.
example (n : Nat) : counter.CostHoare (fun s _ => s + 1) (fun s => s = n)
    ((.liftBind true (fun a => .pure a) : counter.Client Nat).bind fun _ =>
      .liftBind false fun a => .pure a)
    (fun a s => a = s ∧ s = n + 1) (fun s => 2 * s + 3) := by
  apply Spec.CostHoare.bind (mid := fun a s => a = s ∧ s = n + 1)
    (first := fun s => s + 1) (next := fun _ s => s + 1)
  · apply Spec.CostHoare.call
    intro s hs
    exact ⟨trivial, rfl, congrArg (· + 1) hs⟩
  · intro a
    apply Spec.CostHoare.call
    intro s hs
    exact ⟨trivial, rfl, hs.2⟩
  · intro s hs a s' ha
    rw [hs, ha.2]
    omega

/-- info: 'Cslib.Stateful.Spec.CostHoare.link' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Spec.CostHoare.link

/-- info: 'Cslib.Stateful.Module.ChargeBound.comp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Module.ChargeBound.comp

/-- info: 'Cslib.Stateful.Tests.ensurePositive_native' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ensurePositive_native

end Cslib.Stateful.Tests
