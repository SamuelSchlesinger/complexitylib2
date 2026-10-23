/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import Complexity.Computability.Complexity.Classes.LogSpace.USTCON

/-! # Transfer of Reingold's theorem along the exact adjacency-matrix encoding -/

namespace ComplexityTests.Abstracts.USTCONBridge

/-- A Boolean is encoded as one bit. -/
def encBool : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; injection h⟩

/-- A simple graph on `Fin n`, with its symmetric zero-diagonal Boolean adjacency matrix
and two distinguished vertices. The sigma type records the common vertex count. -/
abbrev Instance := Σ n : ℕ,
  {adj : Fin n → Fin n → Bool //
    (∀ a b, adj a b = adj b a) ∧ (∀ a, adj a a = false)} × Fin n × Fin n

/-- The graph determined by the adjacency matrix. -/
def graph (I : Instance) : SimpleGraph (Fin I.1) where
  Adj a b := I.2.1.val a b = true
  symm.symm a b h := (I.2.1.property.1 b a).trans h
  loopless.irrefl a h := by simp only [I.2.1.property.2 a, Bool.false_eq_true] at h

/-- Undirected s–t connectivity: a finite walk connects the distinguished vertices. -/
def USTCON : Set Instance := {I | (graph I).Reachable I.2.2.1 I.2.2.2}

/-- Unary vertex count, source and target, separated by zero bits, followed by the matrix
row by row. Vertex indices range below `n`, so division and remainder select valid entries. -/
def encode (I : Instance) : List Bool :=
  List.replicate I.1 true ++ false :: (List.replicate I.2.2.1.val true ++ false ::
    (List.replicate I.2.2.2.val true ++ false :: List.ofFn (fun i : Fin (I.1 * I.1) =>
      I.2.1.val ⟨i.val / I.1, Nat.div_lt_of_lt_mul i.isLt⟩
        ⟨i.val % I.1, Nat.mod_lt _ (Nat.pos_of_ne_zero (fun h => by simpa [h] using i.isLt))⟩)))

def toInternal (I : Instance) : Cslib.Complexity.USTCONInstance :=
  ⟨I.1, I.2.1.val, I.2.1.property.1, I.2.1.property.2, I.2.2.1, I.2.2.2⟩

def ofInternal (I : Cslib.Complexity.USTCONInstance) : Instance :=
  ⟨I.n, ⟨⟨I.adj, I.symm, I.loopless⟩, I.s, I.t⟩⟩

theorem of_to (I : Instance) : ofInternal (toInternal I) = I := rfl

theorem to_of (I : Cslib.Complexity.USTCONInstance) : toInternal (ofInternal I) = I := rfl

theorem encode_eq (I : Instance) : encode I = Cslib.Complexity.encUSTCON (toInternal I) := rfl

theorem encode_injective : Function.Injective encode := by
  intro I J h
  rw [encode_eq, encode_eq] at h
  exact congrArg ofInternal (Cslib.Complexity.encUSTCON.injective h)

/-- Injective adjacency-matrix instance encoding. -/
def encInstance : Instance ↪ List Bool := ⟨encode, encode_injective⟩

/-- One fixed finite-state binary multi-tape machine computes a total function within
`c * (floor(log₂(input length)) + 1)` work-tape cells and halts on every encoded input.
Read-only input and write-only output are excluded. -/
def ComputableInLogSpace {α β : Type} (f : α → β)
    (a : α ↪ List Bool) (b : β ↪ List Bool) : Prop :=
  ∃ t c, Turing.MultiTapeTM.ComputableInTimeAndSpace f a b t
    (fun x => c * (Nat.log2 (a x).length + 1))

/-- Deterministic logarithmic-space decision. -/
def L {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f : α → Bool, ComputableInLogSpace f enc encBool ∧ ∀ a, a ∈ A ↔ f a = true}

theorem l_eq {α : Type} (enc : α ↪ List Bool) : L enc = Cslib.Complexity.L enc := rfl

theorem ustcon_mem_l : USTCON ∈ L encInstance := by
  obtain ⟨f, ⟨t, c, k, State, hfin, M, hM⟩, hA⟩ := Cslib.Complexity.USTCON_mem_L
  refine ⟨fun I => f (toInternal I), ⟨fun I => t (toInternal I), c, k, State, hfin, M, ?_⟩,
    fun I => hA (toInternal I)⟩
  intro I
  exact hM (toInternal I)

end ComplexityTests.Abstracts.USTCONBridge
