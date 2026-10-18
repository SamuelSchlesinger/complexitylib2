/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Fintype.Pi

/-!
# The Tree Evaluation problem

An instance of Tree Evaluation with height `h` and value length `ℓ` is a full binary tree of
height `h` whose leaves carry `ℓ`-bit values and whose internal nodes carry arbitrary gates
`{0,1}^ℓ × {0,1}^ℓ → {0,1}^ℓ`. The value of a node is its gate applied to the values of its two
children; the answer is the value of the root.

We follow Goldreich's parametrization by the value length `ℓ`, rather than by the alphabet size
`k = 2^ℓ`, so that values are bit strings `Fin ℓ → Bool` without rounding.

## Main definitions

* `Cslib.TreeEval.Tree ℓ h`: a Tree Evaluation instance of height `h` and value length `ℓ`.
* `Cslib.TreeEval.Tree.eval`: the value of the root.
* `Cslib.TreeEval.Tree.nodeAt`: the node at a path from the root.

## References

* [S. Cook, P. McKenzie, D. Wehr, M. Braverman and R. Santhanam, *Pebbles and branching programs
  for tree evaluation*][CMWBS2012] introduce the problem.
* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval] uses the
  parametrization by value length.
-/

@[expose] public section

namespace Cslib.TreeEval

/-- A Tree Evaluation instance: a full binary tree of height `h` whose leaves carry `ℓ`-bit
values and whose internal nodes carry gates on pairs of `ℓ`-bit values. -/
inductive Tree (ℓ : ℕ) : ℕ → Type
  /-- A leaf carrying a value. -/
  | leaf (v : Fin ℓ → Bool) : Tree ℓ 0
  /-- An internal node carrying a gate, with its left and right subtrees. -/
  | node {h : ℕ} (f : (Fin ℓ → Bool) → (Fin ℓ → Bool) → Fin ℓ → Bool) (l r : Tree ℓ h) :
      Tree ℓ (h + 1)
  deriving DecidableEq

namespace Tree

variable {ℓ h : ℕ}

/-- The value of the root: each gate is applied to the values of its children. -/
def eval : {h : ℕ} → Tree ℓ h → Fin ℓ → Bool
  | _, leaf v => v
  | _, node f l r => f l.eval r.eval

@[simp] theorem eval_leaf (v : Fin ℓ → Bool) : (leaf v).eval = v := rfl

@[simp] theorem eval_node (f : (Fin ℓ → Bool) → (Fin ℓ → Bool) → Fin ℓ → Bool)
    (l r : Tree ℓ h) : (node f l r).eval = f l.eval r.eval := rfl

/-- What a path from the root leads to: a leaf with its value, a gate, or nothing. -/
inductive Node (ℓ : ℕ) where
  /-- A leaf with its value. -/
  | leaf (v : Fin ℓ → Bool)
  /-- An internal node with its gate. -/
  | gate (f : (Fin ℓ → Bool) → (Fin ℓ → Bool) → Fin ℓ → Bool)
  /-- A path leaving the tree. -/
  | none

/-- The node reached from the root along a path, where `false` is the left child. -/
def nodeAt : {h : ℕ} → Tree ℓ h → List Bool → Node ℓ
  | _, leaf v, [] => .leaf v
  | _, leaf _, _ :: _ => .none
  | _, node f _ _, [] => .gate f
  | _, node _ l _, false :: P => l.nodeAt P
  | _, node _ _ r, true :: P => r.nodeAt P

@[simp] theorem nodeAt_leaf_nil (v : Fin ℓ → Bool) : (leaf v).nodeAt [] = .leaf v := rfl

@[simp] theorem nodeAt_node_nil (f : (Fin ℓ → Bool) → (Fin ℓ → Bool) → Fin ℓ → Bool)
    (l r : Tree ℓ h) : (node f l r).nodeAt [] = .gate f := rfl

@[simp] theorem nodeAt_node_false (f : (Fin ℓ → Bool) → (Fin ℓ → Bool) → Fin ℓ → Bool)
    (l r : Tree ℓ h) (P : List Bool) : (node f l r).nodeAt (false :: P) = l.nodeAt P := rfl

@[simp] theorem nodeAt_node_true (f : (Fin ℓ → Bool) → (Fin ℓ → Bool) → Fin ℓ → Bool)
    (l r : Tree ℓ h) (P : List Bool) : (node f l r).nodeAt (true :: P) = r.nodeAt P := rfl

end Tree

end Cslib.TreeEval
