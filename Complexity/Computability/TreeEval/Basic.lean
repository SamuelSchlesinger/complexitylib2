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

end Tree

end Cslib.TreeEval
