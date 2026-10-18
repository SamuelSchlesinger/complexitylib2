/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Basic
public import Mathlib.Data.List.OfFn

/-!
# Bit encodings of Tree Evaluation instances

An instance of height `h` and value length `ℓ` is encoded by the unary header `1^ℓ 0 1^h 0`,
followed by its body in pre-order: a leaf is its `ℓ` bits, and a gate `f` is its table, the
`4^ℓ * ℓ` bits `f (α k) (β k) i` for `k < 4^ℓ` and `i < ℓ` in this order, where `α k` and `β k` read
the low and high `ℓ` bits of `k`, followed by the bodies of its children.

The body of a subtree of height `d` has length `bodyLength ℓ d`, so the node at a path starts at the
offset `pathOffset`, which a machine can recompute from the path alone.

## Main definitions

* `Cslib.TreeEval.Tree.body`, `Cslib.TreeEval.Tree.encode`: the body and the full encoding.
* `Cslib.TreeEval.tableBit`: the bit of a gate's table at a position.
* `Cslib.TreeEval.pathOffset`: the offset of the node at a path within a body.

## Main results

* `Cslib.TreeEval.Tree.getElem_body_gate`, `Cslib.TreeEval.Tree.getElem_body_leaf`: the table of
  the gate, or the value of the leaf, at a path, read off the body at its offset.
-/

@[expose] public section

namespace Cslib.TreeEval

variable {ℓ : ℕ}

/-- The low `ℓ` bits of `k`. -/
def lowBits (ℓ k : ℕ) : Fin ℓ → Bool := fun j => k.testBit j

/-- The bits `ℓ, …, 2ℓ - 1` of `k`. -/
def highBits (ℓ k : ℕ) : Fin ℓ → Bool := fun j => k.testBit (ℓ + j)

/-- The number of bits in the table of a gate on `ℓ`-bit values. -/
def tableLength (ℓ : ℕ) : ℕ := 4 ^ ℓ * ℓ

/-- The bit at position `q` of the table of `f`: output bit `q % ℓ` on the inputs indexed by
`q / ℓ`. -/
def tableBit (f : (Fin ℓ → Bool) → (Fin ℓ → Bool) → Fin ℓ → Bool) (q : ℕ) : Bool :=
  if h : q % ℓ < ℓ then f (lowBits ℓ (q / ℓ)) (highBits ℓ (q / ℓ)) ⟨q % ℓ, h⟩ else false

/-- The table of a gate. -/
def table (f : (Fin ℓ → Bool) → (Fin ℓ → Bool) → Fin ℓ → Bool) : List Bool :=
  List.ofFn fun q : Fin (tableLength ℓ) => tableBit f q

@[simp] theorem length_table (f : (Fin ℓ → Bool) → (Fin ℓ → Bool) → Fin ℓ → Bool) :
    (table f).length = tableLength ℓ := List.length_ofFn

/-- The length of the body of a subtree of height `d`. -/
def bodyLength (ℓ : ℕ) : ℕ → ℕ
  | 0 => ℓ
  | d + 1 => tableLength ℓ + 2 * bodyLength ℓ d

/-- The offset of the node at a path within the body of a subtree of height `d`. -/
def pathOffset (ℓ : ℕ) : ℕ → List Bool → ℕ
  | _, [] => 0
  | 0, _ :: _ => 0
  | d + 1, b :: P => tableLength ℓ + (if b then bodyLength ℓ d else 0) + pathOffset ℓ d P

private theorem getElem?_append_add {α : Type*} (l₁ l₂ : List α) (n : ℕ) :
    (l₁ ++ l₂)[l₁.length + n]? = l₂[n]? := by
  rw [List.getElem?_append_right (by omega)]
  simp

private theorem getElem?_append_of_some {α : Type*} {l₁ : List α} (l₂ : List α) {n : ℕ} {a : α}
    (h : l₁[n]? = some a) : (l₁ ++ l₂)[n]? = some a := by
  have hlt : n < l₁.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at h
    exact absurd h (by simp)
  rw [List.getElem?_append_left hlt, h]

namespace Tree

variable {h : ℕ}

/-- The body of an instance: leaves by their values, gates by their tables, in pre-order. -/
def body : {h : ℕ} → Tree ℓ h → List Bool
  | _, leaf v => List.ofFn v
  | _, node f l r => table f ++ l.body ++ r.body

@[simp] theorem length_body (T : Tree ℓ h) : T.body.length = bodyLength ℓ h := by
  induction T with
  | leaf v => simp [body, bodyLength]
  | node f l r ihl ihr => simp [body, bodyLength, ihl, ihr]; omega

/-- The header `1^ℓ 0 1^h 0`. -/
def header (ℓ h : ℕ) : List Bool :=
  List.replicate ℓ true ++ false :: List.replicate h true ++ [false]

@[simp] theorem length_header (ℓ h : ℕ) : (header ℓ h).length = ℓ + h + 2 := by
  simp [header]; omega

/-- The encoding of an instance: its header, then its body. -/
def encode (T : Tree ℓ h) : List Bool := header ℓ h ++ T.body

/-- **The table of the gate at a path**, read off the body at the offset of the path. -/
theorem getElem_body_gate {d : ℕ} (U : Tree ℓ d) {P : List Bool}
    {f : (Fin ℓ → Bool) → (Fin ℓ → Bool) → Fin ℓ → Bool} (hP : U.nodeAt P = .gate f) {q : ℕ}
    (hq : q < tableLength ℓ) :
    U.body[pathOffset ℓ d P + q]? = some (tableBit f q) := by
  induction U generalizing P with
  | leaf v =>
    cases P <;> simp [nodeAt] at hP
  | @node d g l r ihl ihr =>
    rcases P with _ | ⟨b, P⟩
    · simp only [nodeAt_node_nil, Node.gate.injEq] at hP
      subst hP
      rw [pathOffset, zero_add, body, List.append_assoc, List.getElem?_append_left (by simpa)]
      simp [table, hq]
    · cases b
      · rw [nodeAt_node_false] at hP
        have e : pathOffset ℓ (d + 1) (false :: P) + q =
            (table g).length + (pathOffset ℓ d P + q) := by simp [pathOffset]; omega
        rw [e, body, List.append_assoc, getElem?_append_add]
        exact getElem?_append_of_some _ (ihl hP)
      · rw [nodeAt_node_true] at hP
        have e : pathOffset ℓ (d + 1) (true :: P) + q =
            (table g ++ l.body).length + (pathOffset ℓ d P + q) := by simp [pathOffset]; omega
        rw [e, body, getElem?_append_add, ihr hP]

/-- **The value of the leaf at a path**, read off the body at the offset of the path. -/
theorem getElem_body_leaf {d : ℕ} (U : Tree ℓ d) {P : List Bool} {v : Fin ℓ → Bool}
    (hP : U.nodeAt P = .leaf v) (i : Fin ℓ) :
    U.body[pathOffset ℓ d P + i]? = some (v i) := by
  induction U generalizing P with
  | leaf w =>
    rcases P with _ | ⟨b, P⟩
    · simp only [nodeAt_leaf_nil, Node.leaf.injEq] at hP
      subst hP
      simp [pathOffset, body]
    · simp [nodeAt] at hP
  | @node d g l r ihl ihr =>
    rcases P with _ | ⟨b, P⟩
    · simp at hP
    · cases b
      · rw [nodeAt_node_false] at hP
        have e : pathOffset ℓ (d + 1) (false :: P) + i =
            (table g).length + (pathOffset ℓ d P + i) := by simp [pathOffset]; omega
        rw [e, body, List.append_assoc, getElem?_append_add]
        exact getElem?_append_of_some _ (ihl hP)
      · rw [nodeAt_node_true] at hP
        have e : pathOffset ℓ (d + 1) (true :: P) + i =
            (table g ++ l.body).length + (pathOffset ℓ d P + i) := by simp [pathOffset]; omega
        rw [e, body, getElem?_append_add, ihr hP]

end Tree

end Cslib.TreeEval
