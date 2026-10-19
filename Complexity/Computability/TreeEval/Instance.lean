/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Reader.Correct
public import Complexity.Computability.TreeEval.Reader.Arith

/-!
# Tree Evaluation instances of all sizes

`Cslib.TreeEval.Instance` collects the instances of all value lengths and heights, and
`Cslib.TreeEval.encInstance` encodes them injectively by `Cslib.TreeEval.Tree.encode`: the header
determines the value length and the height, and the body determines the tree, as the table of a
gate determines the gate.

## Main definitions

* `Cslib.TreeEval.Instance`: an instance of some value length and height.
* `Cslib.TreeEval.encInstance`: the encoding of instances.
-/

@[expose] public section

namespace Cslib.TreeEval

/-- A Tree Evaluation instance of some value length and height. -/
structure Instance where
  /-- The value length. -/
  ell : ℕ
  /-- The height. -/
  height : ℕ
  /-- The tree. -/
  tree : Tree ell height

open Reader in
/-- The table of a gate determines the gate. -/
theorem table_injective {ℓ : ℕ} {f g : Gate ℓ}
    (h : table f = table g) : f = g := by
  funext a b i
  let k := cubeEquiv ℓ (Sum.elim a b)
  have hk : Sum.elim (lowBits ℓ k) (highBits ℓ k) = Sum.elim a b := by
    rw [← cubeEquiv_symm_apply, Equiv.symm_apply_apply]
  have ha : lowBits ℓ k = a := funext fun j => congrFun hk (Sum.inl j)
  have hb : highBits ℓ k = b := funext fun j => congrFun hk (Sum.inr j)
  have hlt : (k : ℕ) * ℓ + i < tableLength ℓ := by
    have h4 : (k : ℕ) < 4 ^ ℓ := by rw [four_pow_eq]; exact k.isLt
    rw [tableLength]
    nlinarith [i.isLt]
  have := congrArg (fun l : List Bool => l[(k : ℕ) * ℓ + i]?) h
  simp only [table, List.getElem?_ofFn, hlt, dite_true, Option.some.injEq,
    tableBit_mul_add, ha, hb] at this
  exact this

namespace Tree

/-- The body determines the tree. -/
theorem body_injective {ℓ : ℕ} : ∀ {h : ℕ} {T T' : Tree ℓ h}, T.body = T'.body → T = T'
  | _, .leaf v, .leaf v', hb => by
    simp only [body] at hb
    rw [List.ofFn_injective hb]
  | _, .node f l r, .node f' l' r', hb => by
    simp only [body, List.append_assoc] at hb
    obtain ⟨h₁, hb⟩ := List.append_inj hb (by simp)
    obtain ⟨h₂, h₃⟩ := List.append_inj hb (by simp)
    rw [table_injective h₁, body_injective h₂, body_injective h₃]

end Tree

theorem encode_injective {I J : Instance} (h : I.tree.encode = J.tree.encode) : I = J := by
  obtain ⟨ℓ, H, T⟩ := I
  obtain ⟨ℓ', H', T'⟩ := J
  obtain ⟨rfl, rfl, hb⟩ := Tree.header_append_inj h
  cases Tree.body_injective hb; rfl

/-- **The encoding of instances.** -/
def encInstance : Instance ↪ List Bool := ⟨fun I => I.tree.encode, fun _ _ => encode_injective⟩

@[simp] theorem encInstance_apply (I : Instance) : encInstance I = I.tree.encode := rfl

end Cslib.TreeEval
