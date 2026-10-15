/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Init
public import Mathlib.Data.ENat.Lattice

/-!
# Deterministic communication protocols

Alice holds `x : X` and Bob holds `y : Y`. A deterministic protocol is a binary tree whose internal
nodes are owned by one of the players, who sends one bit computed from their input to choose the
branch, and whose leaves are labelled by outputs (`Protocol.run`)
[Kushilevitz and Nisan, Chapter 1][KushilevitzNisan1997]. Its depth is the number of bits sent in
the worst case, and a protocol of depth `d` has at most `2 ^ d` leaves
(`Protocol.leaves_le_two_pow_depth`). A protocol *solves* a relation `R` on inputs from `A × B`
when its output on every such pair is related to the pair (`Protocol.Solves`); the communication
complexity of `R` on `A × B` is the least depth of a protocol solving it, or `⊤` if there is none
(`Protocol.ecomplexity`) [Kushilevitz and Nisan, Chapter 5][KushilevitzNisan1997].

## Main definitions

* `Cslib.Communication.Protocol`: deterministic two-party protocols.
* `Cslib.Communication.Protocol.run`, `Cslib.Communication.Protocol.depth`,
  `Cslib.Communication.Protocol.leaves`, `Cslib.Communication.Protocol.Solves`.
* `Cslib.Communication.Protocol.ecomplexity`: the communication complexity of a relation.

## Main results

* `Cslib.Communication.Protocol.leaves_le_two_pow_depth`: a protocol has at most `2 ^ depth`
  leaves.
* `Cslib.Communication.Protocol.ecomplexity_le_iff`,
  `Cslib.Communication.Protocol.le_ecomplexity_iff`: upper and lower bounds on communication
  complexity.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

/-- A deterministic protocol between Alice, holding `x : X`, and Bob, holding `y : Y`, with
outputs in `Z`. -/
inductive Protocol (X Y Z : Type*) where
  /-- Output `z`. -/
  | output (z : Z)
  /-- Alice sends `send x` and the protocol continues with `ifFalse` or `ifTrue`. -/
  | alice (send : X → Bool) (ifFalse ifTrue : Protocol X Y Z)
  /-- Bob sends `send y` and the protocol continues with `ifFalse` or `ifTrue`. -/
  | bob (send : Y → Bool) (ifFalse ifTrue : Protocol X Y Z)

namespace Protocol

variable {X Y Z : Type*}

/-- The output of a protocol when Alice holds `x` and Bob holds `y`. -/
def run : Protocol X Y Z → X → Y → Z
  | output z, _, _ => z
  | alice send p₀ p₁, x, y => cond (send x) (p₁.run x y) (p₀.run x y)
  | bob send p₀ p₁, x, y => cond (send y) (p₁.run x y) (p₀.run x y)

/-- The number of bits sent in the worst case. -/
def depth : Protocol X Y Z → ℕ
  | output _ => 0
  | alice _ p₀ p₁ => max p₀.depth p₁.depth + 1
  | bob _ p₀ p₁ => max p₀.depth p₁.depth + 1

/-- The number of leaves. -/
def leaves : Protocol X Y Z → ℕ
  | output _ => 1
  | alice _ p₀ p₁ => p₀.leaves + p₁.leaves
  | bob _ p₀ p₁ => p₀.leaves + p₁.leaves

@[simp] theorem run_output (z : Z) (x : X) (y : Y) : (output z : Protocol X Y Z).run x y = z :=
  rfl

@[simp] theorem run_alice (send : X → Bool) (p₀ p₁ : Protocol X Y Z) (x : X) (y : Y) :
    (alice send p₀ p₁).run x y = cond (send x) (p₁.run x y) (p₀.run x y) :=
  rfl

@[simp] theorem run_bob (send : Y → Bool) (p₀ p₁ : Protocol X Y Z) (x : X) (y : Y) :
    (bob send p₀ p₁).run x y = cond (send y) (p₁.run x y) (p₀.run x y) :=
  rfl

@[simp] theorem depth_output (z : Z) : (output z : Protocol X Y Z).depth = 0 :=
  rfl

@[simp] theorem depth_alice (send : X → Bool) (p₀ p₁ : Protocol X Y Z) :
    (alice send p₀ p₁).depth = max p₀.depth p₁.depth + 1 :=
  rfl

@[simp] theorem depth_bob (send : Y → Bool) (p₀ p₁ : Protocol X Y Z) :
    (bob send p₀ p₁).depth = max p₀.depth p₁.depth + 1 :=
  rfl

@[simp] theorem leaves_output (z : Z) : (output z : Protocol X Y Z).leaves = 1 :=
  rfl

@[simp] theorem leaves_alice (send : X → Bool) (p₀ p₁ : Protocol X Y Z) :
    (alice send p₀ p₁).leaves = p₀.leaves + p₁.leaves :=
  rfl

@[simp] theorem leaves_bob (send : Y → Bool) (p₀ p₁ : Protocol X Y Z) :
    (bob send p₀ p₁).leaves = p₀.leaves + p₁.leaves :=
  rfl

/-- A protocol sending `d` bits has at most `2 ^ d` leaves. -/
theorem leaves_le_two_pow_depth (p : Protocol X Y Z) : p.leaves ≤ 2 ^ p.depth := by
  induction p with
  | output z => simp
  | alice send p₀ p₁ ih₀ ih₁ | bob send p₀ p₁ ih₀ ih₁ =>
    have h₀ := ih₀.trans (Nat.pow_le_pow_right (by decide) (le_max_left p₀.depth p₁.depth))
    have h₁ := ih₁.trans (Nat.pow_le_pow_right (by decide) (le_max_right p₀.depth p₁.depth))
    simp only [leaves_alice, leaves_bob, depth_alice, depth_bob, pow_succ]
    omega

/-- A protocol solves the relation `R` on `A × B` when its output on every pair of inputs from
`A × B` is related to them. -/
def Solves (p : Protocol X Y Z) (R : X → Y → Z → Prop) (A : Set X) (B : Set Y) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, R x y (p.run x y)

variable {p : Protocol X Y Z} {R R' : X → Y → Z → Prop} {A A' : Set X} {B B' : Set Y}

/-- A protocol solving a relation on `A × B` solves it on smaller sets. -/
theorem Solves.mono (h : p.Solves R A B) (hA : A' ⊆ A) (hB : B' ⊆ B) : p.Solves R A' B' :=
  fun x hx y hy => h x (hA hx) y (hB hy)

/-- A protocol solving a relation solves every weaker relation. -/
theorem Solves.of_imp (h : p.Solves R A B) (hR : ∀ x y z, R x y z → R' x y z) :
    p.Solves R' A B :=
  fun x hx y hy => hR x y _ (h x hx y hy)

/-- The communication complexity of `R` on `A × B`: the least depth of a protocol solving it, or
`⊤` if there is none. -/
noncomputable def ecomplexity (R : X → Y → Z → Prop) (A : Set X) (B : Set Y) : ℕ∞ :=
  ⨅ p : {p : Protocol X Y Z // p.Solves R A B}, (p.1.depth : ℕ∞)

theorem ecomplexity_le_depth (hp : p.Solves R A B) : ecomplexity R A B ≤ p.depth :=
  iInf_le (fun p : {p : Protocol X Y Z // p.Solves R A B} => (p.1.depth : ℕ∞)) ⟨p, hp⟩

theorem ecomplexity_ne_top_iff :
    ecomplexity R A B ≠ ⊤ ↔ ∃ p : Protocol X Y Z, p.Solves R A B := by
  rw [ecomplexity, ENat.iInf_natCast_ne_top, nonempty_subtype]

/-- When some protocol solves `R`, the least depth is attained. -/
theorem exists_solves_depth_eq_ecomplexity (h : ∃ p : Protocol X Y Z, p.Solves R A B) :
    ∃ p : Protocol X Y Z, p.Solves R A B ∧ (p.depth : ℕ∞) = ecomplexity R A B := by
  have : Nonempty {p : Protocol X Y Z // p.Solves R A B} := nonempty_subtype.mpr h
  obtain ⟨⟨p, hp⟩, hmin⟩ := ENat.exists_eq_iInf
    (fun p : {p : Protocol X Y Z // p.Solves R A B} => (p.1.depth : ℕ∞))
  exact ⟨p, hp, hmin⟩

theorem ecomplexity_le_iff {k : ℕ} :
    ecomplexity R A B ≤ k ↔ ∃ p : Protocol X Y Z, p.Solves R A B ∧ p.depth ≤ k := by
  constructor
  · intro h
    obtain ⟨p, hp, hdepth⟩ := exists_solves_depth_eq_ecomplexity
      (ecomplexity_ne_top_iff.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top k) h))
    exact ⟨p, hp, by exact_mod_cast hdepth.trans_le h⟩
  · rintro ⟨p, hp, hk⟩
    exact (ecomplexity_le_depth hp).trans (by exact_mod_cast hk)

/-- Lower bounds on communication complexity are lower bounds on the depth of every protocol
solving the relation, including when there is none. -/
theorem le_ecomplexity_iff {k : ℕ∞} :
    k ≤ ecomplexity R A B ↔ ∀ p : Protocol X Y Z, p.Solves R A B → k ≤ p.depth := by
  simp only [ecomplexity, le_iInf_iff, Subtype.forall]

/-- Solving a relation on larger sets is harder. -/
theorem ecomplexity_mono (hA : A' ⊆ A) (hB : B' ⊆ B) : ecomplexity R A' B' ≤ ecomplexity R A B :=
  le_iInf fun p => iInf_le_of_le ⟨p.1, p.2.mono hA hB⟩ le_rfl

end Protocol

end Cslib.Communication
