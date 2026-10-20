/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Fintype.Prod

/-!
# Iterated products of vertices

The graph products that build expanders and Reingold's transformation pair a vertex of the
previous graph with a vertex of a fixed base graph at every step, so the vertices of the `ℓ`-th
graph form the product `(⋯ (V × B) × ⋯) × B` with `ℓ` factors `B`, nested to the left
(`Cslib.RotationMap.ReingoldVertex V B ℓ`). The zig-zag tower is the case `V = B`
(`Cslib.RotationMap.ZigzagTowerVertex`), and Reingold's transformation
(`Cslib.RotationMap.reingold`) the case of an arbitrary graph on `V` and a base graph on `B`
[Reingold, Definition 3.1][Reingold2008]. A vertex lies over its first coordinate, its root, and
is presented by its root and its other coordinates, the outermost first
(`Cslib.RotationMap.ReingoldVertex.toList`).

## Main definitions

* `Cslib.RotationMap.ReingoldVertex`: the iterated products.
* `Cslib.RotationMap.ReingoldVertex.root`, `Cslib.RotationMap.ReingoldVertex.mk`,
  `Cslib.RotationMap.ReingoldVertex.setRoot`, `Cslib.RotationMap.ReingoldVertex.map`: the root,
  the vertex with given root and constant coordinates, replacing and mapping the root.
* `Cslib.RotationMap.ReingoldVertex.toList`: the root and the other coordinates.

## Main results

* `Cslib.RotationMap.ReingoldVertex.card`: there are `|V| |B| ^ ℓ` vertices.

## References

* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
-/

@[expose] public section

namespace Cslib.RotationMap

universe u

/-- The iterated product `(⋯ (V × B) × ⋯) × B` with `ℓ` factors `B`, nested to the left: the
vertices of the `ℓ`-th graph of an iterated product of a graph on `V` with graphs on `B`, as each
step pairs a vertex of the previous graph with a vertex on `B`. -/
def ReingoldVertex (V B : Type u) : ℕ → Type u
  | 0 => V
  | ℓ + 1 => ReingoldVertex V B ℓ × B

namespace ReingoldVertex

variable {V W X B : Type u}

/-- The iterated products of finite types are finite. -/
instance instFintype [Fintype V] [Fintype B] : ∀ ℓ, Fintype (ReingoldVertex V B ℓ)
  | 0 => inferInstanceAs (Fintype V)
  | ℓ + 1 =>
    have := instFintype ℓ
    inferInstanceAs (Fintype (ReingoldVertex V B ℓ × B))

/-- Equality in the iterated products is decidable when it is in the factors. -/
instance instDecidableEq [DecidableEq V] [DecidableEq B] : ∀ ℓ, DecidableEq (ReingoldVertex V B ℓ)
  | 0 => inferInstanceAs (DecidableEq V)
  | ℓ + 1 =>
    have := instDecidableEq ℓ
    inferInstanceAs (DecidableEq (ReingoldVertex V B ℓ × B))

/-- The `ℓ`-th iterated product has `|V| |B| ^ ℓ` elements. -/
@[simp]
theorem card [Fintype V] [Fintype B] (ℓ : ℕ) :
    Fintype.card (ReingoldVertex V B ℓ) = Fintype.card V * Fintype.card B ^ ℓ := by
  induction ℓ with
  | zero => exact (mul_one _).symm
  | succ ℓ ih =>
    change Fintype.card (ReingoldVertex V B ℓ × B) = _
    rw [Fintype.card_prod, ih, pow_succ, mul_assoc]

/-- The root of an element of the `ℓ`-th iterated product: its innermost coordinate, in `V`. -/
def root : {ℓ : ℕ} → ReingoldVertex V B ℓ → V
  | 0, v => v
  | ℓ + 1, p => root (ℓ := ℓ) (Prod.fst (β := B) p)

/-- The root of an element of the `(ℓ + 1)`-st iterated product is the root of its first
component. -/
@[simp]
theorem root_succ {ℓ : ℕ} (p : ReingoldVertex V B ℓ × B) :
    root (ℓ := ℓ + 1) p = root p.1 :=
  rfl

/-- The element `(⋯ (v, b) ⋯, b)` of the `ℓ`-th iterated product, with root `v`. -/
def mk (v : V) (b : B) : (ℓ : ℕ) → ReingoldVertex V B ℓ
  | 0 => v
  | ℓ + 1 => (mk v b ℓ, b)

/-- `mk v b ℓ` has root `v`. -/
@[simp]
theorem root_mk (v : V) (b : B) (ℓ : ℕ) : (mk v b ℓ).root = v := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => exact ih

/-- Replace the root of an element of the `ℓ`-th iterated product, keeping its other
coordinates. -/
def setRoot : {ℓ : ℕ} → ReingoldVertex V B ℓ → W → ReingoldVertex W B ℓ
  | 0, _, w => w
  | ℓ + 1, p, w =>
    (setRoot (ℓ := ℓ) (Prod.fst (β := B) p) w, Prod.snd (α := ReingoldVertex V B ℓ) p)

/-- Replacing the root by `w` gives an element with root `w`. -/
@[simp]
theorem root_setRoot {ℓ : ℕ} (x : ReingoldVertex V B ℓ) (w : W) : (x.setRoot w).root = w := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => exact ih _

/-- Replacing the root by itself does nothing. -/
@[simp]
theorem setRoot_root {ℓ : ℕ} (x : ReingoldVertex V B ℓ) : x.setRoot x.root = x := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => exact Prod.ext (ih _) rfl

/-- Apply a map of `V` to the root. -/
def map (φ : V → W) : (ℓ : ℕ) → ReingoldVertex V B ℓ → ReingoldVertex W B ℓ
  | 0 => φ
  | ℓ + 1 => Prod.map (map φ ℓ) id

/-- Mapping the root of a vertex with replaced root. -/
@[simp]
theorem map_setRoot (φ : V → W) {ℓ : ℕ} (x : ReingoldVertex X B ℓ) (v : V) :
    map φ ℓ (x.setRoot v) = x.setRoot (φ v) := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => exact Prod.ext (ih _) rfl

/-- The root of a mapped element is the image of its root. -/
@[simp]
theorem root_map (φ : V → W) {ℓ : ℕ} (x : ReingoldVertex V B ℓ) : (map φ ℓ x).root = φ x.root := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => exact ih _

/-- The root and the other coordinates of an element of the `m`-th iterated product, the
outermost coordinate first. -/
def toList : {m : ℕ} → ReingoldVertex V B m → V × List B
  | 0, v => (v, [])
  | m + 1, p =>
    ((toList (m := m) (Prod.fst (β := B) p)).1,
      Prod.snd (α := ReingoldVertex V B m) p :: (toList (m := m) (Prod.fst (β := B) p)).2)

/-- An element of the `0`-th iterated product has no coordinates besides its root. -/
@[simp]
theorem toList_zero (v : ReingoldVertex V B 0) : toList (m := 0) v = (v, []) :=
  rfl

/-- The coordinates of an element of the `(m + 1)`-st iterated product: its last coordinate, then
those of its first component. -/
@[simp]
theorem toList_succ {m : ℕ} (p : ReingoldVertex V B m × B) :
    toList (m := m + 1) p = ((toList p.1).1, p.2 :: (toList p.1).2) :=
  rfl

/-- The first component of `toList` is the root. -/
@[simp]
theorem fst_toList {m : ℕ} (x : ReingoldVertex V B m) : (toList x).1 = x.root := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih _

/-- An element of the `m`-th iterated product has `m` coordinates besides its root. -/
@[simp]
theorem length_toList {m : ℕ} (x : ReingoldVertex V B m) : (toList x).2.length = m := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg Nat.succ (ih _)

/-- The coordinates of `mk v b m` besides its root are `m` copies of `b`. -/
@[simp]
theorem toList_mk (v : V) (b : B) (m : ℕ) : toList (mk v b m) = (v, List.replicate m b) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [mk, ih, List.replicate_succ]

end ReingoldVertex

end Cslib.RotationMap
