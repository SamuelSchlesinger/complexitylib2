/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Existence
public import Complexity.Foundations.Combinatorics.Expander.Tower
import Complexity.Foundations.Analysis.BernoulliInequality

/-!
# A base graph for the zig-zag tower

The zig-zag tower `Cslib.RotationMap.zigzagTower` is built from one `D`-regular base graph on
`|D| ^ 4` vertices, named by `Fin 2 → D × D`, of spectral expansion at most `1 / 5`. Reingold,
Vadhan and Wigderson find it by exhaustive search, its existence being known from probabilistic
arguments, or construct it algebraically
[Reingold, Vadhan and Wigderson, Section 5][ReingoldVadhanWigderson2002]. Here it is obtained from
the non-explicit family `Cslib.RotationMap.expander` by powering.

The family provides a `120`-regular multigraph of spectral expansion at most `1 - 1 / 360000` on
every finite type, so the base can live directly on the type it must have: with
`D = Fin t → Fin 120`, the labels of the `t`-th power of a `120`-regular multigraph, the `t`-th
power `Cslib.RotationMap.zigzagTowerBase t` of `expander (Fin 2 → D × D)` is a `D`-regular
multigraph on `Fin 2 → D × D` of spectral expansion at most `(1 - 1 / 360000) ^ t`, which is at
most `1 / 5` once `t ≥ 1440000`, as `(1 - x) ^ t (1 + t x) ≤ 1`.

The zig-zag tower over this base is a family of `120 ^ (2 t)`-regular multigraphs on
`120 ^ (4 t (n + 1))` vertices, `n ∈ ℕ`, of spectral expansion at most `2 / 5`
(`Cslib.RotationMap.exists_spectralExpansion_zigzagTower_le`). The base graph is its only
non-explicit ingredient: the tower is computed from the rotation map of the base by a recursion
without choices, while the base is `expander`, chosen by a counting argument.

## Main definitions

* `Cslib.RotationMap.zigzagTowerBase`: the `t`-th power of `expander (Fin 2 → D × D)`, where
  `D = Fin t → Fin 120`.

## Main results

* `Cslib.RotationMap.spectralExpansion_zigzagTowerBase_le_one_div_five`: for `t ≥ 1440000`, the
  base graph has spectral expansion at most `1 / 5`.
* `Cslib.RotationMap.spectralExpansion_zigzagTower_zigzagTowerBase_le`,
  `Cslib.RotationMap.card_zigzagTowerVertex_zigzagTowerBase`: the tower over it consists of
  `120 ^ (2 t)`-regular multigraphs on `120 ^ (4 t (n + 1))` vertices of spectral expansion at most
  `2 / 5`.
* `Cslib.RotationMap.exists_spectralExpansion_zigzagTower_le`: constant-degree expanders on
  `d ^ (4 (n + 1))` vertices for every `n`, explicit given one base graph.

## References

* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
-/

@[expose] public section

namespace Cslib.RotationMap

variable (t : ℕ)

/-- A base graph for the zig-zag tower: the `t`-th power of the `120`-regular multigraph
`expander` on `Fin 2 → D × D`, where `D = Fin t → Fin 120` are the labels of the power. It is
`D`-regular on `|D| ^ 4` vertices, and its spectral expansion is at most `1 / 5` for
`t ≥ 1440000` (`spectralExpansion_zigzagTowerBase_le_one_div_five`). -/
noncomputable def zigzagTowerBase :
    RotationMap (Fin 2 → (Fin t → Fin 120) × (Fin t → Fin 120)) (Fin t → Fin 120) :=
  (expander _).pow t

/-- The spectral expansion of the base graph is at most `(1 - 1 / 360000) ^ t`. -/
theorem spectralExpansion_zigzagTowerBase_le :
    (zigzagTowerBase t).spectralExpansion ≤ (1 - 1 / 360000) ^ t :=
  ((expander _).spectralExpansion_pow_le t).trans
    (pow_le_pow_left₀ (expander _).spectralExpansion_nonneg (spectralExpansion_expander_le _) t)

variable {t}

/-- For `t ≥ 1440000`, the spectral expansion of the base graph is at most `1 / 5`. -/
theorem spectralExpansion_zigzagTowerBase_le_one_div_five (ht : 1440000 ≤ t) :
    (zigzagTowerBase t).spectralExpansion ≤ 1 / 5 := by
  refine (spectralExpansion_zigzagTowerBase_le t).trans ?_
  have h := Real.one_sub_pow_mul_one_add_mul_le_one (p := 1 / 360000) (by norm_num) t
  have ht' : (1440000 : ℝ) ≤ t := by exact_mod_cast ht
  have h₀ : 0 ≤ (1 - 1 / 360000 : ℝ) ^ t := pow_nonneg (by norm_num) t
  nlinarith

/-- The graphs of the zig-zag tower over `zigzagTowerBase t` have `120 ^ (4 t (n + 1))`
vertices. -/
theorem card_zigzagTowerVertex_zigzagTowerBase (t n : ℕ) :
    Fintype.card (ZigzagTowerVertex (Fin 2 → (Fin t → Fin 120) × (Fin t → Fin 120)) n) =
      120 ^ (4 * t * (n + 1)) := by
  rw [card_zigzagTowerVertex_of_equiv (Equiv.refl _), Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, ← pow_mul]
  ring

/-- **Expanders from the zig-zag product**
[Reingold, Vadhan and Wigderson, Theorem 1.4][ReingoldVadhanWigderson2002]: for `t ≥ 1440000`,
the graphs of the zig-zag tower over `zigzagTowerBase t`, which are `120 ^ (2 t)`-regular on
`120 ^ (4 t (n + 1))` vertices, have spectral expansion at most `2 / 5`. -/
theorem spectralExpansion_zigzagTower_zigzagTowerBase_le (ht : 1440000 ≤ t) (n : ℕ) :
    (zigzagTower (zigzagTowerBase t) (Equiv.refl _) n).spectralExpansion ≤ 2 / 5 :=
  spectralExpansion_zigzagTower_le_two_div_five _ _
    (spectralExpansion_zigzagTowerBase_le_one_div_five ht) n

/-- **Constant-degree expanders on `d ^ (4 (n + 1))` vertices, explicit given one base graph**
[Reingold, Vadhan and Wigderson, Theorem 1.4][ReingoldVadhanWigderson2002]
[Hoory, Linial and Wigderson, Section 9.2][HooryLinialWigderson2006]: there are a finite type
`D` of at least two labels and a `D`-regular multigraph `H` on `Fin 2 → D × D` of spectral
expansion at most `1 / 5` such that, for every `n`, the zig-zag tower `zigzagTower H _ n` is a
`|D| ^ 2`-regular multigraph on `|D| ^ (4 (n + 1))` vertices of spectral expansion at most `2 / 5`.

The tower is explicit given `H`: `zigzagTower` computes its rotation maps from that of `H` by a
recursion without choices. Only `H` is obtained non-constructively, as `zigzagTowerBase 1440000`.
-/
theorem exists_spectralExpansion_zigzagTower_le :
    ∃ (D : Type) (_ : Fintype D) (H : RotationMap (Fin 2 → D × D) D),
      1 < Fintype.card D ∧ H.spectralExpansion ≤ 1 / 5 ∧
      ∀ n, Fintype.card (ZigzagTowerVertex (Fin 2 → D × D) n) = Fintype.card D ^ (4 * (n + 1)) ∧
        (zigzagTower H (Equiv.refl _) n).spectralExpansion ≤ 2 / 5 :=
  ⟨Fin 1440000 → Fin 120, inferInstance, zigzagTowerBase 1440000,
    Fintype.one_lt_card_iff_nontrivial.2 inferInstance,
    spectralExpansion_zigzagTowerBase_le_one_div_five le_rfl,
    fun n ↦ ⟨card_zigzagTowerVertex_of_equiv (Equiv.refl _) n,
      spectralExpansion_zigzagTower_zigzagTowerBase_le le_rfl n⟩⟩

end Cslib.RotationMap
