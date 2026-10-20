/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Monotone.BipartiteMatching

/-!
# Bipartite perfect matching

Small instances of the bipartite perfect matching function, the graphs of the Raz–Wigderson
reduction on concrete sizes (Alice's has a perfect matching and Bob's has none, so the game
instances are genuine), and a concrete consequence of the linear depth bound: monotone formulas
for bipartite perfect matching on `2 ^ 20 + 2 ^ 20` vertices have depth at least `126`.
-/

namespace ComplexityTests.BipartiteMatching

open Cslib Cslib.Circuits Cslib.Circuits.BipartiteMatching Cslib.Communication

/-! ### The function -/

-- The complete bipartite graph `K_{3,3}` has a perfect matching, the empty graph has none.
example : bipartitePerfectMatching 3 (fun _ => true) = true :=
  bipartitePerfectMatching_eq_true_iff.mpr ⟨Equiv.refl _, fun _ => rfl⟩

example : bipartitePerfectMatching 3 (fun _ => false) = false := by
  rw [Bool.eq_false_iff]
  rintro h
  obtain ⟨σ, hσ⟩ := bipartitePerfectMatching_eq_true_iff.mp h
  exact Bool.false_ne_true (hσ 0)

example : Monotone (bipartitePerfectMatching 4) :=
  monotone_bipartitePerfectMatching

/-! ### The graphs of the reduction -/

example : HasPerfectMatching (aliceGraph (e := 1) (![true, false, true] : BitString 3)) :=
  hasPerfectMatching_aliceGraph _

example : ¬HasPerfectMatching (bobGraph (e := 1) (1 : Fin 3) ![false, true, true]) :=
  not_hasPerfectMatching_bobGraph _ _

-- With `x = y = {1, 2}` and `i₀ = 0`, the matching edges at `b₀` and `b₂` are both missing from
-- Bob's graph.
example : aliceGraph (e := 0) (![false, true, true] : BitString 3)
    (.inl (.inl 2), aliceMatching ![false, true, true] (.inl (.inl 2))) = true ∧
      bobGraph (e := 0) (0 : Fin 3) ![false, true, true]
        (.inl (.inl 2), aliceMatching ![false, true, true] (.inl (.inl 2))) = false := by
  decide

/-! ### Lower bounds -/

example : PublicCoin.ecomplexityFun (1 / 2 ^ 1) (disjointness : BitString 1 → BitString 1 → Bool) ≤
    1 * (Protocol.ecomplexity ExceedsAt {x | bipartitePerfectMatching 2 x = true}
      {y | bipartitePerfectMatching 2 y = false} + 1) :=
  ecomplexityFun_disjointness_le_mul_ecomplexity_bipartitePerfectMatching (by norm_num)
    (by norm_num) (by norm_num)

example : (126 : ℕ∞) ≤ Monotone.eformulaDepth (bipartitePerfectMatching (2 ^ 20)) := by
  have h := Monotone.le_mul_eformulaDepth_bipartitePerfectMatching_add (2 ^ 20)
  cases hd : Monotone.eformulaDepth (bipartitePerfectMatching (2 ^ 20)) using ENat.recTopCoe with
  | top => exact le_top
  | coe d =>
    rw [hd] at h
    have : 2 ^ 20 ≤ 2 ^ 13 * d + 2 ^ 14 := by exact_mod_cast h
    exact_mod_cast (show 126 ≤ d by omega)

/-! ### Axioms -/

/--
info: 'Cslib.Circuits.Monotone.le_mul_eformulaDepth_bipartitePerfectMatching_add' depends on
axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.Monotone.le_mul_eformulaDepth_bipartitePerfectMatching_add

/--
info: 'Cslib.Circuits.le_mul_ecomplexity_bipartitePerfectMatching_add' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.le_mul_ecomplexity_bipartitePerfectMatching_add

/--
info: 'Cslib.Circuits.ecomplexityFun_disjointness_le_mul_ecomplexity_bipartitePerfectMatching'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.ecomplexityFun_disjointness_le_mul_ecomplexity_bipartitePerfectMatching

/--
info: 'Cslib.Circuits.BipartiteMatching.two_mul_card_filter_run_oneRun_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Circuits.BipartiteMatching.two_mul_card_filter_run_oneRun_le

end ComplexityTests.BipartiteMatching
