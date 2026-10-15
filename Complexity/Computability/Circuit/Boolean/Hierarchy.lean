/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.PPoly
public import Cslib.Computability.Circuit.Boolean.Shannon
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The circuit size hierarchy

Changing one value of a Boolean function on `n` inputs changes its circuit complexity by at most
`2 n + 3` (`complexity_update_le`). Walking from a constant function to a hard one, one value at a
time, the complexity therefore takes every value between `1` and the complexity of the hard
function, up to `2 n + 3` (`exists_complexity_mem_Ioc`). With Shannon's lower bound, every size
below `2 ^ n / n` is the complexity of some function, up to `2 n + 3`, and so more gates allow
strictly more languages (`SIZE_ssubset`). Walking from a constant function to any function `f`
shows that `f` costs at most `2 ^ n (2 n + 3) + 1` gates (`complexity_le_two_pow_mul_add_one`).

## Main results

* `Cslib.Circuits.Boolean.complexity_update_le`: changing one value costs `2 n + 3` gates.
* `Cslib.Circuits.Boolean.complexity_le_two_pow_mul_add_one`,
  `Cslib.Circuits.Boolean.complexity_le_of_dependsOn`: the truth-table bound, for all functions
  and for functions depending on few inputs.
* `Cslib.Circuits.Boolean.exists_complexity_mem_Ioc`: complexities between `1` and that of a given
  function are attained, up to `2 n + 3`.
* `Cslib.Circuits.Boolean.SIZE_ssubset`: the size hierarchy.
* `Cslib.Circuits.Boolean.SIZE_pow_ssubset`: `SIZE ((n + 1) ^ k) ⊂ SIZE ((n + 1) ^ (k + 1))`.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Filter
open scoped Finset

variable {n : ℕ}

/-- Changing one value of a Boolean function costs at most `2 n + 3` gates. -/
theorem complexity_update_le (f : BooleanFunction n) (a : Fin n → Bool) (b : Bool) :
    complexity interpretation (single (Function.update f a b)) ≤
      complexity interpretation (single f) + (2 * n + 3) := by
  let m : BooleanFunction n := fun x => decide ((fun i => x (id i)) = a)
  have hm : complexity interpretation (single m) ≤ 2 * n + 1 :=
    (synthesis_minterm (n := n) id a).complexity_le
  have hma (x : Fin n → Bool) : m x = decide (x = a) := rfl
  cases b
  · have e : Function.update f a false = fun x => f x && !m x := funext fun x => by
      by_cases h : x = a <;> simp [h, hma]
    rw [e]
    calc complexity interpretation (single fun x => f x && !m x)
        ≤ complexity interpretation (single f) +
            complexity interpretation (single fun x => !m x) + 1 := complexity_and_le _ _
      _ ≤ complexity interpretation (single f) + (complexity interpretation (single m) + 1) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add_left (complexity_not_le m) _) _
      _ ≤ complexity interpretation (single f) + (2 * n + 3) := by omega
  · have e : Function.update f a true = fun x => f x || m x := funext fun x => by
      by_cases h : x = a <;> simp [h, hma]
    rw [e]
    calc complexity interpretation (single fun x => f x || m x)
        ≤ complexity interpretation (single f) + complexity interpretation (single m) + 1 :=
          complexity_or_le _ _
      _ ≤ complexity interpretation (single f) + (2 * n + 3) := by omega

/-- **The truth-table bound.** A Boolean function on `n` inputs costs at most
`2 ^ n * (2 * n + 3) + 1` gates: start from a constant and change one value at a time. -/
theorem complexity_le_two_pow_mul_add_one (f : BooleanFunction n) :
    complexity interpretation (single f) ≤ 2 ^ n * (2 * n + 3) + 1 := by
  classical
  suffices h : ∀ S : Finset (Fin n → Bool),
      complexity interpretation (single fun x => decide (x ∈ S) && f x) ≤
        #S * (2 * n + 3) + 1 by
    simpa using h Finset.univ
  intro S
  induction S using Finset.induction_on with
  | empty => simpa using (Synthesis.const false).complexity_le
  | @insert a S ha ih =>
    have e : (fun x => decide (x ∈ insert a S) && f x) =
        Function.update (fun x => decide (x ∈ S) && f x) a (f a) := funext fun x => by
      by_cases hx : x = a
      · subst hx
        simp
      · simp [hx]
    rw [e, Finset.card_insert_of_notMem ha, add_one_mul]
    calc _ ≤ _ := complexity_update_le _ a (f a)
      _ ≤ _ := by omega

/-- A Boolean function that depends only on the inputs in `s` costs at most
`2 ^ #s * (2 * #s + 3) + 1` gates. -/
theorem complexity_le_of_dependsOn {f : BooleanFunction n} {s : Finset (Fin n)}
    (hf : DependsOn f s) : complexity interpretation (single f) ≤ 2 ^ #s * (2 * #s + 3) + 1 := by
  let g : BooleanFunction #s := fun y =>
    f fun i => if h : i ∈ s then y ((s.orderIsoOfFin rfl).symm ⟨i, h⟩) else false
  have hfg : single f = single g ∘ fun x => x ∘ s.orderEmbOfFin rfl := by
    funext x j
    refine hf fun i hi => ?_
    simp only [dite_eq_left (Finset.mem_coe.1 hi), Function.comp_apply,
      ← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  rw [hfg]
  calc _ ≤ complexity interpretation (fun x => x ∘ s.orderEmbOfFin rfl) +
        complexity interpretation (single g) := complexity_comp_le _ _
    _ ≤ _ := by
      rw [complexity_wiring, zero_add]
      exact complexity_le_two_pow_mul_add_one g

/-- **Discrete intermediate values.** If changing one coordinate raises a measure by at most `B`,
and the measure is at most `t` at `u` and above `t` at `v`, then it lies in `(t, t + B]`
somewhere. -/
theorem exists_lt_le_add_of_update_le {ι : Type*} [Finite ι] [DecidableEq ι]
    (μ : (ι → Bool) → ℕ) {B t : ℕ} (hμ : ∀ w i b, μ (Function.update w i b) ≤ μ w + B)
    {u v : ι → Bool} (hu : μ u ≤ t) (hv : t < μ v) : ∃ w, t < μ w ∧ μ w ≤ t + B := by
  have := Fintype.ofFinite ι
  let w : Finset ι → ι → Bool := fun S i => if i ∈ S then v i else u i
  suffices h : ∀ S : Finset ι, μ (w S) ≤ t ∨ ∃ w, t < μ w ∧ μ w ≤ t + B by
    refine (h Finset.univ).resolve_left fun hle => ?_
    have : w Finset.univ = v := funext fun i => by simp [w]
    exact absurd (this ▸ hle) (not_le.2 hv)
  intro S
  induction S using Finset.induction_on with
  | empty => exact Or.inl (by simpa [w] using hu)
  | @insert i S hi ih =>
    have e : w (insert i S) = Function.update (w S) i (v i) := funext fun j => by
      by_cases hj : j = i
      · subst hj
        simp [w]
      · simp [w, hj]
    rcases ih with hle | found
    · by_cases hnext : μ (w (insert i S)) ≤ t
      · exact Or.inl hnext
      · refine Or.inr ⟨_, not_le.1 hnext, ?_⟩
        rw [e]
        exact (hμ _ _ _).trans (Nat.add_le_add_right hle B)
    · exact Or.inr found

/-- Every complexity between `1` and that of a given function is attained by some function, up
to `2 n + 3`. -/
theorem exists_complexity_mem_Ioc {t : ℕ} (ht : 1 ≤ t) (g : BooleanFunction n)
    (hg : t < complexity interpretation (single g)) :
    ∃ f : BooleanFunction n, t < complexity interpretation (single f) ∧
      complexity interpretation (single f) ≤ t + (2 * n + 3) := by
  classical
  exact exists_lt_le_add_of_update_le (fun f => complexity interpretation (single f))
    complexity_update_le (u := fun _ => false)
    ((Synthesis.const false).complexity_le.trans ht) hg

/-- **The circuit size hierarchy.** If `s ≤ t`, `t` is positive, eventually
`s n + 2 n + 3 ≤ t n`, and infinitely often `1 ≤ s n < 2 ^ n / n`, then some language has circuits
of size `t` but not of size `s`. -/
theorem SIZE_ssubset {s t : ℕ → ℕ} (hst : s ≤ t) (ht : ∀ n, 1 ≤ t n)
    (hgap : ∀ᶠ n in atTop, s n + (2 * n + 3) ≤ t n)
    (hs : ∃ᶠ n in atTop, 1 ≤ s n ∧ (s n : ℝ) < 2 ^ n / n) : SIZE s ⊂ SIZE t := by
  classical
  obtain ⟨N, hN⟩ := Shannon.lt_complexity
  -- The lengths at which a function of complexity in `(s n, t n]` is used.
  have hgood : ∃ᶠ n in atTop, N ≤ n ∧ s n + (2 * n + 3) ≤ t n ∧ 1 ≤ s n ∧
      (s n : ℝ) < 2 ^ n / n :=
    (hs.and_eventually (hgap.and (eventually_ge_atTop N))).mono fun n ⟨h₁, h₂, h₃⟩ =>
      ⟨h₃, h₂, h₁⟩
  have hf : ∀ n, ∃ f : BooleanFunction n, complexity interpretation (single f) ≤ t n ∧
      ((N ≤ n ∧ s n + (2 * n + 3) ≤ t n ∧ 1 ≤ s n ∧ (s n : ℝ) < 2 ^ n / n) →
        s n < complexity interpretation (single f)) := by
    intro n
    by_cases hn : N ≤ n ∧ s n + (2 * n + 3) ≤ t n ∧ 1 ≤ s n ∧ (s n : ℝ) < 2 ^ n / n
    · obtain ⟨g, hg⟩ := hN n hn.1
      obtain ⟨f, hf₁, hf₂⟩ := exists_complexity_mem_Ioc hn.2.2.1 g
        (by exact_mod_cast hn.2.2.2.trans hg)
      exact ⟨f, hf₂.trans hn.2.1, fun _ => hf₁⟩
    · exact ⟨fun _ => false, (Synthesis.const false).complexity_le.trans (ht n),
        fun h => absurd h hn⟩
  choose f hft hfs using hf
  refine ⟨SIZE_mono hst, fun hsub => ?_⟩
  have hL : Language.ofSlices f ∈ SIZE t := fun n => by
    rw [Language.slice_ofSlices]
    exact hft n
  obtain ⟨n, hn⟩ := hgood.exists
  have := hsub hL n
  rw [Language.slice_ofSlices] at this
  exact absurd (hfs n hn) (not_lt.2 this)

/-- Polynomials are eventually below `2 ^ n / n`. -/
theorem eventually_pow_lt_two_pow_div (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (((n + 1) ^ k : ℕ) : ℝ) < 2 ^ n / n := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt (k + 1) (r := (2 : ℝ)) one_lt_two).comp
    (tendsto_add_atTop_nat 1)
  filter_upwards [h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_ge_atTop 1] with n hn hn1
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at hn
  rw [div_lt_iff₀ (by positivity), pow_succ 2 n] at hn
  rw [lt_div_iff₀ hn0]
  push_cast
  calc ((n : ℝ) + 1) ^ k * n ≤ ((n : ℝ) + 1) ^ k * (n + 1) := by gcongr; linarith
    _ = ((n : ℝ) + 1) ^ (k + 1) := (pow_succ _ k).symm
    _ < 1 / 2 * (2 ^ n * 2) := hn
    _ = 2 ^ n := by ring

/-- **The polynomial size hierarchy.** For `k ≥ 1`, circuits of size `(n + 1) ^ (k + 1)` decide
strictly more languages than circuits of size `(n + 1) ^ k`. -/
theorem SIZE_pow_ssubset {k : ℕ} (hk : 1 ≤ k) :
    SIZE (fun n => (n + 1) ^ k) ⊂ SIZE (fun n => (n + 1) ^ (k + 1)) := by
  refine SIZE_ssubset (fun n => Nat.pow_le_pow_right n.succ_pos k.le_succ)
    (fun n => Nat.one_le_pow _ _ n.succ_pos) ?_
    ((eventually_pow_lt_two_pow_div k).frequently.mono fun n hn =>
      ⟨Nat.one_le_pow _ _ n.succ_pos, hn⟩)
  filter_upwards [eventually_ge_atTop 3] with n hn
  have h1 : n + 1 ≤ (n + 1) ^ k := Nat.le_self_pow (by omega) _
  rw [pow_succ]
  nlinarith

end Cslib.Circuits.Boolean
