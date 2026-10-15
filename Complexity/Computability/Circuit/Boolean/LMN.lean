/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.HastadCounting
public import Complexity.Foundations.Data.BitString.FourierRestriction
import Complexity.Computability.DecisionTree.Fourier
import Complexity.Foundations.Combinatorics.Hypergeometric
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Linial–Mansour–Nisan theorem

A function computed by a small circuit of constant depth with unbounded fan-in has almost all of
its Fourier weight on small sets of coordinates [LinialMansourNisan1993],
[O'Donnell, Section 4.5][ODonnell2014]: for a circuit of depth `d` with `g` gates and `s ≥ 2`,
the weight on the sets of at least `k` coordinates is at most `2 g / 2 ^ s` once
`max 8 (2 s) n ≤ k ⌊n / (16 s + 1) ^ d⌋` (`sum_fourierCoeff_sq_le`), so for fixed `d` it is
`g 2 ^ (-Ω(k ^ (1 / (d + 1))))` (with an exponent weaker than Håstad's, as in
`Unbounded.two_pow_le_size_of_computes_parity`).

The proof draws a random set `J` of `ℓ = ⌊n / (16 s + 1) ^ d⌋` coordinates and fixes the others
to a random word `z`. A set `U` of at least `k` coordinates meets `J` in at least `s` of them for
at least half of the `J` (`Finset.two_mul_card_filter_card_inter_lt_le`), so the weight on such
`U` is at most twice the expected weight of the restriction on sets of at least `s` coordinates
(`BitString.expect_sum_fourierCoeff_piecewise_sq`). That is zero when the restriction has a
decision tree of depth below `s` (`DecisionTree.fourierCoeff_eq_zero_of_depth_lt`) and at most
one otherwise (Parseval), and the restriction is deep with probability at most `g / 2 ^ s`
(`Unbounded.two_pow_mul_card_filter_exists_not_shallow_le`).

## Main results

* `Cslib.Circuits.Boolean.sum_fourierCoeff_sq_le`: the Linial–Mansour–Nisan theorem.
* `Cslib.Circuits.Boolean.two_pow_le_two_mul_size_of_computes_parity`: parity needs many gates
  in constant depth, from LMN.
* `Cslib.Circuits.Boolean.Restriction.sum_card_filter_outside`: drawing a set `J` of `ℓ`
  coordinates and a word `z` and fixing the coordinates outside `J` to `z` draws every
  restriction with `ℓ` free bits `2 ^ ℓ` times.

## References

* [N. Linial, Y. Mansour, N. Nisan, *Constant depth circuits, Fourier transform, and
  learnability*][LinialMansourNisan1993]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset

variable {n : ℕ}

namespace Restriction

/-- The words agreeing with a restriction outside its free bits: `2 ^ ℓ` of them for `ℓ` free
bits. -/
private theorem card_filter_outside_eq (ρ : Restriction n) :
    (univ.filter fun z : BitString n => outside ρ.free z = ρ).card = 2 ^ ρ.free.card := by
  classical
  have h : (univ.filter fun z : BitString n => outside ρ.free z = ρ).card =
      Fintype.card (∀ i, {b : Bool // i ∉ ρ.free → some b = ρ i}) := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ((Equiv.subtypeEquivRight fun z => ?_).trans
      Equiv.subtypePiEquivPi)
    simp only [mem_filter, mem_univ, true_and, funext_iff, outside]
    refine forall_congr' fun i => ?_
    by_cases hi : i ∈ ρ.free
    · simp [hi, mem_free.1 hi]
    · simp [hi]
  rw [h, Fintype.card_pi]
  have hi (i : Fin n) : Fintype.card {b : Bool // i ∉ ρ.free → some b = ρ i} =
      if i ∈ ρ.free then 2 else 1 := by
    by_cases hif : i ∈ ρ.free
    · simp [hif]
    · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 fun h => hif (mem_free.2 h)
      simp only [hif, not_false_eq_true, forall_const, hc, Option.some.injEq, ↓reduceIte]
      exact Fintype.card_subtype_eq' c
  simp only [hi]
  rw [prod_ite, prod_const, prod_const_one, mul_one, filter_mem_eq_inter, univ_inter]

/-- **Drawing a free set and a word**: fixing the coordinates outside a set `J` of `ℓ`
coordinates to a word `z` draws every restriction with `ℓ` free bits `2 ^ ℓ` times. -/
theorem sum_card_filter_outside (Q : Restriction n → Prop) [DecidablePred Q] (ℓ : ℕ) :
    ∑ J ∈ (univ : Finset (Fin n)).powersetCard ℓ,
        (univ.filter fun z : BitString n => Q (outside J z)).card =
      2 ^ ℓ * ((withFree n ℓ).filter Q).card := by
  classical
  rw [← card_sigma, card_eq_sum_card_fiberwise (f := fun p => outside p.1 p.2)
    (t := (withFree n ℓ).filter Q) fun p hp => ?_]
  · rw [sum_congr rfl fun ρ hρ => ?_, sum_const, smul_eq_mul, mul_comm]
    have hfree : ρ.free.card = ℓ := mem_withFree.1 (mem_filter.1 hρ).1
    rw [← hfree, ← card_filter_outside_eq ρ]
    refine card_nbij' (fun p => p.2) (fun z => ⟨ρ.free, z⟩) (fun p hp => ?_) (fun z hz => ?_)
      (fun p hp => ?_) (fun z _ => rfl)
    · obtain ⟨-, hpρ⟩ := mem_filter.1 hp
      have h1 : p.1 = ρ.free := by rw [← hpρ, free_outside]
      exact mem_filter.2 ⟨mem_univ _, h1 ▸ hpρ⟩
    · have hz' : outside ρ.free z = ρ := (mem_filter.1 hz).2
      refine mem_filter.2 ⟨mem_sigma.2 ⟨mem_powersetCard.2 ⟨subset_univ _, rfl⟩, ?_⟩, hz'⟩
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      change Q (outside ρ.free z)
      rw [hz']
      exact (mem_filter.1 hρ).2
    · obtain ⟨-, hpρ⟩ := mem_filter.1 hp
      have h1 : p.1 = ρ.free := by rw [← hpρ, free_outside]
      exact Sigma.ext h1.symm HEq.rfl
  · obtain ⟨hJ, hz⟩ := mem_sigma.1 hp
    exact mem_filter.2 ⟨mem_withFree.2 (by rw [free_outside]; exact (mem_powersetCard.1 hJ).2),
      (mem_filter.1 hz).2⟩

end Restriction

open BitString
open scoped BigOperators

open scoped Classical in
/-- The weight of a restriction of a `±1`-valued function on sets of at least `s` coordinates is
zero if the restriction is `s`-shallow, and at most one otherwise. -/
private theorem sum_fourierCoeff_sq_le_ite (f : BooleanFunction n) (J : Finset (Fin n))
    (z : BitString n) (s : ℕ) :
    ∑ S with s ≤ #S, fourierCoeff (fun x => signVal (f (J.piecewise x z))) S ^ 2 ≤
      if Shallow s (Restriction.outside J z) f then 0 else 1 := by
  split_ifs with h
  · -- a decision tree of depth below `s` has no weight on sets of `s` coordinates
    obtain ⟨t, ht, hd⟩ := h.exists_tree
    refine (sum_eq_zero fun S hS => ?_).le
    have hfun : (fun x => signVal (f (J.piecewise x z))) = fun x => signVal (t.eval x) := by
      funext x
      rw [ht, Restriction.fill_outside]
    rw [hfun, DecisionTree.fourierCoeff_eq_zero_of_depth_lt signVal t
      (hd.trans_le (mem_filter.1 hS).2)]
    simp
  · rw [← sum_fourierCoeff_sq_signVal fun x => f (J.piecewise x z)]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _

open scoped Classical in
/-- For a fixed set `J` of free coordinates, the weight of a `±1`-valued function on the sets
meeting `J` in at least `s` coordinates is at most the fraction of the words `z` that leave `f`
deep when fixing the coordinates outside `J` to `z`. -/
private theorem sum_fourierCoeff_sq_le_card (f : BooleanFunction n) (J : Finset (Fin n)) (s : ℕ) :
    ∑ U with s ≤ #(U ∩ J), fourierCoeff (fun x => signVal (f x)) U ^ 2 ≤
      ((univ.filter fun z : BitString n => ¬ Shallow s (Restriction.outside J z) f).card : ℝ) /
        2 ^ n := by
  rw [← expect_sum_fourierCoeff_piecewise_sq (fun x => signVal (f x)) J s]
  calc 𝔼 z, ∑ S with s ≤ #S, fourierCoeff (fun x => signVal (f (J.piecewise x z))) S ^ 2
      ≤ 𝔼 z : BitString n, (if Shallow s (Restriction.outside J z) f then 0 else 1 : ℝ) :=
        expect_le_expect fun z _ => sum_fourierCoeff_sq_le_ite f J z s
    _ = _ := by
        rw [expect_eq_sum_div_card, sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul,
          mul_one]
        simp

open scoped Classical in
/-- **The Linial–Mansour–Nisan theorem.** Let `f` be computed by a circuit of negations and
unbounded fan-in conjunctions and disjunctions of depth `d` with `g` gates, let `s ≥ 2` with
`s (16 s + 1) ^ d ≤ n`, and let `ℓ = ⌊n / (16 s + 1) ^ d⌋`. Then the Fourier weight of `f`, read
as `±1`, on the sets of at least `k` coordinates is at most `2 g / 2 ^ s`, whenever
`max 8 (2 s) n ≤ k ℓ`. -/
theorem sum_fourierCoeff_sq_le {f : BooleanFunction n} {C : Circuit Unbounded.signature n 1}
    (hC : C.Computes Unbounded.interpretation (single f)) {s : ℕ} (hs : 2 ≤ s)
    (hn : s * (16 * s + 1) ^ C.depth ≤ n) {k : ℕ}
    (hk : max 8 (2 * s) * n ≤ k * (n / (16 * s + 1) ^ C.depth)) :
    ∑ U with k ≤ #U, fourierCoeff (fun x => signVal (f x)) U ^ 2 ≤ 2 * C.size / 2 ^ s := by
  set ℓ := n / (16 * s + 1) ^ C.depth
  set P := (univ : Finset (Fin n)).powersetCard ℓ
  set N := n.choose ℓ
  set a : Finset (Fin n) → ℝ := fun U => fourierCoeff (fun x => signVal (f x)) U ^ 2
  set bad := (Restriction.withFree n ℓ).filter fun ρ => ¬ Shallow s ρ f
  have ha : ∀ U, 0 ≤ a U := fun U => by simp only [a]; positivity
  have hℓn : ℓ ≤ n := Nat.div_le_self _ _
  have hsℓ : s ≤ ℓ := by
    rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by omega))]
    exact hn
  have hn0 : 0 < n := by omega
  have hN : 0 < N := Nat.choose_pos hℓn
  -- the counted stages: few restrictions leave the output deep
  have hbad : 2 ^ s * bad.card ≤ C.size * (Restriction.withFree n ℓ).card := by
    have h := Unbounded.two_pow_mul_card_filter_exists_not_shallow_le (p := C.program) hs hn
      C.depth le_rfl
    refine (Nat.mul_le_mul_left _ (card_le_card fun ρ hρ => ?_)).trans
      (h.trans (Nat.mul_le_mul_right _ ((card_filter_le _ _).trans (by simp))))
    obtain ⟨hρW, hdeep⟩ := mem_filter.1 hρ
    refine mem_filter.2 ⟨hρW, ?_⟩
    have hf : f = fun x => C.program.trace Unbounded.interpretation x (C.outputs 0) :=
      funext fun x => (congrFun (hC x) 0).symm
    rw [hf] at hdeep
    cases hw : C.outputs 0 with
    | input i =>
      rw [hw] at hdeep
      exact absurd (shallow_proj hs ρ i) hdeep
    | gate k =>
      rw [hw] at hdeep
      refine ⟨k, ?_, hdeep⟩
      have := C.outputDepths_le_depth 0
      simpa only [Circuit.outputDepths, Function.comp_apply, hw,
        Program.wireDepths_gateWire] using this
  -- the weight on sets meeting a random `J` in at least `s` coordinates
  have hupper : ∑ J ∈ P, ∑ U with s ≤ #(U ∩ J), a U ≤ (2 ^ ℓ * bad.card : ℝ) / 2 ^ n := by
    calc ∑ J ∈ P, ∑ U with s ≤ #(U ∩ J), a U
        ≤ ∑ J ∈ P, ((univ.filter fun z : BitString n =>
            ¬ Shallow s (Restriction.outside J z) f).card : ℝ) / 2 ^ n :=
          sum_le_sum fun J _ => sum_fourierCoeff_sq_le_card f J s
      _ = (2 ^ ℓ * bad.card : ℝ) / 2 ^ n := by
          rw [← sum_div]
          congr 1
          exact_mod_cast Restriction.sum_card_filter_outside (fun ρ => ¬ Shallow s ρ f) ℓ
  -- for the sets of at least `k` coordinates, at least half of the `J` meet them in `s`
  have hlower : (N : ℝ) / 2 * ∑ U with k ≤ #U, a U ≤ ∑ J ∈ P, ∑ U with s ≤ #(U ∩ J), a U := by
    have hswap : ∑ J ∈ P, ∑ U with s ≤ #(U ∩ J), a U =
        ∑ U, a U * (P.filter fun J => s ≤ #(U ∩ J)).card := by
      simp only [sum_filter]
      rw [sum_comm]
      refine sum_congr rfl fun U _ => ?_
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    rw [hswap, mul_sum, sum_filter]
    refine sum_le_sum fun U _ => ?_
    split_ifs with hU
    · have hcount := Finset.two_mul_card_filter_card_inter_lt_le (s := univ) (U := U) (ℓ := ℓ)
        (m := s) (subset_univ U) (by simpa using hℓn) (by simpa using hn0)
        (by
          have : 8 * n ≤ k * ℓ := (Nat.mul_le_mul_right _ (le_max_left _ _)).trans hk
          simpa using this.trans (Nat.mul_le_mul_right _ hU))
        (by
          have : 2 * s * n ≤ k * ℓ := (Nat.mul_le_mul_right _ (le_max_right _ _)).trans hk
          simpa using this.trans (Nat.mul_le_mul_right _ hU))
      have hcount' : 2 * (P.filter fun J => #(U ∩ J) < s).card ≤ N := by
        simpa [P, N] using hcount
      have hsplit := card_filter_add_card_filter_not (s := P) (fun J => s ≤ #(U ∩ J))
      have hPN : P.card = N := by simp [P, N]
      have hneg : (P.filter fun J => ¬ s ≤ #(U ∩ J)) = P.filter fun J => #(U ∩ J) < s := by
        congr 1
        ext J
        simp
      rw [hneg, hPN] at hsplit
      have h2 : (N : ℝ) ≤ 2 * (P.filter fun J => s ≤ #(U ∩ J)).card := by
        have : N ≤ 2 * (P.filter fun J => s ≤ #(U ∩ J)).card := by omega
        exact_mod_cast this
      nlinarith [ha U]
    · exact mul_nonneg (ha U) (Nat.cast_nonneg _)
  -- combine: `N / 2 · W ≤ 2 ^ ℓ #bad / 2 ^ n ≤ g N / 2 ^ s`
  have hW := hlower.trans hupper
  have hbadR : (2 ^ s : ℝ) * bad.card ≤ C.size * (N * 2 ^ (n - ℓ)) := by
    have := hbad
    rw [Restriction.card_withFree] at this
    exact_mod_cast this
  have h2n : (2 : ℝ) ^ ℓ * 2 ^ (n - ℓ) = 2 ^ n := by
    rw [← pow_add, Nat.add_sub_cancel' hℓn]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : (0 : ℝ) < 2 ^ s := by positivity
  have hpown : (0 : ℝ) < 2 ^ n := by positivity
  have hpowℓ : (0 : ℝ) < 2 ^ ℓ := by positivity
  rw [le_div_iff₀ hpow]
  have key : (N : ℝ) / 2 * (∑ U with k ≤ #U, a U) * 2 ^ s ≤ C.size * N := by
    have h1 : (N : ℝ) / 2 * (∑ U with k ≤ #U, a U) * 2 ^ n ≤ 2 ^ ℓ * bad.card := by
      rwa [le_div_iff₀ hpown] at hW
    have h3 : (2 : ℝ) ^ ℓ * bad.card * 2 ^ s ≤ 2 ^ ℓ * (C.size * (N * 2 ^ (n - ℓ))) := by
      nlinarith
    have h4 : (N : ℝ) / 2 * (∑ U with k ≤ #U, a U) * 2 ^ s * 2 ^ n ≤ C.size * N * 2 ^ n := by
      calc (N : ℝ) / 2 * (∑ U with k ≤ #U, a U) * 2 ^ s * 2 ^ n
          = (N / 2 * (∑ U with k ≤ #U, a U) * 2 ^ n) * 2 ^ s := by ring
        _ ≤ 2 ^ ℓ * bad.card * 2 ^ s := by gcongr
        _ ≤ 2 ^ ℓ * (C.size * (N * 2 ^ (n - ℓ))) := h3
        _ = C.size * N * (2 ^ ℓ * 2 ^ (n - ℓ)) := by ring
        _ = C.size * N * 2 ^ n := by rw [h2n]
    exact le_of_mul_le_mul_right h4 hpown
  nlinarith

/-- All the Fourier weight of parity, read as `±1`, is on the set of all coordinates. -/
theorem fourierCoeff_signVal_parity (U : Finset (Fin n)) :
    fourierCoeff (fun x => signVal (parity n x)) U = if U = univ then 1 else 0 := by
  have h : (fun x => signVal (parity n x)) = fun x => chi univ x :=
    funext fun x => (chi_eq_signVal_parityOn univ x).symm
  rw [h, fourierCoeff, expect_chi_mul_chi]
  exact if_congr eq_comm rfl rfl

/-- **Parity needs many gates in constant depth**, from the Linial–Mansour–Nisan theorem: all its
Fourier weight is on the set of all `n` coordinates, so a circuit of depth `d` for it has at least
`2 ^ (s - 1)` gates whenever `s ≥ 2`, `s (16 s + 1) ^ d ≤ n` and
`max 8 (2 s) ≤ ⌊n / (16 s + 1) ^ d⌋`. -/
theorem two_pow_le_two_mul_size_of_computes_parity {C : Circuit Unbounded.signature n 1}
    (hC : C.Computes Unbounded.interpretation (single (parity n))) {s : ℕ} (hs : 2 ≤ s)
    (hn : s * (16 * s + 1) ^ C.depth ≤ n) (hℓ : max 8 (2 * s) ≤ n / (16 * s + 1) ^ C.depth) :
    (2 : ℝ) ^ s ≤ 2 * C.size := by
  have h := sum_fourierCoeff_sq_le hC hs hn (k := n)
    (by rw [mul_comm]; exact Nat.mul_le_mul_left _ hℓ)
  have hone : ∑ U with n ≤ #U, fourierCoeff (fun x => signVal (parity n x)) U ^ 2 = 1 := by
    rw [sum_eq_single_of_mem univ (by simp) fun U hU hne => ?_]
    · simp [fourierCoeff_signVal_parity]
    · have : U = univ := eq_univ_of_card U (le_antisymm (card_le_univ U |>.trans_eq (by simp))
        (by simpa using (mem_filter.1 hU).2))
      exact absurd this hne
  rw [hone, le_div_iff₀ (by positivity)] at h
  linarith

end Cslib.Circuits.Boolean
