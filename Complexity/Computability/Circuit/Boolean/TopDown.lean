/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Unbounded
public import Complexity.Computability.Communication.TopDown.Parity
import Complexity.Computability.Circuit.Depth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Top-down lower bounds for circuits of constant depth

A circuit over the unbounded fan-in basis gives a Karchmer–Wigderson protocol in which the players
walk down from the output [Korten, Section 1.1][Korten2026]: at a conjunction the player whose
input makes it false names an argument wire false on that input, at a disjunction the player whose
input makes it true names an argument true on it, a negation exchanges the roles without a
message, and at an input the two inputs differ (`Unbounded.kwProtocol`,
`Unbounded.kwProtocol_solves`). The messages are wires, so a circuit of depth `d` with `g` gates on
`n` inputs gives a protocol with `d` messages from an alphabet of size `n + g`.

**Korten's theorem** [Korten, Theorem 3][Korten2026] bounds such protocols for parity, so for every
`d ≥ 2` there is `ε > 0` such that circuits of depth `d` for the parity of `n` bits have
`n + g > 2 ^ (ε n ^ (1 / (d - 1)))` for all large `n`
(`Unbounded.two_rpow_lt_add_size_of_computes_parity`). The exponent `1 / (d - 1)` is optimal, and
beats the `1 / (d + 1)` of `Unbounded.two_pow_le_size_of_computes_parity`, both with negations
counted in the depth.

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.kwProtocol`: the Karchmer–Wigderson protocol of a wire.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.kwProtocol_solves`: it solves the game of the wire.
* `Cslib.Circuits.Boolean.Unbounded.two_rpow_lt_add_size_of_computes_parity`: Korten's theorem.
* `Cslib.Circuits.Boolean.Unbounded.pow_lt_size_of_computes_parity`: at every fixed depth, parity
  needs more than `n ^ k` gates for large `n`.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Unbounded

open Cslib.Communication

variable {n g : ℕ}

/-- A wire among the arguments of gate `k` that is `b` on the input `x`, if there is one. -/
noncomputable def argWith (p : Program signature n g) (k : Fin g) (b : Bool) (x : BitString n) :
    Wire n g :=
  open scoped Classical in
  if h : ∃ a, p.trace interpretation x ((p.lines k).wires a) = b then
    (p.lines k).wires (Classical.choose h)
  else .gate k

theorem argWith_spec {p : Program signature n g} {k : Fin g} {b : Bool} {x : BitString n}
    (h : ∃ a, p.trace interpretation x ((p.lines k).wires a) = b) :
    ∃ a, argWith p k b x = (p.lines k).wires a ∧
      p.trace interpretation x ((p.lines k).wires a) = b := by
  refine ⟨Classical.choose h, ?_, Classical.choose_spec h⟩
  simp only [argWith, h, ↓reduceDIte]

/-- The first argument wire of gate `k`, or the input `i₀` if it has none. -/
def firstArg (p : Program signature n g) (i₀ : Fin n) (k : Fin g) : Wire n g :=
  if h : 0 < signature.Arity (p.lines k).op then (p.lines k).wires ⟨0, h⟩ else .input i₀

theorem wireDepths_firstArg_lt (p : Program signature n g) (i₀ : Fin n) (k : Fin g) :
    p.wireDepths (firstArg p i₀ k) < p.depths k := by
  unfold firstArg
  split_ifs
  · exact p.wireDepths_lines_lt k _
  · exact p.depths_pos k

theorem firstArg_of_op_eq_not {p : Program signature n g} {k : Fin g} (i₀ : Fin n)
    (h : (p.lines k).op = .not) : firstArg p i₀ k = (p.lines k).wires ⟨0, by simp [h]⟩ := by
  unfold firstArg
  split_ifs with h'
  · rfl
  · exact absurd (by simp [h]) h'

/-- The Karchmer–Wigderson protocol of the wire `w` with at most `d` messages: Alice holds an input
where `w` is `s`, Bob one where it is `!s`. At a conjunction the player whose input makes it false
names an argument false there, at a disjunction the player whose input makes it true names an
argument true there, and a negation exchanges the roles. The default coordinate `i₀` is the answer
when the budget runs out. -/
noncomputable def kwProtocol (p : Program signature n g) (i₀ : Fin n) (d : ℕ) (w : Wire n g)
    (s : Bool) : RoundProtocol (Fin n) (Wire n g) d :=
  match w with
  | .input i => .answer i
  | .gate k =>
    match (p.lines k).op with
    | .not => kwProtocol p i₀ d (firstArg p i₀ k) (!s)
    | .and _ =>
      match d with
      | 0 => .answer i₀
      | d + 1 => .speak s (argWith p k false) fun c => kwProtocol p i₀ d c s
    | .or _ =>
      match d with
      | 0 => .answer i₀
      | d + 1 => .speak (!s) (argWith p k true) fun c => kwProtocol p i₀ d c s
termination_by (d, p.wireDepths w)
decreasing_by
  · refine Prod.Lex.right _ ?_
    rw [Program.wireDepths_gateWire]
    exact wireDepths_firstArg_lt p i₀ k
  all_goals exact Prod.Lex.left _ _ (Nat.lt_succ_self _)

/-- A negation gate negates its argument. -/
theorem interpretation_of_op_eq_not {l : Line signature n g} (h : l.op = .not)
    (v : Wire n g → Bool) :
    interpretation l.op (fun a => v (l.wires a)) = !v (l.wires ⟨0, by simp [h]⟩) := by
  obtain ⟨op, ws⟩ := l
  simp only at h
  subst h
  rfl

/-- A conjunction gate is true when all its arguments are. -/
theorem interpretation_of_op_eq_and {l : Line signature n g} {m : ℕ} (h : l.op = .and m)
    (v : Wire n g → Bool) :
    interpretation l.op (fun a => v (l.wires a)) = true ↔ ∀ a, v (l.wires a) = true := by
  obtain ⟨op, ws⟩ := l
  simp only at h
  subst h
  simp

/-- A disjunction gate is true when one of its arguments is. -/
theorem interpretation_of_op_eq_or {l : Line signature n g} {m : ℕ} (h : l.op = .or m)
    (v : Wire n g → Bool) :
    interpretation l.op (fun a => v (l.wires a)) = true ↔ ∃ a, v (l.wires a) = true := by
  obtain ⟨op, ws⟩ := l
  simp only at h
  subst h
  simp

/-- **The protocol of a wire solves its game**: if the wire `w` has depth at most `d`, Alice's
input makes it `s` and Bob's makes it `!s`, the two inputs differ at the named coordinate. -/
theorem kwProtocol_solves (p : Program signature n g) (i₀ : Fin n) (d : ℕ) (w : Wire n g)
    (s : Bool) (hw : p.wireDepths w ≤ d) (x y : BitString n)
    (hx : p.trace interpretation x w = s) (hy : p.trace interpretation y w = !s) :
    x ((kwProtocol p i₀ d w s).run x y) ≠ y ((kwProtocol p i₀ d w s).run x y) := by
  match w with
  | .input i =>
    rw [kwProtocol.eq_def]
    dsimp only [RoundProtocol.run]
    simp only [Program.trace_input] at hx hy
    rw [hx, hy]
    cases s <;> decide
  | .gate k =>
    have hval (z : BitString n) : p.trace interpretation z (.gate k) =
        interpretation (p.lines k).op fun a => p.trace interpretation z ((p.lines k).wires a) :=
      (p.lines_eval interpretation z k).symm
    have hdk : p.depths k ≤ d := by rwa [Program.wireDepths_gateWire] at hw
    have hlt (a : Fin (signature.Arity (p.lines k).op)) :
        p.wireDepths ((p.lines k).wires a) < p.depths k := p.wireDepths_lines_lt k a
    rw [kwProtocol.eq_def]
    dsimp only
    split
    · rename_i hop
      have hx' := (hval x).symm.trans hx
      have hy' := (hval y).symm.trans hy
      rw [interpretation_of_op_eq_not hop] at hx' hy'
      have hfirst := firstArg_of_op_eq_not i₀ hop
      refine kwProtocol_solves p i₀ d _ (!s) ((wireDepths_firstArg_lt p i₀ k).le.trans hdk) x y
        ?_ ?_
      · rw [hfirst, ← hx', Bool.not_not]
      · rw [hfirst, ← hy', Bool.not_not]
    · rename_i m hop
      split
      · exact absurd hdk (by have := p.depths_pos k; omega)
      rename_i d
      -- the player whose input makes the conjunction false names a false argument
      have hfalse : ∀ {z z' : BitString n}, p.trace interpretation z (.gate k) = false →
          p.trace interpretation z' (.gate k) = true →
          ∃ a, argWith p k false z = (p.lines k).wires a ∧
            p.trace interpretation z ((p.lines k).wires a) = false ∧
            p.trace interpretation z' ((p.lines k).wires a) = true := by
        intro z z' hz hz'
        rw [hval, ← Bool.not_eq_true, interpretation_of_op_eq_and hop] at hz
        push Not at hz
        obtain ⟨a, ha, hza⟩ := argWith_spec (b := false) (by simpa using hz)
        rw [hval, interpretation_of_op_eq_and hop] at hz'
        exact ⟨a, ha, hza, hz' a⟩
      rw [RoundProtocol.run_speak]
      cases s
      · obtain ⟨a, ha, hxa, hya⟩ := hfalse hx (by simpa using hy)
        simp only [Bool.false_eq_true, ↓reduceIte, ha]
        exact kwProtocol_solves p i₀ d _ false (by have := hlt a; omega) x y hxa hya
      · obtain ⟨a, ha, hya, hxa⟩ := hfalse (by simpa using hy) hx
        simp only [↓reduceIte, ha]
        exact kwProtocol_solves p i₀ d _ true (by have := hlt a; omega) x y hxa
          (by simpa using hya)
    · rename_i m hop
      split
      · exact absurd hdk (by have := p.depths_pos k; omega)
      rename_i d
      -- the player whose input makes the disjunction true names a true argument
      have htrue : ∀ {z z' : BitString n}, p.trace interpretation z (.gate k) = true →
          p.trace interpretation z' (.gate k) = false →
          ∃ a, argWith p k true z = (p.lines k).wires a ∧
            p.trace interpretation z ((p.lines k).wires a) = true ∧
            p.trace interpretation z' ((p.lines k).wires a) = false := by
        intro z z' hz hz'
        rw [hval, interpretation_of_op_eq_or hop] at hz
        obtain ⟨a, ha, hza⟩ := argWith_spec (b := true) hz
        rw [hval, ← Bool.not_eq_true, interpretation_of_op_eq_or hop] at hz'
        push Not at hz'
        exact ⟨a, ha, hza, by simpa using hz' a⟩
      rw [RoundProtocol.run_speak]
      cases s
      · obtain ⟨a, ha, hya, hxa⟩ := htrue (by simpa using hy) hx
        simp only [Bool.not_false, ↓reduceIte, ha]
        exact kwProtocol_solves p i₀ d _ false (by have := hlt a; omega) x y hxa
          (by simpa using hya)
      · obtain ⟨a, ha, hxa, hya⟩ := htrue hx (by simpa using hy)
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ha]
        exact kwProtocol_solves p i₀ d _ true (by have := hlt a; omega) x y hxa
          (by simpa using hya)
termination_by (d, p.wireDepths w)
decreasing_by
  all_goals simp_wf
  · exact Prod.Lex.right _ (wireDepths_firstArg_lt p i₀ k)
  all_goals exact Prod.Lex.left _ _ (by omega)

/-- **A circuit gives a protocol**: a circuit of depth at most `d` computing `f` on `n ≥ 1` inputs
gives a Karchmer–Wigderson protocol for `f` with at most `d` messages from its wires. -/
theorem exists_roundProtocol_of_computes {C : Circuit signature n 1} {f : BitString n → Bool}
    (hC : C.Computes interpretation (single f)) (i₀ : Fin n) {d : ℕ} (hd : C.depth ≤ d) :
    ∃ P : RoundProtocol (Fin n) (Wire n C.size) d, P.SolvesKW f := by
  have hval (x : BitString n) : C.program.trace interpretation x (C.outputs 0) = f x :=
    congrFun (hC x) 0
  refine ⟨kwProtocol C.program i₀ d (C.outputs 0) false, fun x y hx hy => ?_⟩
  exact kwProtocol_solves C.program i₀ d _ false ((C.outputDepths_le_depth 0).trans hd) x y
    ((hval x).trans hx) ((hval y).trans hy)

universe u in
/-- **Korten's theorem** [Korten, Theorem 3][Korten2026]: for every depth `d ≥ 2` there is `ε > 0`
such that, for all large `n`, a circuit over the unbounded fan-in basis of depth at most `d`
computing the parity of `n` bits has `n + g > 2 ^ (ε n ^ (1 / (d - 1)))`, where `g` is its number of
gates. -/
theorem two_rpow_lt_add_size_of_computes_parity {d : ℕ} (hd : 2 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ C : Circuit signature n 1,
      C.Computes interpretation (single (parity n)) → C.depth ≤ d →
      (2 : ℝ) ^ (ε * (n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹)) < n + C.size := by
  obtain ⟨ε, hε, N, hN⟩ := parity_communication_lower_bound.{0} d hd
  refine ⟨ε, hε, max N 1, fun n hn C hC hCd => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  obtain ⟨P, hP⟩ := exists_roundProtocol_of_computes hC ⟨0, hn1⟩ hCd
  by_contra hle
  push Not at hle
  have hpos : (0 : ℝ) < n + C.size := by positivity
  have hcard : (Fintype.card (Wire n C.size) : ℝ) = n + C.size := by simp
  refine hN n (le_of_max_le_left hn) (Real.logb 2 (n + C.size))
    (Real.logb_nonneg one_lt_two
      (le_add_of_le_of_nonneg (by exact_mod_cast hn1) (Nat.cast_nonneg _)))
    (by rw [hcard, Real.rpow_logb two_pos (by norm_num) hpos])
    ((Real.logb_le_iff_le_rpow one_lt_two hpos).2 hle) P hP

/-- Polynomials are eventually below `2 ^ (ε n ^ r)` for `r, ε > 0`. -/
private theorem exists_add_pow_le_two_rpow {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (k : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n : ℝ) + n ^ k ≤ 2 ^ (ε * (n : ℝ) ^ r) := by
  have hD : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hc : 0 < ε * Real.log 2 / ((k + 2 : ℕ) : ℝ) := by positivity
  -- `log n = o(n ^ r)`
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop hr).def hc))
  refine ⟨max N 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_of_max_le_right hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hbound := hN n (le_of_max_le_left hn)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnpos.le _)] at hbound
  have hlog : ((k + 2 : ℕ) : ℝ) * Real.log n ≤ Real.log 2 * (ε * (n : ℝ) ^ r) := by
    have h := (le_abs_self _).trans hbound
    rw [div_mul_eq_mul_div, le_div_iff₀ hD] at h
    linarith
  -- `n + n ^ k ≤ 2 n ^ (k + 1) ≤ n ^ (k + 2)`
  have hnat : n + n ^ k ≤ n ^ (k + 2) := by
    have h1 : n ≤ n ^ (k + 1) := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < n) (show 1 ≤ k + 1 by omega)
    have h2 : n ^ k ≤ n ^ (k + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ k)
    calc n + n ^ k ≤ 2 * n ^ (k + 1) := by omega
      _ ≤ n * n ^ (k + 1) := Nat.mul_le_mul_right _ hn2
      _ = n ^ (k + 2) := by ring
  calc (n : ℝ) + n ^ k ≤ ((n ^ (k + 2) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = Real.exp (((k + 2 : ℕ) : ℝ) * Real.log n) := by
        rw [Real.exp_nat_mul, Real.exp_log hnpos]
        norm_cast
    _ ≤ Real.exp (Real.log 2 * (ε * (n : ℝ) ^ r)) := Real.exp_le_exp.2 hlog
    _ = 2 ^ (ε * (n : ℝ) ^ r) := (Real.rpow_def_of_pos two_pos _).symm

/-- **Parity is not in AC⁰, superpolynomially** [Korten2026]: for every depth `d` and exponent
`k`, circuits over the unbounded fan-in basis of depth at most `d` computing the parity of `n`
bits have more than `n ^ k` gates for all large `n`. -/
theorem pow_lt_size_of_computes_parity (d k : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ C : Circuit signature n 1,
      C.Computes interpretation (single (parity n)) → C.depth ≤ d → n ^ k < C.size := by
  obtain ⟨ε, hε, N, hN⟩ := two_rpow_lt_add_size_of_computes_parity (d := max d 2) (le_max_right _ _)
  obtain ⟨N', hN'⟩ := exists_add_pow_le_two_rpow
    (r := (((max d 2 - 1 : ℕ) : ℝ))⁻¹)
    (inv_pos.2 (Nat.cast_pos.2 (by omega))) hε k
  refine ⟨max N N', fun n hn C hC hCd => ?_⟩
  have h₁ := hN n (le_of_max_le_left hn) C hC (hCd.trans (le_max_left _ _))
  have h₂ := hN' n (le_of_max_le_right hn)
  have : (n : ℝ) ^ k < C.size := by linarith
  exact_mod_cast this

end Cslib.Circuits.Boolean.Unbounded
