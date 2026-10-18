/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Relation.RelatesWithinSteps
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Savitch's midpoint reachability with an explicit stack

Savitch's theorem rests on the midpoint recursion: `v` is reachable from `u` within `2 ^ (i + 1)`
steps exactly when some midpoint is reachable from `u` and reaches `v` within `2 ^ i` steps each
(`Relation.RelatesWithinSteps.two_pow_succ_iff`). On the words of a fixed width `w`,
`Cslib.Reachability.reach` is this recursion, with the midpoints in the order of a binary counter
(`Cslib.Reachability.words`, `Cslib.Reachability.next`), and it decides walks of at most `2 ^ i`
steps along the edges of an edge test (`Cslib.Reachability.reach_iff`).

Savitch's algorithm runs the recursion on an explicit stack. A frame records a call in progress:
its level, its endpoints, the midpoint being tried, which doubles as the counter of the midpoints,
and the half being tried. A register holds the pending call or the value just returned. One total
step function (`Cslib.Reachability.step`) handles the five cases: a call at level `0` tests for an
edge, a call at a higher level pushes a frame, a value returned into either half of a frame moves
to the other half, to the next midpoint or out of the frame, and an empty stack holding a value is
a fixed point. A call at level `i` returns within `Cslib.Reachability.callSteps w i` steps
(`Cslib.Reachability.exists_iterate_step_call`), so `2 ^ ((w + 2) * (d + 1)) - 1` steps compute the
recursion at level `d` (`Cslib.Reachability.savitch_eq`).

In the quantitative calculus of tidy computability (`Turing.MultiTapeTM.ComputableTidilyInO`), a
step takes time quadratic and space linear in its encoded state, plus the cost of the edge test on
the endpoints of a call (`Cslib.Reachability.computableTidilyInO_roundStep`). Every state of a run
from a call at level `d` holds at most `d` frames of size `O(d + w)`, so iterating the step with a
binary counter of the rounds takes space `O((d + 1) * (d + w + 1))` plus the parameter of the edge
test and the space of the edge test, and exponential time
(`Cslib.Reachability.computableTidilyInO_savitch`). With an edge test and inputs computable in
polynomial time, the space is polynomial (`Cslib.Reachability.exists_polyBounded_space_savitch`).

## Main definitions

* `Cslib.Reachability.words`, `Cslib.Reachability.next`: the words of a fixed width, in the order
  of the binary counter, and the counter.
* `Cslib.Reachability.reach`: the midpoint recursion.
* `Cslib.Reachability.Frame`, `Cslib.Reachability.Reg`, `Cslib.Reachability.State`,
  `Cslib.Reachability.step`: the stack machine.
* `Cslib.Reachability.savitch`: Savitch's algorithm, the machine run for
  `Cslib.Reachability.savitchSteps` steps.
* `Cslib.Reachability.encState`, `Cslib.Reachability.roundStep`, `Cslib.Reachability.encRound`:
  the encoded states, and the step carrying the parameter of the edge test.
* `Cslib.Reachability.edgeMax`: the cost of the edge test on the worst endpoints.

## Main results

* `Cslib.Reachability.reach_iff`, `Cslib.Reachability.savitch_iff`: the recursion and the
  algorithm decide walks of at most `2 ^ d` steps.
* `Cslib.Reachability.savitch_eq`: the machine computes the recursion.
* `Cslib.Reachability.computableTidilyInO_roundStep`: the time and space of a step.
* `Cslib.Reachability.computableTidilyInO_savitch`: the time and space of Savitch's algorithm.
* `Cslib.Reachability.exists_polyBounded_space_savitch`: Savitch's algorithm in polynomial space.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.5][Sipser2013]
* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Section 4.2][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Reachability

/-! ### Words of a fixed width and the binary counter -/

/-- The word of width `w` writing `n` in binary, least significant bit first; digits beyond the
`w`-th are dropped. -/
def word : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, n => decide (n % 2 = 1) :: word w (n / 2)

/-- All words of width `w`, in the order in which a binary counter of width `w` visits them,
starting from `List.replicate w false`: the words of `0, 1, …, 2 ^ w - 1`, least significant bit
first. -/
def words (w : ℕ) : List (List Bool) := (List.range (2 ^ w)).map (word w)

/-- The successor of a word in the binary counter of its width, least significant bit first, or
`none` on the word of all ones, where the counter overflows. -/
def next : List Bool → Option (List Bool)
  | [] => none
  | false :: u => some (true :: u)
  | true :: u => (next u).map (false :: ·)

/-- The word of `n` has width `w`. -/
@[simp]
theorem length_word (w n : ℕ) : (word w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [word, ih]

/-- The counter starts at the word of all zeros. -/
theorem word_zero (w : ℕ) : word w 0 = List.replicate w false := by
  induction w with
  | zero => rfl
  | succ w ih => simp [word, ih, List.replicate_succ]

/-- The number a word writes in binary, least significant bit first. -/
private def value : List Bool → ℕ
  | [] => 0
  | b :: u => b.toNat + 2 * value u

/-- The number of a word is below `2` to its width. -/
private theorem value_lt (u : List Bool) : value u < 2 ^ u.length := by
  induction u with
  | nil => simp [value]
  | cons b u ih =>
    cases b <;> simp only [value, List.length_cons, pow_succ, Bool.toNat_false, Bool.toNat_true] <;>
      omega

/-- Every word is the word of its number. -/
private theorem word_value (u : List Bool) : word u.length (value u) = u := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    have h₁ : (b.toNat + 2 * value u) / 2 = value u := by
      cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
    have h₂ : decide ((b.toNat + 2 * value u) % 2 = 1) = b := by cases b <;> simp
    simp only [List.length_cons, word, value, h₁, h₂, ih]

/-- There are `2 ^ w` words of width `w`. -/
@[simp]
theorem length_words (w : ℕ) : (words w).length = 2 ^ w := by simp [words]

/-- The `k`-th word of width `w` is the word of `k`. -/
theorem getElem_words (w k : ℕ) (hk : k < (words w).length) : (words w)[k] = word w k := by
  simp [words]

/-- `words w` holds exactly the words of width `w`. -/
theorem mem_words {w : ℕ} {u : List Bool} : u ∈ words w ↔ u.length = w := by
  constructor
  · simp only [words, List.mem_map]
    rintro ⟨n, -, rfl⟩
    exact length_word w n
  · rintro rfl
    exact List.mem_map.mpr ⟨value u, List.mem_range.mpr (value_lt u), word_value u⟩

/-- The successor of the word of `n` is the word of `n + 1`, unless `n + 1` overflows. -/
theorem next_word (w n : ℕ) (hn : n < 2 ^ w) :
    next (word w n) = if n + 1 < 2 ^ w then some (word w (n + 1)) else none := by
  induction w generalizing n with
  | zero =>
    obtain rfl : n = 0 := by simpa using hn
    rfl
  | succ w ih =>
    rw [pow_succ] at hn ⊢
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h₁ : (n + 1) / 2 = n / 2 := by omega
      have h₂ : n + 1 < 2 ^ w * 2 := by omega
      simp [word, h, h₁, h₂, next, Nat.add_mod]
    · have h₁ : (n + 1) / 2 = n / 2 + 1 := by omega
      have h₂ : n + 1 < 2 ^ w * 2 ↔ n / 2 + 1 < 2 ^ w := by omega
      have h₃ : (n + 1) % 2 = 0 := by omega
      simp only [word, h, decide_true, next, ih (n / 2) (by omega), h₁, h₂, h₃]
      split_ifs <;> rfl

/-- Along `words w`, the counter moves from each word to the next one and overflows on the last
one. -/
theorem next_getElem_words (w k : ℕ) (hk : k < (words w).length) :
    next (words w)[k] = (words w)[k + 1]? := by
  rw [getElem_words, next_word w k (by simpa using hk)]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h), getElem_words]
  · rw [List.getElem?_eq_none (by simpa using h)]

/-! ### Reachability by midpoints -/

/-- **Reachability within `2 ^ i` steps, by midpoints.** At level `0`, `v` is `u` or one edge
away; at level `i + 1`, some word `m` of width `w` is reachable from `u` and reaches `v` at level
`i`. This is the recursion of Savitch's theorem [Sipser, Theorem 8.5][Sipser2013]. -/
def reach (edge : List Bool → List Bool → Bool) (w : ℕ) : ℕ → List Bool → List Bool → Bool
  | 0, u, v => decide (u = v) || edge u v
  | i + 1, u, v => (words w).any fun m => reach edge w i u m && reach edge w i m v

/-- A walk along edges between words of width `w` stays among the words of width `w`. -/
theorem length_of_relatesWithinSteps {edge : List Bool → List Bool → Bool} {w n : ℕ}
    {u v : List Bool} (hu : u.length = w)
    (h : Relation.RelatesWithinSteps (fun a b => a.length = w ∧ b.length = w ∧ edge a b = true)
      u v n) : v.length = w := by
  induction h.reflTransGen with
  | refl => exact hu
  | tail _ hstep _ => exact hstep.2.1

/-- **The midpoint recursion decides walks of at most `2 ^ i` steps** between words of width `w`,
along the edges given by `edge` [Sipser, Theorem 8.5][Sipser2013]. -/
theorem reach_iff {edge : List Bool → List Bool → Bool} {w i : ℕ} {u v : List Bool}
    (hu : u.length = w) (hv : v.length = w) :
    reach edge w i u v = true ↔
      Relation.RelatesWithinSteps (fun a b => a.length = w ∧ b.length = w ∧ edge a b = true)
        u v (2 ^ i) := by
  induction i generalizing u v with
  | zero =>
    rw [pow_zero, Relation.RelatesWithinSteps.one_iff, Relation.reflGen_iff]
    simp only [reach, Bool.or_eq_true, decide_eq_true_eq, hu, hv, true_and]
    exact or_congr eq_comm Iff.rfl
  | succ i ih =>
    rw [Relation.RelatesWithinSteps.two_pow_succ_iff]
    simp only [reach, List.any_eq_true, Bool.and_eq_true, mem_words]
    constructor
    · rintro ⟨m, hm, h₁, h₂⟩
      exact ⟨m, (ih hu hm).mp h₁, (ih hm hv).mp h₂⟩
    · rintro ⟨m, h₁, h₂⟩
      have hm := length_of_relatesWithinSteps hu h₁
      exact ⟨m, hm, (ih hu hm).mpr h₁, (ih hm hv).mpr h₂⟩

/-! ### The stack machine -/

/-- A frame of the stack: the call at level `level + 1` from `src` to `dst`, while it tries the
midpoint `mid` with two calls at level `level`. -/
structure Frame where
  /-- The level of the two calls on the halves; the frame answers a call at level `level + 1`. -/
  level : ℕ
  /-- The source of the call. -/
  src : List Bool
  /-- The target of the call. -/
  dst : List Bool
  /-- The midpoint being tried, which is also the counter of the midpoints tried so far. -/
  mid : List Bool
  /-- `false` while the first half, from `src` to `mid`, is being tried; `true` while the second
  half, from `mid` to `dst`, is, once the first half has succeeded. -/
  phase : Bool
deriving Inhabited

/-- The register of the machine: a pending call, or the value of a call that has returned. -/
inductive Reg where
  /-- A call asking whether `dst` is reachable from `src` within `2 ^ level` steps. -/
  | call (level : ℕ) (src dst : List Bool)
  /-- A call has returned `value`. -/
  | ret (value : Bool)
deriving Inhabited

/-- The answer held by a register: the returned value, or `false` while a call is pending. -/
def Reg.answer : Reg → Bool
  | .call .. => false
  | .ret b => b

/-- The state of the machine: the stack of frames, top frame first, and the register. -/
structure State where
  /-- The frames of the calls in progress, the innermost first. -/
  stack : List Frame
  /-- The pending call or the returned value. -/
  reg : Reg
deriving Inhabited

/-- **One step of Savitch's machine**, with the edge test `edge` and midpoints of width `w`.
* A call at level `0` returns whether `v` is `u` or one edge away.
* A call at level `i + 1` pushes a frame and calls the first half with the first midpoint, the word
  of all zeros.
* An empty stack with a returned value is a fixed point: the value is the answer.
* A value `true` returned into the first half moves the frame to the second half; returned into the
  second half, the frame returns `true`.
* A value `false` returned into either half advances the midpoint by the binary counter; when the
  counter overflows, every midpoint has failed and the frame returns `false`. -/
def step (edge : List Bool → List Bool → Bool) (w : ℕ) : State → State
  | ⟨stack, .call 0 u v⟩ => ⟨stack, .ret (decide (u = v) || edge u v)⟩
  | ⟨stack, .call (i + 1) u v⟩ =>
    ⟨⟨i, u, v, List.replicate w false, false⟩ :: stack, .call i u (List.replicate w false)⟩
  | ⟨[], .ret b⟩ => ⟨[], .ret b⟩
  | ⟨f :: stack, .ret true⟩ =>
    if f.phase then ⟨stack, .ret true⟩
    else ⟨{ f with phase := true } :: stack, .call f.level f.mid f.dst⟩
  | ⟨f :: stack, .ret false⟩ =>
    match next f.mid with
    | none => ⟨stack, .ret false⟩
    | some m => ⟨{ f with mid := m, phase := false } :: stack, .call f.level f.src m⟩

/-- The number of steps the machine takes for a call at level `i`, with midpoints of width `w`:
one step to push the frame, and for each of the `2 ^ w` midpoints at most two calls at level `i`,
each followed by one step to take its value. -/
def callSteps (w : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => 1 + 2 * 2 ^ w * (callSteps w i + 1)

/-- The number of steps Savitch's machine runs for: `2 ^ ((w + 2) * (d + 1)) - 1`, at least
`callSteps w d`, and written in binary as `(w + 2) * (d + 1)` ones. -/
def savitchSteps (w d : ℕ) : ℕ := 2 ^ ((w + 2) * (d + 1)) - 1

/-- **Savitch's algorithm**: run the machine from the call at level `d` from `u` to `v` on the
empty stack for `savitchSteps w d` steps, and read the answer off the register. -/
def savitch (edge : List Bool → List Bool → Bool) (w d : ℕ) (u v : List Bool) : Bool :=
  ((step edge w)^[savitchSteps w d] ⟨[], .call d u v⟩).reg.answer

section Correctness

variable {edge : List Bool → List Bool → Bool} {w : ℕ}

/-- Runs compose. -/
private theorem iterate_trans {α : Type*} {f : α → α} {a b c : α} {m n : ℕ}
    (h₁ : f^[m] a = b) (h₂ : f^[n] b = c) : f^[n + m] a = c := by
  rw [Function.iterate_add_apply, h₁, h₂]

/-- The midpoints still to be tried by a frame that is at the `k`-th midpoint. -/
private theorem any_drop_words (P : List Bool → Bool) {k : ℕ} (hk : k < (words w).length) :
    ((words w).drop k).any P = (P (words w)[k] || ((words w).drop (k + 1)).any P) := by
  rw [List.drop_eq_getElem_cons hk, List.any_cons]

/-- The run of a frame at level `i + 1`, from `u` to `v`, at the `k`-th midpoint: if a `false`
returned into the frame is processed within `2 * j * (c + 1) + 1` steps, the frame returns its
value, in either phase. -/
private theorem run_frame {i c : ℕ} {u v : List Bool} {stack : List Frame}
    (ih : ∀ u v (stack : List Frame), ∃ T ≤ c,
      (step edge w)^[T] ⟨stack, .call i u v⟩ = ⟨stack, .ret (reach edge w i u v)⟩)
    {j k : ℕ} (hk : k < (words w).length)
    (hadv : ∀ ph, ∃ T ≤ 2 * j * (c + 1) + 1,
      (step edge w)^[T] ⟨⟨i, u, v, (words w)[k], ph⟩ :: stack, .ret false⟩ =
        ⟨stack, .ret (((words w).drop (k + 1)).any
          fun m => reach edge w i u m && reach edge w i m v)⟩) :
    (∃ T ≤ (2 * j + 2) * (c + 1),
      (step edge w)^[T] ⟨⟨i, u, v, (words w)[k], false⟩ :: stack, .call i u (words w)[k]⟩ =
        ⟨stack, .ret (((words w).drop k).any
          fun m => reach edge w i u m && reach edge w i m v)⟩) ∧
    (reach edge w i u (words w)[k] = true → ∃ T ≤ (2 * j + 1) * (c + 1),
      (step edge w)^[T] ⟨⟨i, u, v, (words w)[k], true⟩ :: stack, .call i (words w)[k] v⟩ =
        ⟨stack, .ret (((words w).drop k).any
          fun m => reach edge w i u m && reach edge w i m v)⟩) := by
  rw [any_drop_words _ hk]
  set m := (words w)[k]
  -- the second half
  have hsecond : reach edge w i u m = true → ∃ T ≤ (2 * j + 1) * (c + 1),
      (step edge w)^[T] ⟨⟨i, u, v, m, true⟩ :: stack, .call i m v⟩ =
        ⟨stack, .ret ((reach edge w i u m && reach edge w i m v) ||
          ((words w).drop (k + 1)).any fun m => reach edge w i u m && reach edge w i m v)⟩ := by
    intro hum
    obtain ⟨T₁, hT₁, h₁⟩ := ih m v (⟨i, u, v, m, true⟩ :: stack)
    rw [hum, Bool.true_and]
    cases hmv : reach edge w i m v
    · obtain ⟨T₂, hT₂, h₂⟩ := hadv true
      rw [hmv] at h₁
      exact ⟨T₂ + T₁, by nlinarith, iterate_trans h₁ h₂⟩
    · rw [hmv] at h₁
      exact ⟨1 + T₁, by nlinarith, iterate_trans h₁ rfl⟩
  refine ⟨?_, hsecond⟩
  -- the first half
  obtain ⟨T₁, hT₁, h₁⟩ := ih u m (⟨i, u, v, m, false⟩ :: stack)
  cases hum : reach edge w i u m
  · obtain ⟨T₂, hT₂, h₂⟩ := hadv false
    rw [hum] at h₁
    rw [Bool.false_and, Bool.false_or]
    exact ⟨T₂ + T₁, by nlinarith, iterate_trans h₁ h₂⟩
  · obtain ⟨T₂, hT₂, h₂⟩ := hsecond hum
    rw [hum] at h₁ h₂
    exact ⟨T₂ + (1 + T₁), by nlinarith, iterate_trans (iterate_trans h₁ rfl) h₂⟩

/-- The runs of a frame, by induction on the number `j` of midpoints after the current one. -/
private theorem run_frames {i c : ℕ} {u v : List Bool} {stack : List Frame}
    (ih : ∀ u v (stack : List Frame), ∃ T ≤ c,
      (step edge w)^[T] ⟨stack, .call i u v⟩ = ⟨stack, .ret (reach edge w i u v)⟩) :
    ∀ j k (hk : k + j + 1 = (words w).length),
    ∃ T ≤ (2 * j + 2) * (c + 1),
      (step edge w)^[T] ⟨⟨i, u, v, (words w)[k], false⟩ :: stack, .call i u (words w)[k]⟩ =
        ⟨stack, .ret (((words w).drop k).any
          fun m => reach edge w i u m && reach edge w i m v)⟩ := by
  intro j
  induction j with
  | zero =>
    intro k hk
    refine (run_frame ih (by omega) fun ph => ⟨1, by omega, ?_⟩).1
    have hnext := next_getElem_words w k (by omega)
    rw [List.getElem?_eq_none (by omega)] at hnext
    rw [List.drop_eq_nil_of_le (by omega)]
    simp [step, hnext]
  | succ j ih' =>
    intro k hk
    refine (run_frame ih (by omega) fun ph => ?_).1
    obtain ⟨T, hT, h⟩ := ih' (k + 1) (by omega)
    have hnext := next_getElem_words w k (by omega)
    rw [List.getElem?_eq_getElem (by omega)] at hnext
    refine ⟨T + 1, by nlinarith, iterate_trans ?_ h⟩
    simp [step, hnext]

/-- **Every call returns its value**: from a call at level `i`, the machine returns
`reach edge w i u v` to the same stack within `callSteps w i` steps. -/
theorem exists_iterate_step_call (i : ℕ) (u v : List Bool) (stack : List Frame) :
    ∃ T ≤ callSteps w i,
      (step edge w)^[T] ⟨stack, .call i u v⟩ = ⟨stack, .ret (reach edge w i u v)⟩ := by
  induction i generalizing u v stack with
  | zero => exact ⟨1, le_rfl, rfl⟩
  | succ i ih =>
    have hlen : 0 + (2 ^ w - 1) + 1 = (words w).length := by
      have := Nat.one_le_two_pow (n := w)
      simp only [length_words]
      omega
    obtain ⟨T, hT, h⟩ := run_frames (u := u) (v := v) (stack := stack) ih _ 0 hlen
    have h₀ : (words w)[0]'(by omega) = List.replicate w false := by
      rw [getElem_words, word_zero]
    rw [h₀, List.drop_zero] at h
    refine ⟨T + 1, ?_, iterate_trans rfl h⟩
    have := Nat.one_le_two_pow (n := w)
    have : (2 * (2 ^ w - 1) + 2) = 2 * 2 ^ w := by omega
    simp only [callSteps]
    rw [this] at hT
    omega

/-- An empty stack with a returned value is a fixed point. -/
theorem iterate_step_ret_nil (b : Bool) (n : ℕ) :
    (step edge w)^[n] ⟨[], .ret b⟩ = ⟨[], .ret b⟩ :=
  Function.iterate_fixed rfl n

/-- The number of steps of a call at level `i` is below `2 ^ ((w + 2) * i + 1)`. -/
theorem callSteps_add_one_le (w i : ℕ) : callSteps w i + 1 ≤ 2 ^ ((w + 2) * i + 1) := by
  induction i with
  | zero => simp [callSteps]
  | succ i ih =>
    have h₁ : 2 ^ ((w + 2) * (i + 1) + 1) = 2 * 2 ^ w * 2 * 2 ^ ((w + 2) * i + 1) := by
      rw [← pow_succ', ← pow_succ, ← pow_add]
      ring_nf
    have h₂ : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    have h₃ := Nat.mul_le_mul_left (2 * 2 ^ w) ih
    simp only [callSteps, h₁]
    nlinarith

/-- Savitch's machine runs for long enough to return from the call at level `d`. -/
theorem callSteps_le_savitchSteps (w d : ℕ) : callSteps w d ≤ savitchSteps w d := by
  have h₁ := callSteps_add_one_le w d
  have h₂ : 2 ^ ((w + 2) * d + 1) ≤ 2 ^ ((w + 2) * (d + 1)) :=
    Nat.pow_le_pow_right two_pos (by nlinarith)
  simp only [savitchSteps]
  omega

/-- **Savitch's machine computes the midpoint recursion.** -/
theorem savitch_eq (edge : List Bool → List Bool → Bool) (w d : ℕ) (u v : List Bool) :
    savitch edge w d u v = reach edge w d u v := by
  obtain ⟨T, hT, h⟩ := exists_iterate_step_call (edge := edge) (w := w) d u v []
  have hN := (callSteps_le_savitchSteps w d)
  rw [savitch, show savitchSteps w d = savitchSteps w d - T + T by omega,
    Function.iterate_add_apply, h, iterate_step_ret_nil]
  rfl

/-- **Savitch's algorithm decides walks of at most `2 ^ d` steps** between words of width `w`
[Sipser, Theorem 8.5][Sipser2013]. -/
theorem savitch_iff {edge : List Bool → List Bool → Bool} {w d : ℕ} {u v : List Bool}
    (hu : u.length = w) (hv : v.length = w) :
    savitch edge w d u v = true ↔
      Relation.RelatesWithinSteps (fun a b => a.length = w ∧ b.length = w ∧ edge a b = true)
        u v (2 ^ d) := by
  rw [savitch_eq, reach_iff hu hv]

end Correctness

/-! ### Encodings -/

open Turing.MultiTapeTM

/-- The fields of a frame. -/
def Frame.fields (f : Frame) : ℕ × List Bool × List Bool × List Bool × Bool :=
  (f.level, f.src, f.dst, f.mid, f.phase)

/-- The encoding of the fields of a frame: the level in unary, the words as themselves. -/
abbrev encFrameFields : ℕ × List Bool × List Bool × List Bool × Bool ↪ List Bool :=
  encPair encUnary (encPair encBits (encPair encBits (encPair encBits encBool)))

/-- Frames encoded by their fields. -/
def encFrame : Frame ↪ List Bool :=
  ⟨fun f => encFrameFields f.fields, fun f g h => by
    obtain ⟨⟩ := f
    obtain ⟨⟩ := g
    simpa [Frame.fields] using encFrameFields.injective h⟩

/-- The register as a pending call, if any, and the returned value, `false` during a call. -/
def Reg.toPair : Reg → Option (ℕ × List Bool × List Bool) × Bool
  | .call i u v => (some (i, u, v), false)
  | .ret b => (none, b)

/-- The encoding of the arguments of a call: the level in unary, the words as themselves. -/
abbrev encCall : ℕ × List Bool × List Bool ↪ List Bool := encPair encUnary (encPair encBits encBits)

/-- Registers encoded by `Reg.toPair`. -/
def encReg : Reg ↪ List Bool :=
  ⟨fun r => encPair (encOption encCall) encBool r.toPair, fun r r' h => by
    have := (encPair (encOption encCall) encBool).injective h
    cases r <;> cases r' <;> simp_all [Reg.toPair]⟩

/-- States encoded as the list of their frames followed by their register. -/
def encState : State ↪ List Bool :=
  ⟨fun s => encPair (encList encFrame) encReg (s.stack, s.reg), fun s s' h => by
    obtain ⟨⟩ := s
    obtain ⟨⟩ := s'
    simpa using (encPair (encList encFrame) encReg).injective h⟩

/-! ### The step in linear time, apart from the edge test -/

section Certificates

open ComputableTidilyInDegree

/-- The binary successor, wrapping around on the word of all ones. -/
private def incr : List Bool → List Bool
  | [] => []
  | false :: u => true :: u
  | true :: u => false :: incr u

/-- The counter overflows on the word of all ones, and otherwise increments. -/
private theorem next_eq (u : List Bool) : next u = if u.all id then none else some (incr u) := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    cases b
    · rfl
    · simp only [next, ih, List.all_cons, id, Bool.true_and]
      split_ifs <;> rfl

/-- The transducer of `incr`, with the carry as its state. -/
@[simps q₀ step final]
private def incrT : Transducer Bool Bool where
  q₀ := true
  step c b := (c && b, [c ^^ b])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

/-- The transducer of `incr` increments with a carry. -/
private theorem incrT_run (c : Bool) (u : List Bool) :
    incrT.run c u = if c then incr u else u := by
  induction u generalizing c with
  | nil => cases c <;> rfl
  | cons b u ih => cases c <;> cases b <;> simp [incrT_step, incr, ih]

/-- The transducer testing whether all bits are ones. -/
@[simps q₀ step final]
private def allT : Transducer Bool Bool where
  q₀ := true
  step a b := (a && b, [])
  final a := [a]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

/-- The transducer `allT` tests whether all bits are ones. -/
private theorem allT_run (a : Bool) (u : List Bool) : allT.run a u = [a && u.all id] := by
  induction u generalizing a with
  | nil => simp [allT_final]
  | cons b u ih => simp [allT_step, ih, Bool.and_assoc]

/-- The transducer writing a zero for every symbol. -/
@[simps q₀ step final]
private def zeroT : Transducer Bool Unit where
  q₀ := ()
  step _ _ := ((), [false])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

/-- The transducer `zeroT` writes the word of all zeros of the same width. -/
private theorem zeroT_run (u : List Bool) : zeroT.run () u = List.replicate u.length false := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [zeroT_step, ih, List.replicate_succ]

/-- The increment, in linear time. -/
@[local fun_prop] private lemma incr_deg : ComputableTidilyInDegree incr encBits encBits 1 1 :=
  of_linear (incrT.computableTidilyInLinearTimeAndSpace fun u => by simp [incrT_run])

/-- The test for the word of all ones, in linear time. -/
@[local fun_prop] private lemma all_deg :
    ComputableTidilyInDegree (fun u : List Bool => u.all id) encBits encBool 1 1 :=
  of_linear (allT.computableTidilyInLinearTimeAndSpace fun u => by simp [allT_run])

/-- The word of all zeros of width `w`, from `w` in unary, in linear time. -/
@[local fun_prop] private lemma replicate_deg :
    ComputableTidilyInDegree (fun n => List.replicate n false) encUnary encBits 1 1 :=
  of_linear (zeroT.computableTidilyInLinearTimeAndSpace fun n => by simp [zeroT_run])

/-- Conjunction. -/
@[local fun_prop] private lemma and_deg :
    ComputableTidilyInDegree (fun p : Bool × Bool => p.1 && p.2) (encPair encBool encBool) encBool
      1 0 :=
  of_finite _

/-- Disjunction. -/
@[local fun_prop] private lemma or_deg :
    ComputableTidilyInDegree (fun p : Bool × Bool => p.1 || p.2) (encPair encBool encBool) encBool
      1 0 :=
  of_finite _

/-- Negation. -/
@[local fun_prop] private lemma not_deg :
    ComputableTidilyInDegree (fun b : Bool => !b) encBool encBool 1 0 :=
  of_finite _

/-- The predecessor in unary. -/
@[local fun_prop] private lemma pred_deg :
    ComputableTidilyInDegree (fun n : ℕ => n - 1) encUnary encUnary 1 1 :=
  unary_pred

/-- Whether a call is pending. -/
@[local fun_prop] private lemma isSome_deg :
    ComputableTidilyInDegree (fun o : Option (ℕ × List Bool × List Bool) => o.isSome)
      (encOption encCall) encBool 1 0 :=
  isSome encCall

/-- The stack of a state. -/
@[local fun_prop] private lemma stack_deg :
    ComputableTidilyInDegree State.stack encState (encList encFrame) 1 1 :=
  of_linear (.of_unframe fun s => by simp [encState])

/-- The register of a state. -/
@[local fun_prop] private lemma reg_deg : ComputableTidilyInDegree State.reg encState encReg 1 1 :=
  of_linear (.of_dropFrame fun s => by simp [encState])

/-- The register as a pair, the identity on encoded values. -/
@[local fun_prop] private lemma toPair_deg :
    ComputableTidilyInDegree Reg.toPair encReg (encPair (encOption encCall) encBool) 1 1 :=
  of_eq fun _ => rfl

/-- The fields of a frame, the identity on encoded values. -/
private lemma fields_deg : ComputableTidilyInDegree Frame.fields encFrame encFrameFields 1 1 :=
  of_eq fun _ => rfl

/-- The level of a frame. -/
@[local fun_prop] private lemma level_deg :
    ComputableTidilyInDegree Frame.level encFrame encUnary 1 1 :=
  fields_deg.fst'

/-- The source of a frame. -/
@[local fun_prop] private lemma src_deg : ComputableTidilyInDegree Frame.src encFrame encBits 1 1 :=
  fields_deg.snd'.fst'.mono

/-- The target of a frame. -/
@[local fun_prop] private lemma dst_deg : ComputableTidilyInDegree Frame.dst encFrame encBits 1 1 :=
  fields_deg.snd'.snd'.fst'.mono

/-- The midpoint of a frame. -/
@[local fun_prop] private lemma mid_deg : ComputableTidilyInDegree Frame.mid encFrame encBits 1 1 :=
  fields_deg.snd'.snd'.snd'.fst'.mono

/-- The phase of a frame. -/
@[local fun_prop] private lemma phase_deg :
    ComputableTidilyInDegree Frame.phase encFrame encBool 1 1 :=
  fields_deg.snd'.snd'.snd'.snd'.mono

/-- A state from its stack and register, the identity on encoded values. -/
@[local fun_prop] private lemma stateMk_deg :
    ComputableTidilyInDegree (fun p : List Frame × Reg => State.mk p.1 p.2)
      (encPair (encList encFrame) encReg) encState 1 1 :=
  of_eq fun _ => rfl

/-- A frame from its fields, the identity on encoded values. -/
@[local fun_prop] private lemma frameMk_deg :
    ComputableTidilyInDegree
      (fun p : ℕ × List Bool × List Bool × List Bool × Bool =>
        Frame.mk p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) encFrameFields encFrame 1 1 :=
  of_eq fun _ => rfl

/-- A pending call from its arguments. -/
@[local fun_prop] private lemma call_deg :
    ComputableTidilyInDegree (fun c : ℕ × List Bool × List Bool => Reg.call c.1 c.2.1 c.2.2)
      encCall encReg 1 1 :=
  (((optionSome (enc₁ := encCall)).prod (const false)).mono).of_enc_eq fun _ => rfl

/-- A returned value. -/
@[local fun_prop] private lemma ret_deg : ComputableTidilyInDegree Reg.ret encBool encReg 1 1 :=
  (((const (encMid := encOption encCall) none).prod (of_eq fun _ => rfl)).mono).of_enc_eq
    fun _ => rfl

/-- The arguments of the pending call, if any. -/
private def State.args (s : State) : ℕ × List Bool × List Bool := s.reg.toPair.1.getD default

/-- The top frame, if any. -/
private def State.top (s : State) : Frame := s.stack.headD default

/-- The arguments of the pending call. -/
@[local fun_prop] private lemma args_deg :
    ComputableTidilyInDegree State.args encState encCall 1 1 := by
  unfold State.args
  fun_prop (disch := first | apply le_refl | lia)

/-- The top frame. -/
@[local fun_prop] private lemma top_deg :
    ComputableTidilyInDegree State.top encState encFrame 1 1 := by
  unfold State.top
  fun_prop (disch := first | apply le_refl | lia)

/-- Whether the register holds a call at level `0`. -/
private def State.isBase (s : State) : Bool := s.reg.toPair.1.isSome && decide (s.args.1 = 0)

/-- The step on a call at level `0`. -/
private def baseStep (edge : List Bool → List Bool → Bool) (s : State) : State :=
  ⟨s.stack, .ret (decide (s.args.2.1 = s.args.2.2) || edge s.args.2.1 s.args.2.2)⟩

/-- The step on the other states, as a case distinction on Boolean tests. -/
private def restStep (w : ℕ) (s : State) : State :=
  if s.reg.toPair.1.isSome then
    ⟨⟨s.args.1 - 1, s.args.2.1, s.args.2.2, List.replicate w false, false⟩ :: s.stack,
      .call (s.args.1 - 1) s.args.2.1 (List.replicate w false)⟩
  else if s.stack.isEmpty then s
  else if s.reg.toPair.2 && !s.top.phase then
    ⟨{ s.top with phase := true } :: s.stack.tail, .call s.top.level s.top.mid s.top.dst⟩
  else if s.reg.toPair.2 || s.top.mid.all id then ⟨s.stack.tail, s.reg⟩
  else
    ⟨{ s.top with mid := incr s.top.mid, phase := false } :: s.stack.tail,
      .call s.top.level s.top.src (incr s.top.mid)⟩

/-- The step, as a case distinction on whether the register holds a call at level `0`. -/
private theorem step_eq (edge : List Bool → List Bool → Bool) (w : ℕ) (s : State) :
    step edge w s = if s.isBase then baseStep edge s else restStep w s := by
  obtain ⟨stack, (⟨_ | i, u, v⟩ | b)⟩ := s
  · rfl
  · rfl
  · have hb : State.isBase ⟨stack, .ret b⟩ = false := rfl
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rcases stack with _ | ⟨⟨i, u, v, m, ph⟩, stack⟩
    · rfl
    · cases b <;> cases ph <;> cases hm : m.all id <;>
        simp [step, restStep, next_eq, hm, State.top, Reg.toPair]

/-- The step on the states other than calls at level `0`, in linear time. -/
@[local fun_prop] private lemma restStep_deg :
    ComputableTidilyInDegree (fun r : ℕ × State => restStep r.1 r.2) (encPair encUnary encState)
      encState 1 1 := by
  unfold restStep
  fun_prop (disch := first | apply le_refl | lia)

/-- The test for a call at level `0`, in linear time. -/
@[local fun_prop] private lemma isBase_deg :
    ComputableTidilyInDegree State.isBase encState encBool 1 1 := by
  have h₁ : ComputableTidilyInDegree (fun s : State => s.reg.toPair.1.isSome) encState encBool
      1 1 := by
    fun_prop (disch := first | apply le_refl | lia)
  have h₂ : ComputableTidilyInDegree (fun s : State => s.args.1) encState encUnary 1 1 := by
    fun_prop (disch := first | apply le_refl | lia)
  exact (and_deg.comp (h₁.prod (unary_isZero.comp h₂))).mono

/-! ### Sizes of encoded states -/

/-- The length of an encoded frame. -/
theorem length_encFrame (f : Frame) :
    (encFrame f).length =
      2 * f.level + 2 * f.src.length + 2 * f.dst.length + 2 * f.mid.length + 5 := by
  change (encFrameFields f.fields).length = _
  simp only [Frame.fields, length_encPair, encUnary_apply, encBits_apply, encBool_apply,
    List.length_replicate, List.length_singleton]
  omega

/-- The length of an encoded pending call. -/
theorem length_encReg_call (i : ℕ) (u v : List Bool) :
    (encReg (.call i u v)).length = 4 * i + 4 * u.length + 2 * v.length + 8 := by
  change (encPair (encOption encCall) encBool (some (i, u, v), false)).length = _
  simp only [length_encPair, encOption_some, List.length_cons, encUnary_apply, encBits_apply,
    encBool_apply, List.length_replicate, List.length_nil]
  omega

/-- The length of an encoded returned value. -/
theorem length_encReg_ret (b : Bool) : (encReg (.ret b)).length = 2 := rfl

/-- The length of an encoded state. -/
theorem length_encState (s : State) :
    (encState s).length = 2 * (encList encFrame s.stack).length + 1 + (encReg s.reg).length := by
  simp [encState]

/-! ### A step carrying the parameter of the edge test -/

variable {π : Type} {encP : π ↪ List Bool}

/-- A round of the iteration of Savitch's algorithm: a step of the machine for the edge test
`edge q.1.1` and the width `q.1.2`, keeping both. -/
def roundStep (edge : π → List Bool → List Bool → Bool) (q : (π × ℕ) × State) : (π × ℕ) × State :=
  (q.1, step (edge q.1.1) q.1.2 q.2)

/-- The encoding of the states of the iteration, with the width in unary. -/
abbrev encRound (encP : π ↪ List Bool) : (π × ℕ) × State ↪ List Bool :=
  encPair (encPair encP encUnary) encState

/-- The cost `T` of the edge test, with the parameter `p`, on the endpoints of the pending call, if
any. -/
def Reg.edgeCost (T : π × List Bool × List Bool → ℕ) (p : π) : Reg → ℕ
  | .call _ u v => T (p, u, v)
  | .ret _ => 0

/-- A round, as a case distinction on whether the register holds a call at level `0`. -/
private theorem roundStep_eq (edge : π → List Bool → List Bool → Bool) (q : (π × ℕ) × State) :
    roundStep edge q = if q.2.isBase then (q.1, baseStep (edge q.1.1) q.2)
      else (q.1, restStep q.1.2 q.2) := by
  rw [roundStep, step_eq]
  split_ifs <;> rfl

/-- A register passing the test for a call at level `0` holds a call. -/
private theorem eq_call_of_isBase {s : State} (h : s.isBase = true) :
    s.reg = .call s.args.1 s.args.2.1 s.args.2.2 := by
  obtain ⟨stack, (⟨i, u, v⟩ | b)⟩ := s
  · rfl
  · simp [State.isBase, Reg.toPair] at h

/-- **A round within the time and space of the edge test, plus quadratic time and linear
space.** A call at level `0` compares its endpoints, in quadratic time, and runs the edge test on
them; the other cases copy and rearrange the encoded state, in linear time. -/
theorem computableTidilyInO_roundStep {edge : π → List Bool → List Bool → Bool}
    {Te Se : π × List Bool × List Bool → ℕ}
    (hedge : ComputableTidilyInO (fun q : π × List Bool × List Bool => edge q.1 q.2.1 q.2.2)
      (encPair encP (encPair encBits encBits)) encBool Te Se) :
    ComputableTidilyInO (roundStep edge) (encRound encP) (encRound encP)
      (fun q => ((encRound encP q).length + 1) ^ 2 + q.2.reg.edgeCost Te q.1.1)
      (fun q => (encRound encP q).length + q.2.reg.edgeCost Se q.1.1) := by
  have hc : ComputableTidilyInDegree (fun q : (π × ℕ) × State => q.2.isBase) (encRound encP)
      encBool 1 1 := by
    fun_prop (disch := first | apply le_refl | lia)
  have hrest : ComputableTidilyInDegree (fun q : (π × ℕ) × State => (q.1, restStep q.1.2 q.2))
      (encRound encP) (encRound encP) 1 1 := by
    fun_prop (disch := first | apply le_refl | lia)
  have hargs : ComputableTidilyInDegree
      (fun q : (π × ℕ) × State => (q.1.1, q.2.args.2.1, q.2.args.2.2)) (encRound encP)
      (encPair encP (encPair encBits encBits)) 1 1 := by
    fun_prop (disch := first | apply le_refl | lia)
  have hends : ComputableTidilyInDegree
      (fun q : (π × ℕ) × State => (q.2.args.2.1, q.2.args.2.2)) (encRound encP)
      (encPair encBits encBits) 1 1 := by
    fun_prop (disch := first | apply le_refl | lia)
  have hkeep : ComputableTidilyInDegree (fun q : (π × ℕ) × State => q.1) (encRound encP)
      (encPair encP encUnary) 1 1 := by
    fun_prop (disch := first | apply le_refl | lia)
  have hstack : ComputableTidilyInDegree (fun q : (π × ℕ) × State => q.2.stack) (encRound encP)
      (encList encFrame) 1 1 := by
    fun_prop (disch := first | apply le_refl | lia)
  have hval := or_deg.inO_one.comp_linear
    ((ComputableTidilyInO.eqWords.comp hends.inO_one).prod (hedge.comp hargs.inO_one))
  have hbase := hkeep.inO_one.prod (stateMk_deg.inO_one.comp_linear
    (hstack.inO_one.prod (ret_deg.inO_one.comp_linear hval)))
  refine ((hc.inO_one.ite hbase hrest.inO_one).mono 8 (fun q => ?_) fun q => ?_).of_enc_eq
    fun q => by rw [roundStep_eq]; split_ifs <;> rfl
  all_goals
    have hE : (encReg q.2.reg).length ≤ (encRound encP q).length := by
      have h₁ : (encState q.2).length ≤ (encRound encP q).length := length_le_encPair_right _ _ q
      have := length_encState q.2
      omega
  · split_ifs with hq
    · have hreg := eq_call_of_isBase hq
      rw [hreg, length_encReg_call] at hE
      rw [hreg, Reg.edgeCost]
      have := Nat.mul_le_mul (show q.2.args.2.1.length + 1 ≤ (encRound encP q).length + 1 by omega)
        (show q.2.args.2.1.length + q.2.args.2.2.length + 1 ≤ (encRound encP q).length + 1 by
          omega)
      nlinarith
    · nlinarith
  · dsimp only
    split_ifs with hq
    · have hreg := eq_call_of_isBase hq
      rw [hreg, length_encReg_call] at hE
      rw [hreg, Reg.edgeCost]
      omega
    · omega

/-! ### The states of a run -/

/-- The rounds keep the parameter and the width, and run the machine. -/
theorem roundStep_iterate (edge : π → List Bool → List Bool → Bool) (p : π) (w : ℕ) (s : State)
    (k : ℕ) : (roundStep edge)^[k] ((p, w), s) = ((p, w), (step (edge p) w)^[k] s) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']; rfl

/-- The frames of a run from a call at level `d` with words of width `w`: a frame with `n` frames
below it is at a level below `d - n`, and its words have width `w`. -/
private def StackOk (w d : ℕ) : List Frame → Prop
  | [] => True
  | f :: stack => f.level + 1 + stack.length ≤ d ∧ f.src.length = w ∧ f.dst.length = w ∧
      f.mid.length = w ∧ StackOk w d stack

/-- The states of a run from a call at level `d` with words of width `w`. -/
private def Invariant (w d : ℕ) (s : State) : Prop :=
  StackOk w d s.stack ∧
    ∀ i u v, s.reg = .call i u v → i + s.stack.length ≤ d ∧ u.length = w ∧ v.length = w

/-- The increment keeps the width. -/
private theorem length_incr (u : List Bool) : (incr u).length = u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp [incr, ih]

/-- The counter keeps the width. -/
private theorem length_of_next {u m : List Bool} (h : next u = some m) : m.length = u.length := by
  rw [next_eq] at h
  split_ifs at h
  cases h
  exact length_incr u

/-- The step keeps the invariant of a run. -/
private theorem invariant_step (edge : List Bool → List Bool → Bool) {w d : ℕ} {s : State}
    (h : Invariant w d s) : Invariant w d (step edge w s) := by
  obtain ⟨hst, hreg⟩ := h
  obtain ⟨stack, (⟨_ | i, u, v⟩ | b)⟩ := s
  · exact ⟨hst, fun _ _ _ h => by cases h⟩
  · obtain ⟨hi, hu, hv⟩ := hreg _ _ _ rfl
    refine ⟨⟨by dsimp only at hi ⊢; omega, hu, hv, List.length_replicate, hst⟩,
      fun i' u' v' h => ?_⟩
    obtain ⟨rfl, rfl, rfl⟩ := Reg.call.inj h
    exact ⟨by simp only [step, List.length_cons] at hi ⊢; omega, hu, List.length_replicate⟩
  · rcases stack with _ | ⟨f, stack⟩
    · exact ⟨hst, hreg⟩
    · obtain ⟨hl, hs, hd, hm, hst⟩ := hst
      cases b
      · cases hn : next f.mid with
        | none =>
          simp only [step, hn]
          exact ⟨hst, fun _ _ _ h => by cases h⟩
        | some m =>
          have hm' := length_of_next hn
          simp only [step, hn]
          refine ⟨⟨hl, hs, hd, by dsimp only; omega, hst⟩, fun i u v h => ?_⟩
          obtain ⟨rfl, rfl, rfl⟩ := Reg.call.inj h
          exact ⟨by simp only [List.length_cons]; omega, hs, by omega⟩
      · cases hph : f.phase
        · simp only [step, hph, Bool.false_eq_true, ↓reduceIte]
          refine ⟨⟨hl, hs, hd, hm, hst⟩, fun i u v h => ?_⟩
          obtain ⟨rfl, rfl, rfl⟩ := Reg.call.inj h
          exact ⟨by simp only [List.length_cons]; omega, hm, hd⟩
        · simp only [step, hph, ↓reduceIte]
          exact ⟨hst, fun _ _ _ h => by cases h⟩

/-- Every state of a run keeps the invariant. -/
private theorem invariant_iterate (edge : List Bool → List Bool → Bool) {w d : ℕ} {s : State}
    (h : Invariant w d s) (k : ℕ) : Invariant w d ((step edge w)^[k] s) := by
  induction k with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply']; exact invariant_step edge ih

/-- A run from a call at level `d` holds at most `d` frames. -/
private theorem StackOk.length_le {w d : ℕ} :
    ∀ {stack : List Frame}, StackOk w d stack → stack.length ≤ d
  | [], _ => Nat.zero_le _
  | _ :: _, h => by have := h.1; simp only [List.length_cons]; omega

/-- The frames of a run from a call at level `d` are below level `d`, with words of width
`w`. -/
private theorem StackOk.mem {w d : ℕ} :
    ∀ {stack : List Frame}, StackOk w d stack → ∀ f ∈ stack,
      f.level < d ∧ f.src.length = w ∧ f.dst.length = w ∧ f.mid.length = w
  | [], _, _, hf => by simp at hf
  | g :: _, h, f, hf => by
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨by have := h.1; omega, h.2.1, h.2.2.1, h.2.2.2.1⟩
    · exact h.2.2.2.2.mem f hf

/-- The states of a run from a call at level `d`, with words of width `w`, are of size
`O((d + 1) * (d + w + 1))`: at most `d` frames of size `O(d + w)`, and a call of size
`O(d + w)`. -/
private theorem length_encState_le {w d : ℕ} {s : State} (h : Invariant w d s) :
    (encState s).length ≤ 24 * (d + 1) * (d + w + 1) := by
  obtain ⟨hst, hreg⟩ := h
  have hlist : (encList encFrame s.stack).length ≤ d * (2 * (2 * d + 6 * w + 5) + 1) := by
    refine (length_encList_le encFrame s.stack fun f hf => ?_).trans
      (Nat.mul_le_mul_right _ hst.length_le)
    obtain ⟨hl, hs, hd, hm⟩ := hst.mem f hf
    rw [length_encFrame]
    omega
  have hr : (encReg s.reg).length ≤ 4 * d + 6 * w + 8 := by
    rcases hs : s.reg with ⟨i, u, v⟩ | b
    · obtain ⟨hi, hu, hv⟩ := hreg i u v hs
      rw [length_encReg_call]
      omega
    · rw [length_encReg_ret]
      omega
  rw [length_encState]
  nlinarith

/-- A bound on the encoded states of the iteration, for an encoded parameter of length `P`. -/
private def stateBound (P w d : ℕ) : ℕ := 4 * P + 27 * ((d + 1) * (d + w + 1))

/-- The rounds of a run from a call at level `d` are of size `stateBound`. -/
private theorem length_encRound_le {p : π} {w d : ℕ} {s : State} (h : Invariant w d s) :
    (encRound encP ((p, w), s)).length ≤ stateBound (encP p).length w d := by
  have := length_encState_le h
  simp only [encRound, length_encPair, encUnary_apply, List.length_replicate, stateBound]
  nlinarith

/-- The largest value of `T` on the parameter `p` and two words of width `w`. -/
def edgeMax (T : π × List Bool × List Bool → ℕ) (p : π) (w : ℕ) : ℕ :=
  listMax (fun u => listMax (fun v => T (p, u, v)) (words w)) (words w)

/-- `edgeMax` bounds `T` on all words of width `w`. -/
theorem le_edgeMax (T : π × List Bool × List Bool → ℕ) (p : π) {w : ℕ} {u v : List Bool}
    (hu : u.length = w) (hv : v.length = w) : T (p, u, v) ≤ edgeMax T p w :=
  (le_listMax (f := fun v => T (p, u, v)) (mem_words.mpr hv)).trans
    (le_listMax (f := fun u => listMax (fun v => T (p, u, v)) (words w)) (mem_words.mpr hu))

/-- The edge test of a round of a run runs on words of width `w`. -/
private theorem edgeCost_le (T : π × List Bool × List Bool → ℕ) (p : π) {w d : ℕ} {s : State}
    (h : Invariant w d s) : s.reg.edgeCost T p ≤ edgeMax T p w := by
  rcases hs : s.reg with ⟨i, u, v⟩ | b
  · obtain ⟨-, hu, hv⟩ := h.2 i u v hs
    exact le_edgeMax T p hu hv
  · exact Nat.zero_le _

/-! ### The number of rounds, in binary -/

/-- `2 ^ K - 1` in binary is `K` ones. -/
private theorem bits_two_pow_sub_one (K : ℕ) : Nat.bits (2 ^ K - 1) = List.replicate K true := by
  induction K with
  | zero => exact Nat.zero_bits
  | succ K ih =>
    have := Nat.one_le_two_pow (n := K)
    rw [show 2 ^ (K + 1) - 1 = 2 * (2 ^ K - 1) + 1 by rw [pow_succ]; omega, Nat.bit1_bits, ih,
      List.replicate_succ]

/-- The number of rounds in binary is `(w + 2) * (d + 1)` ones. -/
private theorem encNat_savitchSteps (w d : ℕ) :
    encNat (savitchSteps w d) = List.replicate ((w + 2) * (d + 1)) true := by
  rw [encNat_apply, savitchSteps, bits_two_pow_sub_one]

/-- A round of writing the number of rounds: `p` more ones. -/
private def countStep (p : ℕ) (acc : List Bool) (_ : Bool) : List Bool :=
  acc ++ List.replicate p true

/-- Writing the number of rounds, `p` ones at a time. -/
private theorem foldl_countStep (p n : ℕ) (acc : List Bool) :
    (List.replicate n true).foldl (countStep p) acc = acc ++ List.replicate (n * p) true := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons, ih, countStep, List.append_assoc,
      ← List.replicate_add]
    congr 2
    ring

/-- The number of rounds, `(w + 2) * (d + 1)` ones in binary, from `w` and `d` in unary. -/
private theorem savitchSteps_inO :
    ComputableTidilyInO (fun t : ℕ × ℕ => savitchSteps t.1 t.2) (encPair encUnary encUnary)
      encNat (fun t => (t.2 + 2) * ((t.1 + 2) * (t.2 + 1))) fun t => (t.1 + 2) * (t.2 + 1) := by
  have hpar : ComputableTidilyInDegree (fun t : ℕ × ℕ => t.1 + 2) (encPair encUnary encUnary)
      encUnary 1 1 :=
    (unary_succ.comp (unary_succ.comp (fst encUnary encUnary))).mono
  have hlist : ComputableTidilyInDegree (fun t : ℕ × ℕ => List.replicate (t.2 + 1) true)
      (encPair encUnary encUnary) encBits 1 1 :=
    ((unary_succ.comp (snd encUnary encUnary)).mono).of_enc_eq fun _ => rfl
  have hstep : ComputableTidilyInDegree
      (fun r : (ℕ × List Bool) × Bool => countStep r.1.1 r.1.2 r.2)
      (encPair (encPair encUnary encBits) encBool) encBits 1 1 :=
    (((snd encUnary encBits).comp (fst (encPair encUnary encBits) encBool)).append
      ((fst encUnary encBits).comp (fst (encPair encUnary encBits) encBool))
      (enc₂ := encUnary) fun _ => rfl).mono
  have hacc (t : ℕ × ℕ) (i : ℕ) : (((List.replicate (t.2 + 1) true).take i).foldl
      (countStep (t.1 + 2)) []).length ≤ (t.1 + 2) * (t.2 + 1) := by
    rw [List.take_replicate, foldl_countStep, List.nil_append, List.length_replicate]
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (min_le_right _ _)
  have hfold := ComputableTidilyInO.foldlWith (encL := encBits) (encB := encBits) hpar.inO_one
    hlist.inO_one (ComputableTidilyInO.const []) hstep.inO_one
    (R := fun t => 6 * ((t.1 + 2) * (t.2 + 1)) + 4)
    (Q := fun t => 6 * ((t.1 + 2) * (t.2 + 1)) + 4)
    (B := fun t => (t.1 + 2) * (t.2 + 1))
    (fun t i _ => by
      have := hacc t i
      simp only [length_encPair, encUnary_apply, encBits_apply, encBool_apply,
        List.length_replicate, List.length_singleton]
      nlinarith)
    (fun t i _ => by
      have := hacc t i
      simp only [length_encPair, encUnary_apply, encBits_apply, encBool_apply,
        List.length_replicate, List.length_singleton]
      nlinarith)
    (fun t i _ => by simpa using hacc t i)
  refine (hfold.mono 32 (fun t => ?_) fun t => ?_).of_enc_eq fun t => ?_
  all_goals
    have hK : t.1 + t.2 + 2 ≤ (t.1 + 2) * (t.2 + 1) := by nlinarith
  · simp only [length_encPair, encUnary_apply, encBits_apply, List.length_replicate]
    generalize (t.1 + 2) * (t.2 + 1) = K at hK ⊢
    nlinarith
  · simp only [length_encPair, encUnary_apply, encBits_apply, List.length_replicate]
    generalize (t.1 + 2) * (t.2 + 1) = K at hK ⊢
    nlinarith
  · rw [encNat_savitchSteps, foldl_countStep, List.nil_append, encBits_apply, Nat.mul_comm]

/-! ### Savitch's algorithm in the space of its stack -/

/-- The encoding of the inputs of Savitch's algorithm: the parameter of the edge test, the width and
the depth in unary, and the endpoints. -/
abbrev encArgs (encP : π ↪ List Bool) : π × ℕ × ℕ × List Bool × List Bool ↪ List Bool :=
  encPair encP (encPair encUnary (encPair encUnary (encPair encBits encBits)))

/-- The first round, from the arguments, in linear time. -/
private lemma init_deg : ComputableTidilyInDegree
    (fun t : π × ℕ × ℕ × List Bool × List Bool =>
      ((t.1, t.2.1), State.mk [] (.call t.2.2.1 t.2.2.2.1 t.2.2.2.2)))
    (encArgs encP) (encRound encP) 1 1 := by
  fun_prop (disch := first | apply le_refl | lia)

/-- The width and the depth, from the arguments, in linear time. -/
private lemma widthDepth_deg : ComputableTidilyInDegree
    (fun t : π × ℕ × ℕ × List Bool × List Bool => (t.2.1, t.2.2.1)) (encArgs encP)
    (encPair encUnary encUnary) 1 1 := by
  fun_prop (disch := first | apply le_refl | lia)

/-- The answer, from a round, in linear time. -/
private lemma answer_deg : ComputableTidilyInDegree
    (fun q : (π × ℕ) × State => q.2.reg.toPair.2) (encRound encP) encBool 1 1 := by
  fun_prop (disch := first | apply le_refl | lia)

/-- The answer is the second component of the register as a pair. -/
private theorem answer_eq (r : Reg) : r.answer = r.toPair.2 := by
  cases r <;> rfl

/-- There are `2 ^ ((w + 2) * (d + 1))` states in a run, counting the first. -/
private theorem savitchSteps_add_one (w d : ℕ) :
    savitchSteps w d + 1 = 2 ^ ((w + 2) * (d + 1)) :=
  Nat.sub_add_cancel Nat.one_le_two_pow

/-- The counter of the rounds has `(w + 2) * (d + 1)` digits. -/
private theorem length_encNat_savitchSteps (w d : ℕ) :
    (encNat (savitchSteps w d)).length = (w + 2) * (d + 1) := by
  rw [encNat_savitchSteps, List.length_replicate]

/-- The arithmetic of the bounds of `computableTidilyInO_savitch`, where `S₀ = (d + 1) *
(d + w + 1) + P` bounds the stack and the parameter. -/
private theorem savitch_bounds (P w d : ℕ) :
    stateBound P w d + 1 ≤ 27 * ((d + 1) * (d + w + 1) + P + 1) ∧
      (w + 2) * (d + 1) + 1 ≤ 2 * ((d + 1) * (d + w + 1) + P + 1) ∧
      d + 2 ≤ (d + 1) * (d + w + 1) + P + 1 := by
  simp only [stateBound]
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **Savitch's algorithm in the space of its stack.** Let the edge test `edge p` be tidily
computable within time `O(Te)` and space `O(Se)`, and let the parameter, the width `w` and depth
`d` in unary, and endpoints of width `w` be computable from `x` within time `O(Tin)` and space
`O(Sin)`. Then Savitch's algorithm is tidily computable within time
`O(Tin + 2 ^ ((w + 2) * (d + 1)) * (S₀ ^ 2 + Te))` and space `O(Sin + S₀ + Se)`, with
`S₀ = (d + 1) * (d + w + 1) + |p|` and `Te`, `Se` at the worst endpoints of width `w`
(`Cslib.Reachability.edgeMax`). The space charges the stack of at most `d` frames, each with a
level and three words, the register, the parameter, the width, and the counter of the rounds; the
time charges every round, which copies the state [Sipser, Theorem 8.5][Sipser2013]
[Arora and Barak, Section 4.2][AroraBarak09]. -/
theorem computableTidilyInO_savitch {γ : Type} {encIn : γ ↪ List Bool}
    {edge : π → List Bool → List Bool → Bool} {Te Se : π × List Bool × List Bool → ℕ}
    (hedge : ComputableTidilyInO (fun q : π × List Bool × List Bool => edge q.1 q.2.1 q.2.2)
      (encPair encP (encPair encBits encBits)) encBool Te Se)
    {par : γ → π} {width depth : γ → ℕ} {src dst : γ → List Bool} {Tin Sin : γ → ℕ}
    (hin : ComputableTidilyInO (fun x => (par x, width x, depth x, src x, dst x)) encIn
      (encArgs encP) Tin Sin)
    (hsrc : ∀ x, (src x).length = width x) (hdst : ∀ x, (dst x).length = width x) :
    ComputableTidilyInO (fun x => savitch (edge (par x)) (width x) (depth x) (src x) (dst x))
      encIn encBool
      (fun x => Tin x + 2 ^ ((width x + 2) * (depth x + 1)) *
        (((depth x + 1) * (depth x + width x + 1) + (encP (par x)).length + 1) ^ 2 +
          edgeMax Te (par x) (width x)))
      fun x => Sin x + (depth x + 1) * (depth x + width x + 1) + (encP (par x)).length +
        edgeMax Se (par x) (width x) := by
  rcases isEmpty_or_nonempty γ with hγ | ⟨⟨x₀⟩⟩
  · exact ((ComputableTidilyInO.const (encMid := encBool) false).mono 0 (fun x => isEmptyElim x)
      fun x => isEmptyElim x).of_enc_eq fun x => isEmptyElim x
  have : Inhabited π := ⟨par x₀⟩
  have hn := savitchSteps_inO.comp (widthDepth_deg.inO_one.comp_linear hin)
  have hinit := init_deg.inO_one.comp_linear hin
  -- every state of the run is a state of a run from a call at level `depth x`
  have hinv (x : γ) (k : ℕ) : Invariant (width x) (depth x)
      ((step (edge (par x)) (width x))^[k] ⟨[], .call (depth x) (src x) (dst x)⟩) :=
    invariant_iterate (w := width x) (d := depth x)
      (s := ⟨[], .call (depth x) (src x) (dst x)⟩) _ ⟨trivial, fun i u v h => by
        obtain ⟨rfl, rfl, rfl⟩ := Reg.call.inj h
        exact ⟨by simp, hsrc x, hdst x⟩⟩ k
  have hiter := ComputableTidilyInO.iterate hn hinit (computableTidilyInO_roundStep hedge)
    (R := fun x => (stateBound (encP (par x)).length (width x) (depth x) + 1) ^ 2 +
      edgeMax Te (par x) (width x))
    (Q := fun x => stateBound (encP (par x)).length (width x) (depth x) +
      edgeMax Se (par x) (width x))
    (B := fun x => stateBound (encP (par x)).length (width x) (depth x))
    (fun x k _ => by
      simp only [Function.comp_apply, roundStep_iterate]
      exact Nat.add_le_add (Nat.pow_le_pow_left (Nat.add_le_add_right
        (length_encRound_le (hinv x k)) 1) 2) (edgeCost_le Te _ (hinv x k)))
    (fun x k _ => by
      simp only [Function.comp_apply, roundStep_iterate]
      exact Nat.add_le_add (length_encRound_le (hinv x k)) (edgeCost_le Se _ (hinv x k)))
    (fun x k _ => by
      simp only [Function.comp_apply, roundStep_iterate]
      exact length_encRound_le (hinv x k))
  refine ((answer_deg.inO_one.comp_linear hiter).mono 900 (fun x => ?_) fun x => ?_).of_enc_eq
    fun x => ?_
  all_goals simp only [Function.comp_apply]
  · rw [savitchSteps_add_one, length_encNat_savitchSteps]
    obtain ⟨h₁, h₂, h₃⟩ := savitch_bounds (encP (par x)).length (width x) (depth x)
    generalize stateBound (encP (par x)).length (width x) (depth x) = B at h₁ ⊢
    generalize (depth x + 1) * (depth x + width x + 1) + (encP (par x)).length = S at h₁ h₂ h₃ ⊢
    generalize (width x + 2) * (depth x + 1) = K at h₂ ⊢
    generalize edgeMax Te (par x) (width x) = E
    have hM : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    generalize 2 ^ K = M at hM ⊢
    have hB := Nat.pow_le_pow_left h₁ 2
    have hK := Nat.pow_le_pow_left h₂ 2
    have hdK := Nat.mul_le_mul h₃ (show K ≤ 2 * (S + 1) by omega)
    rw [Nat.mul_pow] at hB hK
    have hround : (B + 1) ^ 2 + E + B + (K + 1) ^ 2 ≤ 760 * (S + 1) ^ 2 + E := by nlinarith
    have := Nat.mul_le_mul_left M hround
    have : (S + 1) ^ 2 ≤ M * (S + 1) ^ 2 := Nat.le_mul_of_pos_left _ hM
    nlinarith
  · rw [length_encNat_savitchSteps]
    obtain ⟨h₁, h₂, -⟩ := savitch_bounds (encP (par x)).length (width x) (depth x)
    simp only [stateBound] at h₁ ⊢
    nlinarith
  · rw [roundStep_iterate, savitch, answer_eq]

/-- **Savitch's algorithm in polynomial space.** If the edge test is tidily computable in
polynomial time, and the parameter, the width and depth in unary, and endpoints of width `w` are
computable from `x` in polynomial time, then Savitch's algorithm is tidily computable within
space polynomial in the length of the encoded input; the time is exponential, see
`Cslib.Reachability.computableTidilyInO_savitch`. The width and the depth are polynomial since they
are computed in unary [Sipser, Theorem 8.5][Sipser2013]. -/
theorem exists_polyBounded_space_savitch {γ : Type} {encIn : γ ↪ List Bool}
    {edge : π → List Bool → List Bool → Bool}
    (hedge : ComputableTidilyInPolyTime (fun q : π × List Bool × List Bool => edge q.1 q.2.1 q.2.2)
      (encPair encP (encPair encBits encBits)) encBool)
    {par : γ → π} {width depth : γ → ℕ} {src dst : γ → List Bool}
    (hin : ComputableTidilyInPolyTime (fun x => (par x, width x, depth x, src x, dst x)) encIn
      (encArgs encP))
    (hsrc : ∀ x, (src x).length = width x) (hdst : ∀ x, (dst x).length = width x) :
    ∃ t s, PolyBounded (fun x => (encIn x).length) s ∧
      ComputableTidilyInTimeAndSpace
        (fun x => savitch (edge (par x)) (width x) (depth x) (src x) (dst x)) encIn encBool t
        s := by
  have hlen := hin.polyBounded_length
  obtain ⟨te, se, -, hse, he⟩ := hedge
  obtain ⟨ti, si, hti, hsi, hi⟩ := hin
  obtain ⟨cs, ds, hcs⟩ := hse.exists_le
  have hedgeO : ComputableTidilyInO _ _ encBool te se :=
    ⟨1, he.mono (fun _ => by omega) fun _ => by omega, fun _ => by simp⟩
  have hinO : ComputableTidilyInO _ encIn (encArgs encP) ti fun x => ti x + si x :=
    ⟨1, hi.mono (fun _ => by omega) fun _ => by dsimp only; omega, fun x => by
      have := hi.length_le x
      dsimp only
      omega⟩
  obtain ⟨c, h, -⟩ := computableTidilyInO_savitch hedgeO hinO hsrc hdst
  refine ⟨_, _, ?_, h⟩
  -- the stack, the parameter and the edge test are polynomial in the encoded arguments
  set L := fun x => (encArgs encP (par x, width x, depth x, src x, dst x)).length
  have hL (x : γ) : depth x ≤ L x ∧ width x ≤ L x ∧ (encP (par x)).length ≤ L x := by
    simp only [L, encArgs, length_encPair, encUnary_apply, List.length_replicate]
    omega
  have hE (x : γ) : edgeMax se (par x) (width x) ≤ cs * (5 * L x + 3) ^ ds :=
    listMax_le fun u hu => listMax_le fun v hv => by
      refine (hcs _).trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left ?_ ds))
      have := hL x
      simp only [length_encPair, encBits_apply, mem_words.mp hu, mem_words.mp hv]
      omega
  have hpoly : Cslib.PolynomiallyBounded
      fun n => (n + 1) * (2 * n + 1) + n + cs * (5 * n + 3) ^ ds + 1 := by
    fun_prop
  have hg : PolyBounded (fun x => (encIn x).length)
      fun x => (L x + 1) * (2 * L x + 1) + L x + cs * (5 * L x + 3) ^ ds + 1 :=
    PolyBounded.comp (size' := id) (g := L) (PolyBounded.of_polynomiallyBounded id hpoly) hlen
  refine ((PolyBounded.const c).mul ((hti.add hsi).add hg)).mono fun x => ?_
  obtain ⟨hd, hw, hP⟩ := hL x
  have := Nat.mul_le_mul (show depth x + 1 ≤ L x + 1 by omega)
    (show depth x + width x + 1 ≤ 2 * L x + 1 by omega)
  dsimp only
  exact Nat.mul_le_mul_left c (by have := hE x; omega)

end Certificates

end Cslib.Reachability
