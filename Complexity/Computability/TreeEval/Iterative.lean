/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.CookMertz

/-!
# The Cook–Mertz procedure as an iterative machine

`Cslib.TreeEval.proc` is recursive. This file unravels the recursion into a machine whose state is
the three registers, a stack with one frame per level, and a mode. A frame records only the round,
the phase within the round, the sign and the target register of its level, which is what makes the
procedure space-efficient: the path to the current node is read off the phases of the frames.

In mode `call neg t`, the machine is about to add `±` the value of the node at the current path
to register `t`: at a leaf it does so in one step, at a gate it pushes a frame and calls the left
child. In mode `ret`, it continues the round of the top frame, which calls the children in the
order left, right, left, right, with signs `+, +, -, -`, as in `Cslib.TreeEval.gateRound`, and
moves on to the next round or returns.

The update of a round and the reading of a leaf are single steps here; they are refined into steps
that read the input bit by bit separately.

## Main definitions

* `Cslib.TreeEval.Iter.Cfg`: the configurations of the machine.
* `Cslib.TreeEval.Iter.step`: one step, for a tree and an enumeration `unit 0, …, unit (m - 1)` of
  units.
* `Cslib.TreeEval.Iter.steps`: the number of steps to evaluate a subtree of a given height.
* `Cslib.TreeEval.Iter.zmodUnit`: the units `1, …, p - 1` of `ZMod p`.

## Main results

* `Cslib.TreeEval.Iter.iterate_step_call`: run from a call on a subtree, the machine performs the
  procedure on it and returns.
* `Cslib.TreeEval.Iter.iterate_step_init`: run from the initial configuration, it halts with the
  result of the procedure.
* `Cslib.TreeEval.Iter.iterate_step_init_zmod`: over `ZMod p` with the units `1, …, p - 1` and
  `2ℓ < p - 1`, it halts with the value of the tree in register `2`.

## References

* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval],
  Algorithm 1 and Lemma 5.
-/

@[expose] public section

namespace Cslib.TreeEval

namespace Iter

variable {K : Type*} [Field K] {ℓ : ℕ}

/-- A frame of the recursion: the round, the phase within the round, whether the level subtracts
its value, and its target register. In phase `n` the frame has called its left child (`n` even)
or its right child (`n` odd), adding for `n < 2` and subtracting otherwise. -/
structure Frame where
  /-- The round, indexing the unit that masks the children. -/
  round : ℕ
  /-- The phase within the round. -/
  phase : Fin 4
  /-- Whether the value of this level is subtracted. -/
  neg : Bool
  /-- The target register. -/
  target : Fin 3
  deriving DecidableEq

/-- The child a frame has called: the right one in the odd phases. -/
def Frame.dir (fr : Frame) : Bool := fr.phase.val % 2 == 1

/-- The path to the node called by the top frame, from the root. -/
def path : List Frame → List Bool
  | [] => []
  | fr :: st => path st ++ [fr.dir]

/-- The mode of the machine: about to evaluate the current node into a register, or returning to
the top frame. -/
inductive Mode where
  /-- About to add `±` the value of the node at the current path to register `t`. -/
  | call (neg : Bool) (t : Fin 3)
  /-- Returning to the top frame. -/
  | ret
  deriving DecidableEq

/-- A configuration: the registers, the stack, innermost frame first, and the mode. -/
structure Cfg (K : Type*) (ℓ : ℕ) where
  /-- The registers. -/
  regs : State K ℓ
  /-- The stack of frames, innermost first. -/
  stack : List Frame
  /-- The mode. -/
  mode : Mode

/-- The coefficient of a sign. -/
def sgn (neg : Bool) : K := if neg then -1 else 1

variable {H : ℕ} (T : Tree ℓ H) (m : ℕ) (unit : ℕ → Kˣ)

/-- One step of the machine evaluating `T`, with the units `unit 0, …, unit (m - 1)`. -/
noncomputable def step : Cfg K ℓ → Cfg K ℓ
  | ⟨S, st, .call neg t⟩ =>
    match T.nodeAt (path st) with
    | .leaf v => ⟨Function.update S t (S t + (sgn neg : K) • (embed v : Fin ℓ → K)), st, .ret⟩
    | .gate _ => ⟨scale (t + 1) (unit 0 : K) S, ⟨0, 0, neg, t⟩ :: st, .call false (t + 1)⟩
    | .none => ⟨S, st, .call neg t⟩
  | ⟨S, [], .ret⟩ => ⟨S, [], .ret⟩
  | ⟨S, fr :: st, .ret⟩ =>
    match fr.phase with
    | 0 => ⟨scale (fr.target + 2) (unit fr.round : K) S, { fr with phase := 1 } :: st,
        .call false (fr.target + 2)⟩
    | 1 =>
      match T.nodeAt (path st) with
      | .gate f => ⟨gateUpdate f (sgn fr.neg) fr.target S, { fr with phase := 2 } :: st,
          .call true (fr.target + 1)⟩
      | _ => ⟨S, fr :: st, .ret⟩
    | 2 => ⟨scale (fr.target + 1) (((unit fr.round)⁻¹ : Kˣ) : K) S, { fr with phase := 3 } :: st,
        .call true (fr.target + 2)⟩
    | 3 =>
      let S := scale (fr.target + 2) (((unit fr.round)⁻¹ : Kˣ) : K) S
      if fr.round + 1 < m then
        ⟨scale (fr.target + 1) (unit (fr.round + 1) : K) S,
          ⟨fr.round + 1, 0, fr.neg, fr.target⟩ :: st, .call false (fr.target + 1)⟩
      else ⟨S, st, .ret⟩

/-- The number of steps to evaluate a subtree of height `d`. -/
def steps : ℕ → ℕ
  | 0 => 1
  | d + 1 => 1 + m * (4 * steps d + 4)

/-- The initial configuration: zero registers, an empty stack, a call into register `2`. -/
def init : Cfg K ℓ := ⟨0, [], .call false 2⟩

variable {T m unit}

@[simp] theorem path_cons (fr : Frame) (st : List Frame) :
    path (fr :: st) = path st ++ [fr.dir] := rfl

@[simp] theorem sgn_false : (sgn false : K) = 1 := rfl
@[simp] theorem sgn_true : (sgn true : K) = -1 := rfl

/-- The configuration that starts round `j` at a gate whose stack below is `st`, before scaling
register `t + 1` by the unit of the round. -/
noncomputable def roundStart (unit : ℕ → Kˣ) (j : ℕ) (neg : Bool) (t : Fin 3) (st : List Frame)
    (X : State K ℓ) : Cfg K ℓ :=
  ⟨scale (t + 1) (unit j : K) X, ⟨j, 0, neg, t⟩ :: st, .call false (t + 1)⟩

/-- **One round.** If both subtrees are evaluated by the machine as by the procedure, a round
takes `4 * steps d + 4` steps and performs `gateRound`, then starts the next round or returns. -/
theorem iterate_step_round {d : ℕ} {f : (Fin ℓ → Bool) → (Fin ℓ → Bool) → Fin ℓ → Bool}
    {st : List Frame} (hg : T.nodeAt (path st) = .gate f)
    (pl pr : K → Fin 3 → State K ℓ → State K ℓ)
    (hl : ∀ st' neg t S, path st' = path st ++ [false] →
      (step T m unit)^[steps m d] ⟨S, st', .call neg t⟩ = ⟨pl (sgn neg) t S, st', .ret⟩)
    (hr : ∀ st' neg t S, path st' = path st ++ [true] →
      (step T m unit)^[steps m d] ⟨S, st', .call neg t⟩ = ⟨pr (sgn neg) t S, st', .ret⟩)
    (j : ℕ) (neg : Bool) (t : Fin 3) (X : State K ℓ) :
    (step T m unit)^[4 * steps m d + 4] (roundStart unit j neg t st X) =
      let Y := gateRound pl pr f (sgn neg) t (unit j) X
      if j + 1 < m then roundStart unit (j + 1) neg t st Y else ⟨Y, st, .ret⟩ := by
  have e : 4 * steps m d + 4 =
      1 + (steps m d + (1 + (steps m d + (1 + (steps m d + (1 + steps m d)))))) := by ring
  rw [e]
  simp only [Function.iterate_add_apply, Function.iterate_one, roundStart]
  rw [hl _ _ _ _ (by simp [Frame.dir])]
  simp only [step]
  rw [hr _ _ _ _ (by simp [Frame.dir])]
  simp only [hg]
  rw [hl _ _ _ _ (by simp [Frame.dir])]
  rw [hr _ _ _ _ (by simp [Frame.dir])]
  simp only [gateRound, sgn_false, sgn_true]

/-- The rounds `j, …, j + k` of a gate, the last ones before `m`, perform the corresponding
`gateRound`s and return. -/
theorem iterate_step_rounds {d : ℕ} {f : (Fin ℓ → Bool) → (Fin ℓ → Bool) → Fin ℓ → Bool}
    {st : List Frame} (hg : T.nodeAt (path st) = .gate f)
    (pl pr : K → Fin 3 → State K ℓ → State K ℓ)
    (hl : ∀ st' neg t S, path st' = path st ++ [false] →
      (step T m unit)^[steps m d] ⟨S, st', .call neg t⟩ = ⟨pl (sgn neg) t S, st', .ret⟩)
    (hr : ∀ st' neg t S, path st' = path st ++ [true] →
      (step T m unit)^[steps m d] ⟨S, st', .call neg t⟩ = ⟨pr (sgn neg) t S, st', .ret⟩)
    (neg : Bool) (t : Fin 3) (k : ℕ) :
    ∀ j X, j + k + 1 = m →
      (step T m unit)^[(k + 1) * (4 * steps m d + 4)] (roundStart unit j neg t st X) =
        ⟨((List.range' j (k + 1)).map unit).foldl
          (fun S u => gateRound pl pr f (sgn neg) t u S) X, st, .ret⟩ := by
  induction k with
  | zero =>
    intro j X hj
    rw [zero_add, one_mul, iterate_step_round hg pl pr hl hr]
    simp [show ¬j + 1 < m by omega]
  | succ k ih =>
    intro j X hj
    rw [show (k + 1 + 1) * (4 * steps m d + 4) =
        (k + 1) * (4 * steps m d + 4) + (4 * steps m d + 4) by ring,
      Function.iterate_add_apply, iterate_step_round hg pl pr hl hr]
    simp only [show j + 1 < m by omega, ite_true]
    rw [ih (j + 1) _ (by omega)]
    simp only [List.range'_succ, List.map_cons, List.foldl_cons]

/-- **The machine performs the procedure.** Run from a call on a subtree `U` at the path of the
stack `st`, the machine adds `±` the procedure's result for `U` and returns, in `steps m d`
steps. -/
theorem iterate_step_call (hm : 0 < m) {d : ℕ} (U : Tree ℓ d) :
    ∀ (st : List Frame), (∀ Q, T.nodeAt (path st ++ Q) = U.nodeAt Q) →
      ∀ neg t S, (step T m unit)^[steps m d] ⟨S, st, .call neg t⟩ =
        ⟨proc ((List.range m).map unit) U (sgn neg) t S, st, .ret⟩ := by
  induction U with
  | leaf v =>
    intro st hst neg t S
    have hv : T.nodeAt (path st) = .leaf v := by simpa using hst []
    simp only [steps, Function.iterate_one, step, hv, proc]
  | @node d f l r ihl ihr =>
    intro st hst neg t S
    have hg : T.nodeAt (path st) = .gate f := by simpa using hst []
    have hl : ∀ st' neg t S, path st' = path st ++ [false] →
        (step T m unit)^[steps m d] ⟨S, st', .call neg t⟩ =
          ⟨proc ((List.range m).map unit) l (sgn neg) t S, st', .ret⟩ := fun st' neg t S h =>
      ihl st' (fun Q => by rw [h, List.append_assoc]; simpa using hst (false :: Q)) neg t S
    have hr : ∀ st' neg t S, path st' = path st ++ [true] →
        (step T m unit)^[steps m d] ⟨S, st', .call neg t⟩ =
          ⟨proc ((List.range m).map unit) r (sgn neg) t S, st', .ret⟩ := fun st' neg t S h =>
      ihr st' (fun Q => by rw [h, List.append_assoc]; simpa using hst (true :: Q)) neg t S
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [steps, show 1 + (k + 1) * (4 * steps (k + 1) d + 4) =
        (k + 1) * (4 * steps (k + 1) d + 4) + 1 from Nat.add_comm _ _,
      Function.iterate_add_apply, Function.iterate_one]
    have h0 : step T (k + 1) unit ⟨S, st, .call neg t⟩ = roundStart unit 0 neg t st S := by
      simp only [step, hg, roundStart]
    rw [h0, iterate_step_rounds hg _ _ hl hr neg t k 0 S (by omega), proc,
      List.range_eq_range']

/-- Returning with an empty stack is final. -/
@[simp] theorem step_halted (S : State K ℓ) :
    step T m unit ⟨S, [], .ret⟩ = ⟨S, [], .ret⟩ := rfl

/-- **The machine evaluates the tree.** From the initial configuration it reaches, in
`steps m H` steps, the final configuration with the procedure's result for `T`. -/
theorem iterate_step_init (hm : 0 < m) :
    (step T m unit)^[steps m H] init =
      ⟨proc ((List.range m).map unit) T 1 2 0, [], .ret⟩ :=
  iterate_step_call hm T [] (fun Q => by simp [path]) false 2 0

section ZMod

variable {p : ℕ} [Fact p.Prime]

/-- The units `1, …, p - 1` of `ZMod p`, in order: `zmodUnit j` is `j + 1` for `j < p - 1`. -/
noncomputable def zmodUnit (p : ℕ) [Fact p.Prime] (j : ℕ) : (ZMod p)ˣ :=
  if h : ((j + 1 : ℕ) : ZMod p) = 0 then 1 else Units.mk0 _ h

theorem zmodUnit_val {j : ℕ} (hj : j < p - 1) :
    (zmodUnit p j : ZMod p) = ((j + 1 : ℕ) : ZMod p) := by
  have hp := (Fact.out : p.Prime).two_le
  have h : ((j + 1 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  rw [zmodUnit, dite_eq_right h, Units.val_mk0]

theorem nodup_zmodUnits : ((List.range (p - 1)).map (zmodUnit p)).Nodup := by
  refine List.Nodup.map_on (fun i hi j hj hij => ?_) List.nodup_range
  have hp := (Fact.out : p.Prime).two_le
  have h := congrArg (fun u : (ZMod p)ˣ => ((u : ZMod p)).val) hij
  simp only [zmodUnit_val (List.mem_range.mp hi), zmodUnit_val (List.mem_range.mp hj),
    ZMod.val_natCast, Nat.mod_eq_of_lt (show i + 1 < p by have := List.mem_range.mp hi; omega),
    Nat.mod_eq_of_lt (show j + 1 < p by have := List.mem_range.mp hj; omega)] at h
  omega

theorem mem_zmodUnits (u : (ZMod p)ˣ) : u ∈ (List.range (p - 1)).map (zmodUnit p) := by
  have hp := (Fact.out : p.Prime).two_le
  have hu : (u : ZMod p).val ≠ 0 := by
    rw [Ne, ZMod.val_eq_zero]; exact u.ne_zero
  have hlt := ZMod.val_lt (u : ZMod p)
  refine List.mem_map.mpr ⟨(u : ZMod p).val - 1, List.mem_range.mpr (by omega), ?_⟩
  refine Units.ext ?_
  rw [zmodUnit_val (by omega), Nat.sub_add_cancel (by omega), ZMod.natCast_zmod_val]

/-- **The iterative machine evaluates the tree** over `ZMod p`, with the units `1, …, p - 1`,
whenever `2ℓ < p - 1`: after `steps (p - 1) H` steps it has halted with the value of the tree in
register `2`. -/
theorem iterate_step_init_zmod (hp : 2 * ℓ < p - 1) :
    (step T (p - 1) (zmodUnit p))^[steps (p - 1) H] init = ⟨Function.update 0 2 (embed T.eval),
      [], .ret⟩ := by
  rw [iterate_step_init (by omega)]
  congr 1
  rw [proc_eq nodup_zmodUnits mem_zmodUnits (by simpa [ZMod.card] using hp)]
  simp

end ZMod

end Iter

end Cslib.TreeEval
