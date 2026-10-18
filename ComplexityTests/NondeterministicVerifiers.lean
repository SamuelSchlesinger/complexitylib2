/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.NP.GuessVerify
import Complexity.Computability.Complexity.Problems.SAT.PolyTime

/-! Nondeterministic acceptance and time bounds on concrete stuck and fair-coin machines, and
guess-and-verify deciders for verifier `NP`, including empty instances. -/

namespace ComplexityTests.NondeterministicVerifiers

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### A stuck machine: time bounds do not force halting -/

/-- A machine with no transitions; its initial configuration is stuck. -/
private def stuck : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ _ := False

/-- Every computation path of `stuck` consists of its initial configuration. -/
private theorem time_stuck {input : List Bool} (p : stuck.ComputationPath input) : p.time = 0 := by
  by_contra h
  have hpos : 0 < p.length := Nat.pos_of_ne_zero h
  have hstep : stuck.Step (p.toRunPath (Fin.castSucc ⟨0, hpos⟩))
      (p.toRunPath (Fin.succ ⟨0, hpos⟩)) := p.step ⟨0, hpos⟩
  have hhead : p.toRunPath (Fin.castSucc ⟨0, hpos⟩) = stuck.initCfg input := p.head_eq
  rw [hhead] at hstep
  simp [MultiTapeNTM.Step, stuck] at hstep

/-- The time bound holds vacuously although no branch halts. -/
private theorem runsInTime_stuck (input : List Bool) : stuck.RunsInTime input 1 :=
  fun p hp => absurd (time_stuck p) (by omega)

/-- A stuck branch does not accept. -/
private theorem not_accepts_stuck (input : List Bool) : ¬stuck.Accepts input := by
  rw [MultiTapeNTM.accepts_iff_exists_time_eq (runsInTime_stuck input)]
  rintro ⟨p, hp, -⟩
  simp [time_stuck p] at hp

example : stuck.DecidesInTime encBits ∅ fun _ => 1 :=
  fun a => ⟨runsInTime_stuck a, by simpa using not_accepts_stuck a⟩

example : ¬(stuck.initCfg [] : Cfg 0 Bool Unit []).Halted := by simp [stuck]

/-! ### A fair coin as a nondeterministic machine -/

/-- Emit one fair bit and halt. -/
private def coin : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ bit := .step
    { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

/-- The configuration after one coin: halted, with the coin as output. -/
private def coinFinal (bit : Bool) (input : List Bool) : Cfg 0 Bool Unit input :=
  ⟨none, 1, fun _ _ => none, fun _ => 0, [bit]⟩

/-- One step with a given coin halts with that bit as output. -/
private theorem stepCoins_coin (bit : Bool) (input : List Bool) :
    coin.stepCoins [bit] (coin.toNTM.initCfg input) = coinFinal bit input := by
  simp only [MultiTapePTM.stepCoins, List.foldl_cons, List.foldl_nil]
  rw [MultiTapeTM.step_of_state rfl]
  apply Cfg.ext_zero_tapes <;>
    simp [MultiTapeMachine.toTM, MultiTapeMachine.Action.emptyOracleEquiv, MultiTapePTM.withCoin,
      coin, Action.apply, MultiTapePTM.toNTM, coinFinal]

/-- For each bit, a computation path of one step halts with that bit as output. -/
private theorem exists_path_coin (bit : Bool) (input : List Bool) :
    ∃ p : coin.toNTM.ComputationPath input, p.time = 1 ∧ p.last.Halted ∧ p.last.output = [bit] := by
  obtain ⟨p, hhead, hlen, hlast⟩ :=
    (coin.exists_runPath_toNTM_iff (c := coin.toNTM.initCfg input) (n := 1)).mpr
      ⟨[bit], rfl, rfl⟩
  have hfinal : (⟨p, hhead⟩ : coin.toNTM.ComputationPath input).last = coinFinal bit input :=
    hlast.trans (stepCoins_coin bit input)
  exact ⟨⟨p, hhead⟩, hlen, by rw [hfinal]; rfl, by rw [hfinal]; rfl⟩

/-- Both branches halt after one step. -/
private theorem runsInTime_coin (input : List Bool) : coin.toNTM.RunsInTime input 1 := by
  intro p hp
  have hlt : 1 < p.length + 1 := Nat.lt_succ_of_le hp
  have hstep : coin.toNTM.Step (p.toRunPath (Fin.castSucc ⟨0, hp⟩))
      (p.toRunPath (Fin.succ ⟨0, hp⟩)) := p.step ⟨0, hp⟩
  have hhead : p.toRunPath (Fin.castSucc ⟨0, hp⟩) = coin.toNTM.initCfg input := p.head_eq
  rw [hhead] at hstep
  obtain ⟨bit, hbit⟩ := (coin.step_toNTM_iff).mp hstep
  have hone : p.toRunPath ⟨1, hlt⟩ = coinFinal bit input :=
    hbit.symm.trans (stepCoins_coin bit input)
  have hhalt : (p.toRunPath ⟨1, hlt⟩).Halted := by rw [hone]; rfl
  exact (MultiTapeNTM.RunPath.last_eq_of_halted p.toRunPath _ hhalt) ▸ hhalt

example (input : List Bool) : coin.toNTM.Accepts input :=
  let ⟨p, _, hhalt, hout⟩ := exists_path_coin true input
  ⟨p, hhalt, hout⟩

/-- A rejecting branch exists beside the accepting one. -/
example (input : List Bool) :
    ∃ p : coin.toNTM.ComputationPath input, p.last.Halted ∧ p.last.output = [false] :=
  let ⟨p, _, hhalt, hout⟩ := exists_path_coin false input
  ⟨p, hhalt, hout⟩

/-- Halted self-loops: the accepting path also has exactly three steps. -/
example : ∃ p : coin.toNTM.ComputationPath [], p.time = 3 ∧ p.last.output = [true] :=
  (MultiTapeNTM.accepts_iff_exists_time_eq ((runsInTime_coin []).mono (by omega))).mp
    (let ⟨p, _, hhalt, hout⟩ := exists_path_coin true []; ⟨p, hhalt, hout⟩)

/-- The fair coin is never stuck, so its paths within the bound extend to halted ones. -/
example (input : List Bool) (p : coin.toNTM.ComputationPath input) (hp : p.time ≤ 1) :
    ∃ (q : coin.toNTM.ComputationPath input) (_ : q.time = 1), q.last.Halted ∧
      ∀ i (hi : i < p.length + 1), q.toRunPath ⟨i, by
        unfold MultiTapeNTM.ComputationPath.time MultiTapeNTM.RunPath.time at *; omega⟩ =
        p.toRunPath ⟨i, hi⟩ :=
  MultiTapeNTM.ComputationPath.exists_halted_extension (coin.exists_step_toNTM)
    (runsInTime_coin input) p hp

/-! ### A looping machine violates every time bound -/

/-- Stay in its only state forever. -/
private def loop : MultiTapeTM 0 Bool Unit :=
  MultiTapeTM.ofTr () fun _ _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := none, state := some () }

private theorem state_runFrom_loop (input : List Bool) (t : ℕ) :
    (loop.runFrom (loop.initCfg input) t).state = some () := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom, Function.iterate_succ_apply', ← MultiTapeTM.runFrom,
      MultiTapeTM.step_of_state ih]
    simp [loop, Action.apply]

example (input : List Bool) (t : ℕ) : ¬loop.toMultiTapeNTM.RunsInTime input t := by
  intro h
  have hhalt := h (MultiTapeNTM.ComputationPath.ofDeterministic loop input t) le_rfl
  rw [MultiTapeTM.computationPath_last_eq_runFrom] at hhalt
  have htime : (MultiTapeNTM.ComputationPath.ofDeterministic loop input t).time = t := rfl
  rw [htime, Cfg.Halted, state_runFrom_loop] at hhalt
  exact Option.some_ne_none _ hhalt

/-! ### A stuck branch beside an accepting one -/

/-- Halt with output `[true]`. -/
private def acceptAction : Action 0 Bool Bool :=
  { inputTape := 0, workTapes := Fin.elim0, output := some true, state := none }

/-- Move to the state `true`, which has no transitions. -/
private def stuckAction : Action 0 Bool Bool :=
  { inputTape := 0, workTapes := Fin.elim0, output := none, state := some true }

/-- From its initial state `false`, either accept or move to the stuck state `true`. -/
private def fork : MultiTapeNTM 0 Bool Bool where
  q₀ := false
  Tr q _ _ action := q = false ∧ (action = acceptAction ∨ action = stuckAction)

/-- The stuck branch does not prevent acceptance. -/
example (input : List Bool) : fork.Accepts input := by
  have hstep : fork.Step (fork.initCfg input) (acceptAction.apply (fork.initCfg input)) :=
    ⟨acceptAction, ⟨rfl, .inl rfl⟩, rfl⟩
  refine ⟨⟨(RelSeries.singleton _ _).cons (fork.initCfg input) hstep, rfl⟩, ?_, ?_⟩ <;>
    simp [acceptAction]

/-- After one step the stuck branch is still running, so one step is not a time bound. -/
example (input : List Bool) : ¬fork.RunsInTime input 1 := by
  have hstep : fork.Step (fork.initCfg input) (stuckAction.apply (fork.initCfg input)) :=
    ⟨stuckAction, ⟨rfl, .inr rfl⟩, rfl⟩
  intro h
  have := h ⟨(RelSeries.singleton _ _).cons (fork.initCfg input) hstep, rfl⟩
    (by simp [MultiTapeNTM.ComputationPath.time, MultiTapeNTM.RunPath.time])
  simp [Cfg.Halted, stuckAction] at this

/-- Two steps bound every branch: the stuck branch has no second step. -/
example (input : List Bool) : fork.RunsInTime input 2 := by
  intro p hp
  have hlen : 1 < p.length := hp
  have h₀ : fork.Step (p.toRunPath (Fin.castSucc ⟨0, by omega⟩))
      (p.toRunPath (Fin.succ ⟨0, by omega⟩)) := p.step ⟨0, by omega⟩
  have h₁ : fork.Step (p.toRunPath (Fin.castSucc ⟨1, hlen⟩))
      (p.toRunPath (Fin.succ ⟨1, hlen⟩)) := p.step ⟨1, hlen⟩
  have hhead : p.toRunPath (Fin.castSucc ⟨0, by omega⟩) = fork.initCfg input := p.head_eq
  have hone : p.toRunPath (Fin.succ ⟨0, by omega⟩) = p.toRunPath (Fin.castSucc ⟨1, hlen⟩) :=
    congrArg p.toRunPath (Fin.ext rfl)
  rw [hhead] at h₀
  rw [← hone] at h₁
  obtain ⟨action, ⟨-, haction⟩, hnext⟩ := h₀
  rcases haction with rfl | rfl
  · have hhalt : (p.toRunPath (Fin.succ ⟨0, by omega⟩)).Halted := by rw [hnext]; rfl
    exact (MultiTapeNTM.RunPath.last_eq_of_halted p.toRunPath _ hhalt) ▸ hhalt
  · rw [hnext] at h₁
    simp [MultiTapeNTM.Step, fork, stuckAction] at h₁

/-! ### Acceptance requires exactly the output `[true]` -/

/-- Emit `true` twice, then halt. -/
private def twice : MultiTapeTM 0 Bool (Fin 2) :=
  MultiTapeTM.ofTr 0 fun q _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := some true,
      state := if q = 0 then some 1 else none }

private theorem runFrom_twice (input : List Bool) :
    twice.runFrom (twice.initCfg input) 2 =
      ⟨none, 1, fun _ _ => none, fun _ => 0, [true, true]⟩ := by
  change twice.step (twice.step (twice.initCfg input)) = _
  rw [MultiTapeTM.step_of_state (cfg := twice.initCfg input) (q := 0) rfl,
    MultiTapeTM.step_of_state (q := 1) (by simp [twice, Action.apply])]
  apply Cfg.ext_zero_tapes <;> simp [twice, Action.apply]

/-- Every branch halts after two steps, with output `[true, true]`. -/
private theorem runsInTime_twice (input : List Bool) :
    twice.toMultiTapeNTM.RunsInTime input 2 :=
  MultiTapeTM.runsInTime_of_halted (by rw [runFrom_twice])

/-- Halting after emitting `[true, true]` does not accept. -/
example (input : List Bool) : ¬twice.toMultiTapeNTM.Accepts input := by
  rw [MultiTapeNTM.accepts_iff_exists_time_eq (runsInTime_twice input)]
  rintro ⟨p, hp, hout⟩
  have hlast := MultiTapeTM.computationPath_last_eq_runFrom p
  rw [show p.time = 2 from hp, runFrom_twice] at hlast
  simp [hlast] at hout

/-! ### Guess and verify -/

/-- `SAT`, whose certificates are genuine assignments, has a polynomial-time nondeterministic
decider. -/
example : MultiTapeNTM.DecidableInPolyTime SAT encCNF :=
  decidableInPolyTime_of_mem_NP SAT.mem_NP

/-- The verifier reading the first certificate bit. -/
private theorem polyTime_headD :
    ComputableTidilyInPolyTime (fun x : List Bool × List Bool => x.2.headD false)
      (encPair encBits encBits) encBool :=
  (ComputableTidilyInPolyTime.headD (encA := encBool) false).comp
    (ComputableTidilyInPolyTime.snd encBits encBits)

/-- With one-bit certificates, the decider accepts the empty instance only through the branch
guessing `[true]`. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State),
    machine.toNTM.Accepts [] := by
  obtain ⟨k, State, hfinite, machine, c, d, hdecides, -⟩ :=
    IsVerifier.exists_decidesInTime (enc := encBits) (p := 1) (A := Set.univ) polyTime_headD
      fun _ => ⟨fun _ => ⟨[true], by simp, rfl⟩, fun _ => trivial⟩
  exact ⟨k, State, hfinite, machine, ((hdecides []).2).mp trivial⟩

/-- With empty certificates, the same verifier rejects: the decider guesses exactly
`p (enc a).length` bits, so it cannot reach the accepting certificate `[true]`. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State),
    ¬machine.toNTM.Accepts [] := by
  obtain ⟨k, State, hfinite, machine, c, d, hdecides, -⟩ :=
    IsVerifier.exists_decidesInTime (enc := encBits) (p := 0) (A := ∅) polyTime_headD
      fun _ => by simp
  exact ⟨k, State, hfinite, machine, fun h => ((hdecides []).2).mpr h⟩

/-- The guessing decider of the trivial verifier accepts the empty instance. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State),
    machine.toNTM.Accepts [] := by
  obtain ⟨k, State, hfinite, machine, c, d, hdecides, -⟩ :=
    IsVerifier.exists_decidesInTime (enc := encBits) (p := 0) (A := Set.univ)
      (ComputableTidilyInPolyTime.const true) fun _ => by simp
  exact ⟨k, State, hfinite, machine, ((hdecides []).2).mp trivial⟩

/-- The guessing decider of the rejecting verifier rejects the empty instance, although every
branch halts within the explicit polynomial bound. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State)
    (t : ℕ), ¬machine.toNTM.Accepts [] ∧ machine.toNTM.RunsInTime [] t ∧
      ∀ input (cfg : Cfg k Bool State input), ∃ cfg', machine.toNTM.Step cfg cfg' := by
  obtain ⟨k, State, hfinite, machine, c, d, hdecides, htotal⟩ :=
    IsVerifier.exists_decidesInTime (enc := encBits) (p := 0) (A := ∅)
      (ComputableTidilyInPolyTime.const false) fun _ => by simp
  exact ⟨k, State, hfinite, machine, _, fun h => ((hdecides []).2).mpr h, (hdecides []).1,
    htotal⟩

/-- A verifier reading only its instance, under a pair encoding. -/
example : MultiTapeNTM.DecidableInPolyTime {a : Bool × ℕ | a.1 = true}
    (encPair encBool encNat) := by
  refine decidableInPolyTime_of_mem_NP ⟨0, fun x => x.1.1, ?_, fun a => by simp⟩
  exact (ComputableTidilyInPolyTime.fst encBool encNat).comp
    (ComputableTidilyInPolyTime.fst (encPair encBool encNat) encBits)

/-! ### Axioms -/

/--
info: 'Turing.MultiTapePTM.exists_runPath_toNTM_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.exists_runPath_toNTM_iff

/--
info: 'Turing.MultiTapePTM.mem_support_runClosedConfigFrom_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.mem_support_runClosedConfigFrom_iff

/--
info: 'Turing.MultiTapePTM.runsInTime_toNTM' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapePTM.runsInTime_toNTM

/--
info: 'Turing.MultiTapeNTM.accepts_iff_exists_time_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeNTM.accepts_iff_exists_time_eq

/--
info: 'Turing.MultiTapeNTM.ComputationPath.exists_halted_extension' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeNTM.ComputationPath.exists_halted_extension

/--
info: 'Cslib.Complexity.IsVerifier.exists_decidesInTime' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.IsVerifier.exists_decidesInTime

/--
info: 'Cslib.Complexity.decidableInPolyTime_of_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.decidableInPolyTime_of_mem_NP

end ComplexityTests.NondeterministicVerifiers
