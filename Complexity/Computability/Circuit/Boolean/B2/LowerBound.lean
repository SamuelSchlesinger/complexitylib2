/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.B2.Step
public import Complexity.Computability.Circuit.Program
public import Cslib.Computability.Circuit.Full
public import Mathlib.Data.Fin.VecNotation

/-!
# A `3.5 n` lower bound for affine dispersers over the full binary basis

**Theorem 4.1** of [Mishra and Santhanam][MishraSanthanam2026]: every circuit over the full
binary basis `B₂` computing an affine disperser for dimension `d` on `n` bits has at least
`3.5 n - 7 d` gates (`seven_mul_le_two_mul_size_add`).

The proof starts gate elimination from the circuit itself (`initialState`): its inputs are the
parameters, its gates the acyclic part, the affine system is empty and the parameter map is the
identity, so `a = n` and `W ≤ 2 |C| + 7 n`. Every valid state satisfies `14 a ≤ W + 14 d`
(`State.Valid.fourteen_mul_a_le`), by induction on `m + s` along the steps of Lemma 4.2
(`State.Valid.exists_step`), so `14 n ≤ 2 |C| + 7 n + 14 d`.

The circuits are those of cslib over `fullSignature 2 Bool`, where a constant also costs a gate;
the source lets circuits read constants for free, so the bound holds here a fortiori.

## Main definitions

* `Cslib.Circuits.Boolean.B2.initialState`: the initial state of gate elimination.

## Main results

* `Cslib.Circuits.Boolean.B2.State.Valid.fourteen_mul_a_le`: the potential bound.
* `Cslib.Circuits.Boolean.B2.seven_mul_le_two_mul_size_add`: Theorem 4.1.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.B2

open Cslib.Circuits Cslib.BitString

variable {n : ℕ} {f : BooleanFunction n}

/-! ### The potential bound -/

/-- Every valid state for an affine disperser for dimension `d` satisfies `14 a ≤ W + 14 d`:
apply Lemma 4.2 until `a ≤ d`, adding up `ΔW ≤ 14 Δa`. -/
theorem State.Valid.fourteen_mul_a_le {d : ℕ} (hf : IsAffineDisperser f d) :
    ∀ S : State n, S.Valid f → 14 * S.a ≤ S.W + 14 * d := by
  intro S
  induction h : S.m + S.s using Nat.strong_induction_on generalizing S with
  | _ k ih =>
    intro hS
    by_cases ha : S.a ≤ d
    · omega
    · obtain ⟨S', hstep⟩ := hS.exists_step hf (lt_of_not_ge ha)
      have := ih _ (h ▸ hstep.lt) S' rfl hstep.valid
      have := hstep.potential
      omega

/-! ### The initial state of a circuit -/

/-- The name of a wire of a circuit with `n` inputs: input `i` is `i` and gate `j` is `n + j`. -/
def wireName {g : ℕ} : Wire n g → ℕ
  | .input i => i
  | .gate j => n + j

/-- The gate of a line of a circuit over the full binary basis; a constant becomes a gate with
a constant operation. -/
def lineGate {g : ℕ} : Line (fullSignature 2 Bool) n g → Gate
  | ⟨.fn op, w⟩ => ⟨fun a b => op ![a, b], .node (wireName (w ⟨0, by simp [fullSignature]⟩)),
      .node (wireName (w ⟨1, by simp [fullSignature]⟩))⟩
  | ⟨.con c, _⟩ => ⟨fun _ _ => c, .const false, .const false⟩

theorem eval_lineGate {g : ℕ} (line : Line (fullSignature 2 Bool) n g) (val : ℕ → Bool) :
    (lineGate line).eval val =
      fullInterpretation line.op fun a => val (wireName (line.wires a)) := by
  obtain ⟨op | c, w⟩ := line
  · simp only [lineGate, Gate.eval, Arg.eval_node, fullInterpretation]
    congr 1
    funext a
    obtain ⟨_ | _ | k, ha⟩ := a
    · rfl
    · rfl
    · simp at ha
  · rfl

theorem reads_lineGate {g : ℕ} {line : Line (fullSignature 2 Bool) n g} {i : ℕ}
    (h : (lineGate line).Reads i) : ∃ a, wireName (line.wires a) = i := by
  obtain ⟨op | c, w⟩ := line
  · rcases h with h | h
    · exact ⟨_, Arg.node.inj h⟩
    · exact ⟨_, Arg.node.inj h⟩
  · rcases h with h | h <;> cases h

/-- The initial state of gate elimination for a circuit: its inputs are the parameters, its
gates are the acyclic part, the affine system is empty, there are no pairs and the parameter
map reads the inputs. -/
def initialState (C : Circuit (fullSignature 2 Bool) n 1) : State n where
  params := Finset.range n
  aux := ∅
  gates := Finset.Ico n (n + C.size)
  gate i := if h : n ≤ i ∧ i < n + C.size then lineGate (C.program.lines ⟨i - n, by omega⟩)
    else ⟨fun _ _ => false, .const false, .const false⟩
  eqns := ∅
  eqn _ := ⟨∅, false⟩
  out := ⟨.node (wireName (C.outputs 0)), false⟩
  pairs := ∅
  phi val := fun i => val i

theorem initialState_gate (C : Circuit (fullSignature 2 Bool) n 1) (k : Fin C.size) :
    (initialState C).gate (n + k) = lineGate (C.program.lines k) := by
  have h : n ≤ n + (k : ℕ) ∧ n + (k : ℕ) < n + C.size := ⟨Nat.le_add_right _ _, by omega⟩
  simp only [initialState, dite_eq_left h]
  congr 2
  exact Fin.ext (by simp)

theorem wireName_mem_live (C : Circuit (fullSignature 2 Bool) n 1) (w : Wire n C.size) :
    wireName w ∈ (initialState C).live := by
  cases w with
  | input i => simp [SemiCircuit.live, initialState, wireName]
  | gate j => simp [SemiCircuit.live, initialState, wireName]

/-- The initial state of a circuit computing `f` is valid. -/
theorem initialState_valid {C : Circuit (fullSignature 2 Bool) n 1}
    (hC : C.Computes fullInterpretation (single f)) : (initialState C).Valid f where
  wf :=
    { disjoint_params_aux := Finset.disjoint_empty_right _
      disjoint_params_gates := by
        rw [Finset.disjoint_left]
        intro i hi hg
        simp only [initialState, Finset.mem_range, Finset.mem_Ico] at hi hg
        omega
      disjoint_aux_gates := Finset.disjoint_empty_left _
      reads_lt := fun J hJ i hi hr => by
        simp only [initialState, Finset.mem_Ico] at hJ hi
        obtain ⟨k, rfl⟩ : ∃ k : Fin C.size, J = n + k := ⟨⟨J - n, by omega⟩, by simp; omega⟩
        rw [initialState_gate] at hr
        obtain ⟨a, ha⟩ := reads_lineGate hr
        cases hw : (C.program.lines k).wires a with
        | input i' => rw [hw] at ha; simp only [wireName] at ha; omega
        | gate j =>
          rw [hw] at ha
          simp only [wireName] at ha
          have := C.program.lt_of_lines_wires_eq_gate k a j hw
          rw [← ha]
          exact Nat.add_lt_add_left this n
      reads_live := fun J hJ i hr => by
        simp only [initialState, Finset.mem_Ico] at hJ
        obtain ⟨k, rfl⟩ : ∃ k : Fin C.size, J = n + k := ⟨⟨J - n, by omega⟩, by simp; omega⟩
        rw [initialState_gate] at hr
        obtain ⟨a, rfl⟩ := reads_lineGate hr
        exact wireName_mem_live C _
      terms_subset := fun e he => by simp [initialState] at he
      card_terms_le := fun e he => by simp [initialState] at he
      out_live := fun i hi => by
        cases hi
        exact wireName_mem_live C _
      solvable := fun u => ⟨u, fun _ _ => rfl, fun e he => by simp [initialState] at he⟩
      unique := fun _ _ _ _ _ v hv => by simp [initialState] at hv }
  pair_mem := fun pr hpr => by simp [initialState] at hpr
  pairs_disjoint := fun pr hpr => by simp [initialState] at hpr
  phi_congr := fun val val' h => funext fun i => h i (Finset.mem_range.2 i.2)
  phi_affine := fun k σ hσ _ u v w => funext fun i => congrFun (hσ u v w) i
  phi_injective := fun val val' h j hj => by
    have := congrFun h ⟨j, Finset.mem_range.1 hj⟩
    simpa [initialState] using this
  computes := fun val hval => by
    set x : Fin n → Bool := fun i => val i
    have htrace : (fun w => val (wireName w)) = C.program.trace fullInterpretation x := by
      refine Program.eq_trace_of_forall_gate (fun i => rfl) fun k => ?_
      have hk : n + (k : ℕ) ∈ (initialState C).gates := by
        simp only [initialState, Finset.mem_Ico]; omega
      have := hval.2 _ hk
      rw [initialState_gate, eval_lineGate] at this
      exact this
    have hout := congrFun (hC x) 0
    simp only [Circuit.eval, Function.comp_apply, single_apply] at hout
    change (val (wireName (C.outputs 0)) ^^ false) = f x
    rw [Bool.xor_false, ← hout, ← htrace]

theorem initialState_a (C : Circuit (fullSignature 2 Bool) n 1) : (initialState C).a = n := by
  simp [State.a, State.m, State.q, initialState]

theorem initialState_W_le (C : Circuit (fullSignature 2 Bool) n 1) :
    (initialState C).W ≤ 2 * C.size + 7 * n := by
  have hs : (initialState C).s = C.size := by
    simp [State.s, SemiCircuit.size, initialState]
  have hq : (initialState C).q = 0 := by simp [State.q, initialState]
  unfold State.W
  rw [hs, hq]
  have : ∑ x ∈ (initialState C).unpaired, weight ((initialState C).deg x) ≤ 7 * n := by
    calc ∑ x ∈ (initialState C).unpaired, weight ((initialState C).deg x)
        ≤ ∑ _x ∈ (initialState C).unpaired, 7 := Finset.sum_le_sum fun _ _ => weight_le_seven _
      _ = 7 * (initialState C).unpaired.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 7 * n := by
        have : (initialState C).unpaired.card ≤ n :=
          (Finset.card_filter_le _ _).trans (by simp [initialState])
        omega
  omega

/-! ### Theorem 4.1 -/

/-- **Theorem 4.1** of [Mishra and Santhanam][MishraSanthanam2026]: every circuit over the full
binary basis computing an affine disperser for dimension `d` on `n` bits has at least
`3.5 n - 7 d` gates, stated without subtraction as `7 n ≤ 2 |C| + 14 d`. -/
theorem seven_mul_le_two_mul_size_add {d : ℕ} (hf : IsAffineDisperser f d)
    (C : Circuit (fullSignature 2 Bool) n 1) (hC : C.Computes fullInterpretation (single f)) :
    7 * n ≤ 2 * C.size + 14 * d := by
  have h := State.Valid.fourteen_mul_a_le hf _ (initialState_valid hC)
  rw [initialState_a] at h
  have := initialState_W_le C
  omega

end Cslib.Circuits.Boolean.B2
