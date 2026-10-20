/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CircuitValue
public import Complexity.Computability.Complexity.Classes.LogSpace
public import Complexity.Computability.Circuit.Boolean.Tableau.Correct
public import Complexity.Computability.Circuit.Boolean.Tableau.Space
public import Complexity.Computability.Machines.ReadMachine.Tidy
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Run
import Mathlib.Data.List.GetD

/-!
# The circuit value problem is `P`-complete

**Ladner's theorem** [Ladner1975]: the circuit value problem is `P`-complete under
logarithmic-space many-one reductions [Arora and Barak, Section 6.7][AroraBarak09],
[Papadimitriou, Theorem 8.1][Papadimitriou94].

A problem `A ∈ P enc` is decided by a machine `tm` within `C (n + 1) ^ d` steps on encoded
instances of length `n`. The reduction maps an instance `a` to the tableau circuit of `tm` for
`C (n + 1) ^ d + n + 1` steps on inputs of length `n = |enc a|`
(`Cslib.Circuits.Boolean.Tableau.circuit`), together with the input `enc a`. The circuit outputs
whether `tm`, started on `enc a`, has written exactly `[true]` after that many steps
(`Cslib.Circuits.Boolean.Tableau.eval_circuit`); since `tm` has halted by then with the answer on
its output, this is whether `a ∈ A`. The circuit reads the bits of `enc a` as its inputs; it does
not hardwire them as constants. The reduction is
computable in logarithmic space: a read machine (`Turing.ReadMachine`) on the framed input counts
its length `n`, then writes the gates one by one, keeping only the number of the current gate,
since each gate is computed from its number within work space linear in the binary lengths of `n`,
the time bound and the number (`Cslib.Circuits.Boolean.Tableau.gateCode_inSpace`), and finally
copies the input.

## Main definitions

* `Cslib.Complexity.CircuitValue.tableauInstance`: the instance of the circuit value problem for
  an input of a machine.
* `Cslib.Complexity.CircuitValue.writer`: the read machine writing the instance.

## Main results

* `Cslib.Complexity.CircuitValue.run_writer`: the writer writes the encoded instance.
* `Cslib.Complexity.CircuitValue.computableInLogSpace_tableauInstance`: the instances are
  computable in logarithmic space.
* `Cslib.Complexity.CircuitValue.logSpaceHard`: the circuit value problem is `P`-hard under
  logarithmic-space reductions.
* `Cslib.Complexity.CircuitValue.logSpaceComplete`: the circuit value problem is `P`-complete
  under logarithmic-space reductions.
* `Cslib.Complexity.CircuitValue.mem_L_iff_forall_P_eq_L`: the circuit value problem is in `L`
  exactly when `P = L`.

## References

* [R. E. Ladner, *The circuit value problem is log space complete for P*][Ladner1975]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Sections 6.1 and 6.7][AroraBarak09]
* [C. H. Papadimitriou, *Computational Complexity*, Theorem 8.1][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing MultiTapeTM Circuits Circuits.Boolean

/-! ### Framed words -/

/-- Each bit preceded by `true`: `frame` without its closing `false`. -/
def dbl (l : List Bool) : List Bool := l.flatMap fun b => [true, b]

theorem frame_eq_dbl (l : List Bool) : frame l = dbl l ++ [false] := rfl

@[simp] theorem dbl_append (l l' : List Bool) : dbl (l ++ l') = dbl l ++ dbl l' :=
  List.flatMap_append

@[simp] theorem dbl_false : dbl [false] = [true, false] := rfl

theorem dbl_flatten (L : List (List Bool)) : dbl L.flatten = (L.map dbl).flatten := by
  induction L with
  | nil => rfl
  | cons l L ih => simp [ih]

theorem dbl_dbl_replicate (n : ℕ) :
    dbl (dbl (List.replicate n true)) = (List.replicate n [true, true, true, true]).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, dbl, ← ih]

theorem getD_frame_two_mul (w : List Bool) (i : ℕ) :
    (frame w).getD (2 * i) false = decide (i < w.length) := by
  induction w generalizing i with
  | nil => rcases i with _ | i <;> simp [frame_nil, List.getD_eq_getElem?_getD]
  | cons b w ih =>
    rcases i with _ | i
    · simp [frame_cons]
    · rw [frame_cons, show 2 * (i + 1) = 2 * i + 1 + 1 by omega, List.getD_cons_succ,
        List.getD_cons_succ, ih]
      simp

theorem getD_frame_two_mul_add_one (w : List Bool) (i : ℕ) :
    (frame w).getD (2 * i + 1) false = w.getD i false := by
  induction w generalizing i with
  | nil => rcases i with _ | i <;> simp [frame_nil, List.getD_eq_getElem?_getD]
  | cons b w ih =>
    rcases i with _ | i
    · simp [frame_cons]
    · rw [frame_cons, show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by omega, List.getD_cons_succ,
        List.getD_cons_succ, ih, List.getD_cons_succ]

theorem getElem?_frame_two_mul (w : List Bool) (i : ℕ) :
    ((frame w)[2 * i]?).getD false = decide (i < w.length) := by
  rw [← List.getD_eq_getElem?_getD, getD_frame_two_mul]

theorem getElem?_frame_two_mul_add_one (w : List Bool) (i : ℕ) :
    ((frame w)[2 * i + 1]?).getD false = (w[i]?).getD false := by
  rw [← List.getD_eq_getElem?_getD, getD_frame_two_mul_add_one, List.getD_eq_getElem?_getD]

namespace CircuitValue

/-! ### The writer -/

section Writer

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM k Bool State) (C d : ℕ)

/-- The number of steps of the tableau for inputs of length `n`: `C (n + 1) ^ d + n + 1`. -/
def timeBound (C d n : ℕ) : ℕ := C * (n + 1) ^ d + n + 1

/-- **The instance of the circuit value problem** for the input `w`: the tableau circuit of `tm`
for `timeBound C d |w|` steps on inputs of length `|w|`, with the input `w`. -/
noncomputable def tableauInstance (w : List Bool) : Σ n, Circuit signature n 1 × BitString n :=
  ⟨w.length, Tableau.circuit tm w.length (timeBound C d w.length), fun i => w[i]⟩

/-- Gate `i` of the tableau, as the writer emits it. -/
noncomputable def gateChunk (n i : ℕ) : List Bool :=
  dbl (dbl (frame (encGate (Tableau.gateCode tm n (timeBound C d n) i))))

variable (k State) in
/-- What the writer emits after the gates: the end of the gate list and the output wire. -/
noncomputable def trailer (n : ℕ) : List Bool :=
  [true, false] ++ dbl (frame (encNat (Tableau.outWire k State n (timeBound C d n)))) ++ [false]

/-- **The encoded instance**: the length in unary, the gates and the output wire, framed twice,
and the input. -/
theorem encCircuitValue_tableauInstance (w : List Bool) :
    encCircuitValue (tableauInstance tm C d w) =
      (List.replicate w.length [true, true, true, true]).flatten ++ [true, false] ++
        ((List.range (Tableau.numGates k State (timeBound C d w.length))).map
          (gateChunk tm C d w.length)).flatten ++ trailer k State C d w.length ++ w := by
  rw [encCircuitValue_apply]
  simp only [tableauInstance, Tableau.code_circuit, encPair_apply, encUnary_apply, encList_cons,
    encList_nil, List.append_nil, encBits_apply, frame_eq_dbl, dbl_append, Tableau.gates,
    trailer]
  have hw : List.ofFn (fun i : Fin w.length => w[i]) = w := List.ofFn_getElem
  rw [hw, dbl_dbl_replicate]
  have hl : encList encGate ((List.range (Tableau.numGates k State (timeBound C d w.length))).map
      (Tableau.gateCode tm w.length (timeBound C d w.length))) =
      ((List.range (Tableau.numGates k State (timeBound C d w.length))).map fun i =>
        frame (encGate (Tableau.gateCode tm w.length (timeBound C d w.length) i))).flatten := by
    generalize List.range (Tableau.numGates k State (timeBound C d w.length)) = L
    induction L with
    | nil => rfl
    | cons i L ih => simp [ih]
  have hc : gateChunk tm C d w.length = fun i =>
      dbl (dbl (dbl (encGate (Tableau.gateCode tm w.length (timeBound C d w.length) i)))) ++
        dbl (dbl [false]) := by
    funext i
    simp only [gateChunk, frame_eq_dbl, dbl_append]
  rw [hl, dbl_flatten, dbl_flatten, List.map_map, List.map_map, hc]
  simp only [frame_eq_dbl, Function.comp_def, dbl_append, List.append_assoc, dbl_false]

/-- The step of the writer. Its state is a phase, the length `n` of the input and a counter:
phase `0` counts the input, phase `1` writes the gates, phase `2` copies the input, phase `3`
halts. -/
noncomputable def writerStep (s : ℕ × ℕ × ℕ) (b : Bool) : (ℕ × ℕ × ℕ) × List Bool :=
  if s.1 = 0 then
    if b then ((0, 0, s.2.2 + 1), [true, true, true, true]) else ((1, s.2.2, 0), [true, false])
  else if s.1 = 1 then
    if s.2.2 < Tableau.numGates k State (timeBound C d s.2.1) then
      ((1, s.2.1, s.2.2 + 1), gateChunk tm C d s.2.1 s.2.2)
    else ((2, s.2.1, 0), trailer k State C d s.2.1)
  else if s.1 = 2 then
    if s.2.2 < s.2.1 then ((2, s.2.1, s.2.2 + 1), [b]) else ((3, s.2.1, 0), [])
  else (s, [])

/-- The read address of the writer: the markers `true` of the framed input while counting, the
input bits while copying. -/
def writerAddr (s : ℕ × ℕ × ℕ) : Option ℕ :=
  if s.1 = 0 then some (2 * s.2.2) else if s.1 = 2 then some (2 * s.2.2 + 1) else none

/-- **The writer**: on the framed input `frame w`, it writes the encoded instance
`encCircuitValue (tableauInstance tm C d w)`. -/
noncomputable def writer : ReadMachine (ℕ × ℕ × ℕ) where
  init := (0, 0, 0)
  halt s := decide (s.1 = 3)
  addr := writerAddr
  step := writerStep tm C d

/-- The number of steps of the writer on an input of length `n`. -/
noncomputable def writerRounds (n : ℕ) : ℕ :=
  (n + 1) + (Tableau.numGates k State (timeBound C d n) + 1) + (n + 1)

theorem readBit_writer_count (w : List Bool) (i : ℕ) :
    (writer tm C d).readBit (frame w) (0, 0, i) = decide (i < w.length) := by
  simp only [ReadMachine.readBit, writer, writerAddr, ↓reduceIte]
  exact getD_frame_two_mul w i

theorem readBit_writer_copy (w : List Bool) (n i : ℕ) :
    (writer tm C d).readBit (frame w) (2, n, i) = w.getD i false := by
  simp only [ReadMachine.readBit, writer, writerAddr, OfNat.ofNat_ne_zero, ↓reduceIte]
  exact getD_frame_two_mul_add_one w i

theorem run_writer (w : List Bool) :
    (writer tm C d).run (frame w) (writerRounds (k := k) (State := State) C d w.length) =
      ⟨(3, w.length, 0), encCircuitValue (tableauInstance tm C d w)⟩ := by
  -- counting
  have h₀ := (writer tm C d).runFrom_loop (frame w) (fun i => (0, 0, i))
    (fun _ => [true, true, true, true]) (M := w.length) (fun i hi => ⟨rfl, by
      rw [readBit_writer_count, decide_eq_true hi]; rfl⟩) [] le_rfl
  have h₀' (out : List Bool) : (writer tm C d).next (frame w) ⟨(0, 0, w.length), out⟩ =
      ⟨(1, w.length, 0), out ++ [true, false]⟩ := by
    rw [ReadMachine.next_of_not_halt _ _ rfl]
    simp only [readBit_writer_count, lt_self_iff_false, decide_false]
    rfl
  -- the gates
  have h₁ (out : List Bool) := (writer tm C d).runFrom_loop (frame w) (fun j => (1, w.length, j))
    (gateChunk tm C d w.length) (M := Tableau.numGates k State (timeBound C d w.length))
    (fun j hj => ⟨rfl, by
      change writerStep tm C d (1, w.length, j) ((writer tm C d).readBit (frame w) (1, w.length, j))
        = _
      simp only [writerStep, ↓reduceIte, hj, one_ne_zero]⟩) out le_rfl
  have h₁' (out : List Bool) : (writer tm C d).next (frame w)
      ⟨(1, w.length, Tableau.numGates k State (timeBound C d w.length)), out⟩ =
      ⟨(2, w.length, 0), out ++ trailer k State C d w.length⟩ := by
    rw [ReadMachine.next_of_not_halt _ _ rfl]
    change (⟨(writerStep tm C d (1, w.length, Tableau.numGates k State (timeBound C d w.length))
        ((writer tm C d).readBit (frame w)
          (1, w.length, Tableau.numGates k State (timeBound C d w.length)))).1,
      out ++ (writerStep tm C d (1, w.length, Tableau.numGates k State (timeBound C d w.length))
        ((writer tm C d).readBit (frame w)
          (1, w.length, Tableau.numGates k State (timeBound C d w.length)))).2⟩ :
      ReadMachine.Cfg (ℕ × ℕ × ℕ)) = _
    simp only [writerStep, one_ne_zero, ↓reduceIte, lt_self_iff_false]
  -- copying
  have h₂ (out : List Bool) := (writer tm C d).runFrom_loop (frame w) (fun i => (2, w.length, i))
    (fun i => [w.getD i false]) (M := w.length) (fun i hi => ⟨rfl, by
      rw [readBit_writer_copy]
      change writerStep tm C d (2, w.length, i) (w.getD i false) = _
      simp only [writerStep, OfNat.ofNat_ne_zero, ↓reduceIte, hi, OfNat.ofNat_ne_one]⟩) out le_rfl
  have h₂' (out : List Bool) : (writer tm C d).next (frame w) ⟨(2, w.length, w.length), out⟩ =
      ⟨(3, w.length, 0), out⟩ := by
    rw [ReadMachine.next_of_not_halt _ _ rfl]
    change (⟨(writerStep tm C d (2, w.length, w.length)
        ((writer tm C d).readBit (frame w) (2, w.length, w.length))).1,
      out ++ (writerStep tm C d (2, w.length, w.length)
        ((writer tm C d).readBit (frame w) (2, w.length, w.length))).2⟩ :
      ReadMachine.Cfg (ℕ × ℕ × ℕ)) = _
    simp only [writerStep, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one,
      lt_self_iff_false, List.append_nil]
  have hcopy : ((List.range w.length).map fun i => [w.getD i false]).flatten = w := by
    have hs (l : List ℕ) (f : ℕ → Bool) : (l.map fun i => [f i]).flatten = l.map f := by
      induction l with
      | nil => rfl
      | cons i l ih => simp [ih]
    rw [hs]
    refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
    simp [List.getElem?_eq_getElem h₂]
  set out₁ := [] ++ ((List.range w.length).map fun _ => [true, true, true, true]).flatten ++
    [true, false]
  set out₂ := out₁ ++ ((List.range (Tableau.numGates k State (timeBound C d w.length))).map
    (gateChunk tm C d w.length)).flatten ++ trailer k State C d w.length
  have hA : (writer tm C d).runFrom (frame w) ⟨(0, 0, 0), []⟩ (w.length + 1) =
      ⟨(1, w.length, 0), out₁⟩ := by
    rw [ReadMachine.runFrom_add, h₀, ReadMachine.runFrom_one, h₀']
  have hB : (writer tm C d).runFrom (frame w) ⟨(1, w.length, 0), out₁⟩
      (Tableau.numGates k State (timeBound C d w.length) + 1) = ⟨(2, w.length, 0), out₂⟩ := by
    rw [ReadMachine.runFrom_add, h₁, ReadMachine.runFrom_one, h₁']
  have hC : (writer tm C d).runFrom (frame w) ⟨(2, w.length, 0), out₂⟩ (w.length + 1) =
      ⟨(3, w.length, 0),
        out₂ ++ ((List.range w.length).map fun i => [w.getD i false]).flatten⟩ := by
    rw [ReadMachine.runFrom_add, h₂, ReadMachine.runFrom_one, h₂']
  rw [ReadMachine.run, writerRounds, show (writer tm C d).init = (0, 0, 0) from rfl,
    (writer tm C d).runFrom_add (frame w) _
      (w.length + 1 + (Tableau.numGates k State (timeBound C d w.length) + 1)) (w.length + 1),
    (writer tm C d).runFrom_add (frame w) _ (w.length + 1)
      (Tableau.numGates k State (timeBound C d w.length) + 1), hA, hB, hC,
    encCircuitValue_tableauInstance, hcopy]
  simp [out₂, out₁, List.map_const']

end Writer

/-! ### The writer in logarithmic space -/

section Space

open ComputableTidilyInSpace Tableau

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM k Bool State) (C d : ℕ)

/-- Doubles each bit after a `true`. -/
def dblT : Transducer Bool Unit where
  q₀ := ()
  step _ b := ((), [true, b])
  final _ := []
  length_step_le _ _ := by simp
  length_final_le _ := by simp

theorem dblT_run (l : List Bool) : dblT.run () l = dbl l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [Transducer.run_cons]
    change [true, b] ++ dblT.run () l = [true, b] ++ dbl l
    rw [ih]

theorem dbl_inSpace :
    ComputableTidilyInSpace dbl encBits encBits fun l => (encBits l).length :=
  of_inO (.of_linear (dblT.computableTidilyInLinearTimeAndSpace fun l => (dblT_run l).symm))

/-- The encoding of the states of the writer. -/
abbrev encWState : ℕ × ℕ × ℕ ↪ List Bool := encPair encNat (encPair encNat encNat)

/-- The space budget of a state of the writer: the length of its encoding. -/
def wBudget (s : ℕ × ℕ × ℕ) : ℕ := (encWState s).length + 1

section Components

variable {α : Type} {encIn : α ↪ List Bool} {Bs : α → ℕ}
  (hin : (fun x => (encIn x).length) ≼ Bs)
include hin

theorem timeBound_inSpace {n : α → ℕ} (hn : ComputableTidilyInSpace n encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => timeBound C d (n x)) encIn encNat Bs :=
  add_inSpace (add_inSpace (mul_inSpace (budget_const C hin)
    (pow_inSpace (add_inSpace hn (budget_const 1 hin)) hin d)) hn) (budget_const 1 hin)

omit [DecidableEq State] in
theorem numGates_inSpace {T : α → ℕ} (hT : ComputableTidilyInSpace T encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => numGates k State (T x)) encIn encNat Bs :=
  add_inSpace (budget_const 2 hin) (mul_inSpace (add_inSpace hT (budget_const 1 hin))
    (blockSize_inSpace (k := k) (State := State) hT hin))

theorem gateChunk_inSpace {n i : α → ℕ} (hn : ComputableTidilyInSpace n encIn encNat Bs)
    (hi : ComputableTidilyInSpace i encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => gateChunk tm C d (n x) (i x)) encIn encBits Bs := by
  have hframe : ComputableTidilyInSpace (fun g => frame (encGate g)) encGate encBits
      fun g => (encGate g).length :=
    of_inO (.of_linear (.of_frame fun _ => rfl))
  exact budget_comp_linear dbl_inSpace (budget_comp_linear dbl_inSpace
    (budget_comp_linear (g := fun g => frame (encGate g)) hframe
      (gateCode_inSpace tm hn (timeBound_inSpace C d hin hn) hin hi)))

omit [DecidableEq State] in
theorem trailer_inSpace {n : α → ℕ} (hn : ComputableTidilyInSpace n encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => trailer k State C d (n x)) encIn encBits Bs := by
  have hT := timeBound_inSpace C d hin hn
  have ho : ComputableTidilyInSpace (fun x => outWire k State (n x) (timeBound C d (n x)))
      encIn encNat Bs :=
    add_inSpace (add_inSpace (add_inSpace hn (budget_const 2 hin))
      (mul_inSpace hT (blockSize_inSpace (k := k) (State := State) hT hin)))
      (add_inSpace (gfStart_inSpace (k := k) (State := State) hT hin) (budget_const _ hin))
  have hframe : ComputableTidilyInSpace (fun m => frame (encNat m)) encNat encBits
      fun m => (encNat m).length :=
    of_inO (.of_linear (.of_frame fun _ => rfl))
  have hmid := budget_comp_linear dbl_inSpace
    (budget_comp_linear (g := fun m => frame (encNat m)) hframe ho)
  have h₁ := (budget_const (encB := encBits) [true, false] hin).append hmid
    (g := fun x => [true, false] ++ dbl (frame (encNat (outWire k State (n x)
      (timeBound C d (n x)))))) (encD := encBits) fun _ => rfl
  have h₂ := (h₁.weaken (.add (.refl _) (.refl _))).append
    (budget_const (encB := encBits) [false] hin) (encD := encBits)
    (g := fun x => trailer k State C d (n x)) fun _ => rfl
  exact h₂.weaken (.add (.refl _) (.refl _))

end Components

theorem writerHalt_inSpace :
    ComputableTidilyInSpace (writer tm C d).halt encWState encBool wBudget := by
  have hin : (fun s => (encWState s).length) ≼ wBudget := .of_le fun _ => by
    simp only [wBudget]; omega
  have hph := (ComputableTidilyInSpace.fst encNat (encPair encNat encNat)).weaken hin
  exact eq_inSpace hph (budget_const (encB := encNat) 3 hin)

theorem writerAddr_inSpace :
    ComputableTidilyInSpace writerAddr encWState (encOption encNat) wBudget := by
  have hin : (fun s => (encWState s).length) ≼ wBudget := .of_le fun _ => by
    simp only [wBudget]; omega
  have hph := (ComputableTidilyInSpace.fst encNat (encPair encNat encNat)).weaken hin
  have hi := snd' ((ComputableTidilyInSpace.snd encNat (encPair encNat encNat)).weaken hin)
  have hsome {a : ℕ × ℕ × ℕ → ℕ} (ha : ComputableTidilyInSpace a encWState encNat wBudget) :
      ComputableTidilyInSpace (fun s => some (a s)) encWState (encOption encNat) wBudget :=
    budget_comp_linear (of_inO (ComputableTidilyInDegree.optionSome (enc₁ := encNat)).inO_one) ha
  have h2i := mul_inSpace (budget_const (encB := encNat) 2 hin) hi
  refine (budget_ite (eq_inSpace hph (budget_const (encB := encNat) 0 hin)) (hsome h2i)
    (budget_ite (eq_inSpace hph (budget_const (encB := encNat) 2 hin))
      (hsome (add_inSpace h2i (budget_const 1 hin)))
      (budget_const (encB := encOption encNat) none hin))).of_enc_eq fun s => ?_
  simp only [writerAddr, decide_eq_true_eq]

theorem writerStep_inSpace :
    ComputableTidilyInSpace (fun p : (ℕ × ℕ × ℕ) × Bool => writerStep tm C d p.1 p.2)
      (encPair encWState encBool) (encPair encWState encBits) fun p => wBudget p.1 := by
  have hin : (fun p => (encPair encWState encBool p).length) ≼ fun p => wBudget p.1 :=
    .of_le_linear 2 0 fun p => by
      simp only [length_encPair, encBool_apply, wBudget]
      simp only [encNat_apply, List.length_cons, List.length_nil, zero_add, add_zero,
        Order.add_one_le_iff]
      omega
  have hs := (ComputableTidilyInSpace.fst encWState encBool).weaken hin
  have hb := (ComputableTidilyInSpace.snd encWState encBool).weaken hin
  have hph := fst' hs
  have hn := fst' (snd' hs)
  have hi := snd' (snd' hs)
  have hst {a b c : (ℕ × ℕ × ℕ) × Bool → ℕ}
      (ha : ComputableTidilyInSpace a (encPair encWState encBool) encNat fun p => wBudget p.1)
      (hb : ComputableTidilyInSpace b (encPair encWState encBool) encNat fun p => wBudget p.1)
      (hc : ComputableTidilyInSpace c (encPair encWState encBool) encNat fun p => wBudget p.1) :
      ComputableTidilyInSpace (fun p => (a p, b p, c p)) (encPair encWState encBool) encWState
        fun p => wBudget p.1 :=
    budget_prod ha (budget_prod hb hc)
  have hc (m : ℕ) := budget_const (encB := encNat) m hin
  have hw (l : List Bool) := budget_const (encB := encBits) l hin
  have hsucc := add_inSpace hi (hc 1)
  have hN := numGates_inSpace (k := k) (State := State) hin (timeBound_inSpace C d hin hn)
  have hbit : ComputableTidilyInSpace (fun p : (ℕ × ℕ × ℕ) × Bool => [p.2])
      (encPair encWState encBool) encBits fun p => wBudget p.1 := hb.of_enc_eq fun _ => rfl
  refine (budget_ite (eq_inSpace hph (hc 0))
    (budget_ite hb (budget_prod (hst (hc 0) (hc 0) hsucc) (hw [true, true, true, true]))
      (budget_prod (hst (hc 1) hi (hc 0)) (hw [true, false])))
    (budget_ite (eq_inSpace hph (hc 1))
      (budget_ite (lt_inSpace hi hN)
        (budget_prod (hst (hc 1) hn hsucc) (gateChunk_inSpace tm C d hin hn hi))
        (budget_prod (hst (hc 2) hn (hc 0))
          (trailer_inSpace (k := k) (State := State) C d hin hn)))
      (budget_ite (eq_inSpace hph (hc 2))
        (budget_ite (lt_inSpace hi hn) (budget_prod (hst (hc 2) hn hsucc) hbit)
          (budget_prod (hst (hc 3) hn (hc 0)) (hw [])))
        (budget_prod hs (hw []))))).of_enc_eq fun p => ?_
  simp only [writerStep, decide_eq_true_eq]

/-- The states of the writer on an input of length `n`, with `N` gates. -/
def WInv (n N : ℕ) (s : ℕ × ℕ × ℕ) : Prop :=
  (s.1 = 0 ∧ s.2.1 = 0 ∧ s.2.2 ≤ n) ∨ (s.1 = 1 ∧ s.2.1 = n ∧ s.2.2 ≤ N) ∨
    (s.1 = 2 ∧ s.2.1 = n ∧ s.2.2 ≤ n) ∨ (s.1 = 3 ∧ s.2.1 = n ∧ s.2.2 = 0)

/-- The states of the writer along its run. -/
theorem wInv_run (w : List Bool) (j : ℕ) :
    WInv w.length (numGates k State (timeBound C d w.length))
      ((writer tm C d).run (frame w) j).state := by
  induction j with
  | zero => exact Or.inl ⟨rfl, rfl, Nat.zero_le _⟩
  | succ j ih =>
    rw [ReadMachine.run, ReadMachine.runFrom, Function.iterate_succ_apply', ← ReadMachine.runFrom,
      ← ReadMachine.run]
    generalize (writer tm C d).run (frame w) j = cfg at ih ⊢
    obtain ⟨⟨ph, nn, i⟩, out⟩ := cfg
    simp only [WInv] at ih
    rcases ih with ⟨rfl, rfl, hi⟩ | ⟨rfl, rfl, hi⟩ | ⟨rfl, rfl, hi⟩ | ⟨rfl, rfl, rfl⟩
    · rw [ReadMachine.next_of_not_halt _ _ rfl, readBit_writer_count]
      rcases Nat.lt_or_ge i w.length with h | h
      · simp only [decide_eq_true h]
        exact Or.inl ⟨rfl, rfl, h⟩
      · simp only [decide_eq_false (Nat.not_lt.2 h)]
        exact Or.inr (Or.inl ⟨rfl, by
          simp only [writer, writerStep, ↓reduceIte, Bool.false_eq_true]; omega, Nat.zero_le _⟩)
    · rw [ReadMachine.next_of_not_halt _ _ rfl]
      change WInv _ _ (writerStep tm C d (1, w.length, i) _).1
      rcases Nat.lt_or_ge i (numGates k State (timeBound C d w.length)) with h | h
      · simp only [writerStep, one_ne_zero, ↓reduceIte, h]
        exact Or.inr (Or.inl ⟨rfl, rfl, h⟩)
      · simp only [writerStep, one_ne_zero, ↓reduceIte, Nat.not_lt.2 h]
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Nat.zero_le _⟩))
    · rw [ReadMachine.next_of_not_halt _ _ rfl]
      change WInv _ _ (writerStep tm C d (2, w.length, i) _).1
      rcases Nat.lt_or_ge i w.length with h | h
      · simp only [writerStep, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, h]
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h⟩))
      · simp only [writerStep, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one,
          Nat.not_lt.2 h]
        exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
    · rw [show (writer tm C d).next (frame w) ⟨(3, w.length, 0), out⟩ =
        ⟨(3, w.length, 0), out⟩ by simp [ReadMachine.next, writer]]
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))

theorem le_of_wInv {n N : ℕ} {s : ℕ × ℕ × ℕ} (h : WInv n N s) :
    s.1 ≤ 3 ∧ s.2.1 ≤ n ∧ s.2.2 ≤ n + N := by
  rcases h with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ <;> omega

end Space

/-! ### The reduction in logarithmic space -/

section LogSpace

open Tableau

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM k Bool State) (C d : ℕ)

theorem tidy_writer : ∃ T, (writer tm C d).toStepMachine.Tidy (encPair encWState encNat)
    (ReadMachine.stateT encWState T wBudget) (ReadMachine.stateS encWState wBudget) := by
  obtain ⟨T₁, h₁⟩ := writerHalt_inSpace tm C d
  obtain ⟨T₂, h₂⟩ := writerAddr_inSpace
  obtain ⟨T₃, h₃⟩ := writerStep_inSpace tm C d
  let T : ℕ × ℕ × ℕ → ℕ := fun s => T₁ s + T₂ s + T₃ (s, false) + T₃ (s, true)
  exact ⟨T, ReadMachine.tidy_toStepMachine
    (h₁.mono_le (fun s => by simp only [T]; omega) fun _ => le_rfl)
    (h₂.mono_le (fun s => by simp only [T]; omega) fun _ => le_rfl)
    (h₃.mono_le (fun p => by rcases p with ⟨s, _ | _⟩ <;> simp only [T] <;> omega)
      fun _ => le_rfl)⟩

variable (k State) in
/-- A bound on the numbers held by the writer and on the position of its head, on inputs of
length `n`. -/
noncomputable def wMax (n : ℕ) : ℕ := numGates k State (timeBound C d n) + 3 * n + 5

omit [DecidableEq State] in
theorem stateS_le (w : List Bool) {q : (ℕ × ℕ × ℕ) × ℕ}
    (hq : WInv w.length (numGates k State (timeBound C d w.length)) q.1)
    (hpos : q.2 ≤ (frame w).length + 1) :
    ReadMachine.stateS encWState wBudget q ≤
      30 * ((encNat (wMax k State C d w.length)).length + 1) := by
  obtain ⟨h₁, h₂, h₃⟩ := le_of_wInv hq
  rw [length_frame] at hpos
  have hm (a : ℕ) (ha : a ≤ wMax k State C d w.length) :
      (encNat a).length ≤ (encNat (wMax k State C d w.length)).length :=
    ComputableTidilyInO.length_encNat_mono ha
  have e₁ := hm q.1.1 (by simp only [wMax]; omega)
  have e₂ := hm q.1.2.1 (by simp only [wMax]; omega)
  have e₃ := hm q.1.2.2 (by simp only [wMax]; omega)
  have e₄ := hm q.2 (by simp only [wMax]; omega)
  simp only [ReadMachine.stateS, wBudget, length_encPair]
  omega

omit [DecidableEq State] in
theorem polynomiallyBounded_wMax : PolynomiallyBounded (wMax k State C d) := by
  change PolynomiallyBounded fun n => wMax k State C d n
  simp only [wMax, numGates, blockSize, colStart, gfStart, globStart, numCols, timeBound]
  fun_prop

/-- A number below a polynomial in `L` has a binary length logarithmic in `L`. -/
theorem length_encNat_le_log {M A D L : ℕ} (h : M ≤ A * (L + 1) ^ D) :
    (encNat M).length ≤ (Nat.size A + 2 * D + 1) * (Nat.log2 L + 1) := by
  have hpow (a D : ℕ) : (encNat (a ^ D)).length ≤ D * (encNat a).length + 1 := by
    induction D with
    | zero => simp
    | succ D ih =>
      rw [pow_succ]
      have := length_encNat_mul_le (a ^ D) a
      rw [Nat.succ_mul]
      omega
  have hL : (encNat (L + 1)).length ≤ Nat.log2 L + 2 := by
    rw [length_encNat_eq_size, Nat.size_le]
    have := Nat.lt_log2_self (n := L)
    rw [pow_succ]
    omega
  have h₁ := (ComputableTidilyInO.length_encNat_mono h).trans (length_encNat_mul_le _ _)
  have h₂ := hpow (L + 1) D
  rw [← length_encNat_eq_size]
  have : D * (encNat (L + 1)).length ≤ D * (Nat.log2 L + 2) := Nat.mul_le_mul_left _ hL
  nlinarith

/-- **The instances are computable in logarithmic space**, from the framed input. -/
theorem computableInLogSpace_tableauInstance :
    ComputableInLogSpace (tableauInstance tm C d) (encFramed encBits) encCircuitValue := by
  obtain ⟨T, hT⟩ := tidy_writer tm C d
  have hc (w : List Bool) : (writer tm C d).toStepMachine.Computes (encFramed encBits w)
      (encCircuitValue (tableauInstance tm C d w)) := by
    have hrun := run_writer (k := k) (State := State) tm C d w
    have := ReadMachine.computes_toStepMachine (m := writer tm C d) (x := frame w)
      (n := writerRounds (k := k) (State := State) C d w.length) (by rw [hrun]; rfl)
    rwa [hrun] at this
  choose rounds hr ho using hc
  obtain ⟨A, D, hAD⟩ := polynomiallyBounded_iff_le.1 (polynomiallyBounded_wMax (k := k)
    (State := State) C d)
  let tS := ReadMachine.stateT encWState T wBudget
  let tMax (w : List Bool) : ℕ := ∑ i ∈ Finset.range (rounds w + 1),
    tS ((writer tm C d).toStepMachine.run (encFramed encBits w) i).state
  have hbig := hT.computableTidilyInTimeAndSpace (tableauInstance tm C d) rounds hr
    (fun w => (ho w).symm) (tMax := tMax)
    (sMax := fun w => 30 * ((encNat (wMax k State C d w.length)).length + 1))
    fun w i hi => ⟨Finset.single_le_sum (f := fun i => tS ((writer tm C d).toStepMachine.run
      (encFramed encBits w) i).state) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega)),
      by
        obtain ⟨j, hq, hpos⟩ := ReadMachine.exists_state_run (m := writer tm C d)
          (encFramed encBits w) i
        rw [hq]
        exact stateS_le C d w (wInv_run tm C d w j) (by simpa using hpos)⟩
  obtain ⟨c, hc⟩ := hbig
  refine ⟨_, c * (31 * (Nat.size A + 2 * D + 2)), hc.computableInTimeAndSpace.mono
    (fun _ => le_rfl) fun w => ?_⟩
  have hM : wMax k State C d w.length ≤ A * ((encFramed encBits w).length + 1) ^ D :=
    (hAD w.length).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by
      simp only [encFramed_apply, encBits_apply, length_frame]; omega) D))
  have hl := length_encNat_le_log hM
  have hX : 1 ≤ Nat.log2 (encFramed encBits w).length + 1 := by omega
  beta_reduce
  generalize Nat.log2 (encFramed encBits w).length + 1 = X at hl hX ⊢
  generalize (encNat (wMax k State C d w.length)).length = L at hl ⊢
  generalize Nat.size A + 2 * D = B at hl ⊢
  rw [Nat.mul_assoc]
  refine Nat.mul_le_mul_left c ?_
  nlinarith

end LogSpace

/-! ### `P`-completeness -/

/-- Frames its input. -/
def frameTr : Transducer Bool Unit where
  q₀ := ()
  step _ b := ((), [true, b])
  final _ := [false]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

theorem frameTr_run (l : List Bool) : frameTr.run () l = frame l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [Transducer.run_cons, frame_cons]
    change [true, b] ++ frameTr.run () l = _
    rw [ih]
    rfl

/-- **Framing an encoded instance** takes no work space. -/
theorem computableInLogSpace_frame {α : Type} (enc : α ↪ List Bool) :
    ComputableInLogSpace (fun a => enc a) enc (encFramed encBits) := by
  have h := frameTr.computableTidilyInTimeAndSpace (encOut := encFramed encBits)
    (f := fun a => enc a) fun a => by rw [encFramed_apply, encBits_apply, frameTr_run]
  exact ⟨_, 0, h.computableInTimeAndSpace.mono (fun _ => le_rfl) fun _ => Nat.zero_le _⟩

/-- **Every problem in `P` reduces to the circuit value problem in logarithmic space**: an
instance is mapped to the tableau circuit of a polynomial-time decider on inputs of the length of
the encoded instance, with the encoded instance as its input. -/
theorem logSpaceReducible_of_mem_P {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ P enc) : LogSpaceReducible enc encCircuitValue A CircuitValue := by
  obtain ⟨f, ⟨t, s, ht, -, k, State, hfin, tm, htm⟩, hAf⟩ := hA
  have := Fintype.ofFinite State
  classical
  obtain ⟨C, d, htle⟩ := ht.exists_le
  refine ⟨fun a => tableauInstance tm C d (enc a),
    (computableInLogSpace_tableauInstance tm C d).comp (computableInLogSpace_frame enc),
    fun a => ?_⟩
  rw [hAf a, mem_CircuitValue]
  simp only [tableauInstance]
  have hw : List.ofFn (fun i : Fin (enc a).length => (enc a)[i]) = enc a := List.ofFn_getElem
  rw [Tableau.eval_circuit tm (by simp only [timeBound]; omega), hw]
  obtain ⟨hhalt, hout⟩ := ComputesTidilyInTimeAndSpace.runFrom_initCfg (htm a)
  have hle : t a ≤ timeBound C d (enc a).length := by
    have := htle a
    simp only [timeBound]
    omega
  rw [MultiTapeTM.runFrom_eq_of_halt tm _ hle hhalt, hout, encBool_apply]
  cases f a <;> simp [OutView.ofList]

/-- **The circuit value problem is `P`-hard under logarithmic-space reductions** [Ladner1975]. -/
theorem logSpaceHard : LogSpaceHard @P encCircuitValue CircuitValue :=
  fun _ _ hA => logSpaceReducible_of_mem_P hA

/-- **Ladner's theorem: the circuit value problem is `P`-complete under logarithmic-space
reductions** [Ladner1975], [Arora and Barak, Section 6.7][AroraBarak09]. -/
theorem logSpaceComplete : LogSpaceComplete @P encCircuitValue CircuitValue :=
  ⟨mem_P, logSpaceHard⟩

/-- **The circuit value problem is in `L` exactly when `P = L`**, for every encoding of instances
[Arora and Barak, Section 6.7][AroraBarak09]. -/
theorem mem_L_iff_forall_P_eq_L :
    CircuitValue ∈ L encCircuitValue ↔ ∀ {α : Type} (enc : α ↪ List Bool), P enc = L enc := by
  constructor
  · intro h α enc
    ext A
    exact ⟨fun hA => (logSpaceReducible_of_mem_P hA).mem_L h, fun hA => L_subset_P hA⟩
  · intro h
    rw [← h]
    exact mem_P

end CircuitValue

end Cslib.Complexity
