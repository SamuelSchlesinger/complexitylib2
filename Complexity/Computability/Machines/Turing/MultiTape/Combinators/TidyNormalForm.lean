/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (after #1126)

public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ClearShadowed
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindInput
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fin.Tuple.Embedding
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapesView
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.SequentialSpace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The tidy normal form

Every computation can be made tidy (`Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`) at a
linear cost in time and space: `tidy m₀ m₁ tm` runs `tm` with every work tape shadowed
(`Turing.MultiTapeTM.shadow`), then clears each work tape along its shadow
(`Turing.MultiTapeTM.clearShadowed`), and finally rewinds the input head
(`Turing.MultiTapeTM.rewindInput`); the symbols `m₀ ≠ m₁` mark the shadows. A computation of `tm`
within `t` steps and `s` cells becomes a tidy computation of `tidy m₀ m₁ tm` within
`2 t + 3 s + 2 k + 4` steps (`ComputesInTimeAndSpace.computesTidily_tidy`). So tidiness, which
makes machines composable, is no restriction on what is computable within given resources up to
constant factors (`ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace`).

The shadow tapes are needed because a work tape may hold blanks among the cells `tm` has written:
sweeping until the first blank would not find them all.

## Main definitions

* `Turing.MultiTapeTM.clearList`: clear a list of work tapes along their shadows.
* `Turing.MultiTapeTM.tidy`: the tidy normal form of a machine.

## Main results

* `Turing.MultiTapeTM.ComputesInTimeAndSpace.computesTidily_tidy`: `tidy m₀ m₁ tm` computes
  tidily what `tm` computes.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace`: computable
  functions are tidily computable.
-/

@[expose] public section

/-- The tapes `0, …, k - 1` and `k, …, 2 k - 1` of `Fin (k + k)` are distinct. -/
theorem Fin.castAdd_ne_natAdd {k : ℕ} (i j : Fin k) : Fin.castAdd k i ≠ Fin.natAdd k j := by
  simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
  omega

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol : Type*} [DecidableEq Symbol] {input : List Symbol} {m₀ m₁ : Symbol}

/-! ### Clearing a work tape and its shadow -/

/-- The embedding of work tape `i` and its shadow `k + i`. -/
def pairEmb (i : Fin k) : Fin 2 ↪ Fin (k + k) :=
  Function.Embedding.embFinTwo (Fin.castAdd_ne_natAdd i i)

@[simp] theorem pairEmb_zero (i : Fin k) : pairEmb i 0 = Fin.castAdd k i := rfl

theorem pairEmb_one (i : Fin k) : pairEmb i 1 = Fin.natAdd k i := rfl

/-- The tapes of the pair `i` are work tape `i` and its shadow. -/
theorem pairIdx_eq_iff {j : Fin (k + k)} {i : Fin k} :
    pairIdx j = i ↔ j = Fin.castAdd k i ∨ j = Fin.natAdd k i := by
  refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
  · simp only [pairIdx_castAdd, Fin.castAdd_inj, Fin.castAdd_ne_natAdd, or_false]
  · simp only [pairIdx_natAdd, Fin.natAdd_inj, (Fin.castAdd_ne_natAdd _ _).symm, false_or]

/-- Tape `j` is a tape of the pair `i` exactly when it is work tape `i` or its shadow. -/
theorem partialInv_pairEmb (i : Fin k) (j : Fin (k + k)) :
    partialInv (pairEmb i) j =
      if j = Fin.castAdd k i then some 0 else if j = Fin.natAdd k i then some 1 else none := by
  split_ifs with h₀ h₁
  · exact h₀ ▸ partialInv_embed (pairEmb i) 0
  · exact h₁ ▸ partialInv_embed (pairEmb i) 1
  · refine partialInv_eq_none _ ?_
    rintro ⟨a, rfl⟩
    fin_cases a <;> simp_all [pairEmb_one]

variable {σ σ' : Type*}

/-- Work tape `i` of `C` and its shadow `k + i` are ready to be cleared: the heads of both are on
cell `c - a`, the shadow marks cells `V` that together with `c - a` form the interval `[-a, b]`,
and the work tape is blank outside it. -/
structure PairReady (m₀ m₁ : Symbol) (C : Cfg (k + k) Symbol σ input) (i : Fin k) (a b c : ℕ)
    (V : Finset ℤ) : Prop where
  /-- The head of the work tape is on cell `c - a`. -/
  pos_castAdd : C.workTapePos (Fin.castAdd k i) = c - a
  /-- The head of the shadow is on cell `c - a`. -/
  pos_natAdd : C.workTapePos (Fin.natAdd k i) = c - a
  /-- The marked cells and the cell under the heads form the interval `[-a, b]`. -/
  insert_eq : insert ((c : ℤ) - a) V = Finset.Icc (-(a : ℤ)) b
  /-- The shadow marks the cells `V`. -/
  shadow_eq : C.workTapes (Fin.natAdd k i) = shadowTape m₀ m₁ V
  /-- The work tape is blank outside `[-a, b]`. -/
  blank : ∀ y ∉ Finset.Icc (-(a : ℤ)) b, C.workTapes (Fin.castAdd k i) y = none

/-- `C`, halted, with the work tapes in `l` and their shadows blank and their heads on the start
cell. -/
def clearedCfg (l : List (Fin k)) (C : Cfg (k + k) Symbol σ input) :
    Cfg (k + k) Symbol σ' input :=
  ⟨none, C.inputPos, fun j => if pairIdx j ∈ l then fun _ => none else C.workTapes j,
    fun j => if pairIdx j ∈ l then 0 else C.workTapePos j, C.output⟩

/-- **Clearing one work tape and its shadow** inside a machine with `k + k` work tapes. -/
theorem runFrom_clearShadowed_pairEmb (hm : m₀ ≠ m₁) {C : Cfg (k + k) Symbol σ input} {i : Fin k}
    {a b c : ℕ} {V : Finset ℤ} (h : PairReady m₀ m₁ C i a b c V) :
    ((clearShadowed m₀ m₁).extendTapes (pairEmb i)).runFrom (C.withState (some .start))
        (a + 2 * b + c + 5) = clearedCfg [i] C := by
  have hview : viewCfg (pairEmb i) (C.withState (some .start)) =
      ClearShadowed.cfg (some .start) C.inputPos (C.workTapes (Fin.castAdd k i))
        (shadowTape m₀ m₁ V) (c - a) C.output := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext j <;> fin_cases j
    · rfl
    · exact h.shadow_eq
    · exact h.pos_castAdd
    · exact h.pos_natAdd
  rw [runFrom_extendTapes, hview, runFrom_clearShadowed hm h.insert_eq h.blank]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext j <;>
    simp only [embed, partialInv_pairEmb, clearedCfg, List.mem_singleton, Cfg.withState,
      pairIdx_eq_iff] <;>
    by_cases h₀ : j = Fin.castAdd k i <;> by_cases h₁ : j = Fin.natAdd k i <;>
    simp [-Fin.natAdd_eq_addNat, h₀, h₁, (Fin.castAdd_ne_natAdd _ _).symm]

/-- The control states of `clearList` for a list of length `n`. -/
def ClearListState : ℕ → Type
  | 0 => Unit
  | n + 1 => ClearShadowedState ⊕ ClearListState n

instance instFiniteClearListState : (n : ℕ) → Finite (ClearListState n)
  | 0 => inferInstanceAs (Finite Unit)
  | n + 1 =>
    haveI := instFiniteClearListState n
    inferInstanceAs (Finite (ClearShadowedState ⊕ ClearListState n))

variable (m₀ m₁) in
/-- Clear the work tapes in `l` along their shadows, one after the other. -/
noncomputable def clearList :
    (l : List (Fin k)) → MultiTapeTM (k + k) Symbol (ClearListState l.length)
  | [] => nop (k + k) Symbol
  | i :: l => ((clearShadowed m₀ m₁).extendTapes (pairEmb i)).seq (clearList l)

omit [DecidableEq Symbol] in
/-- `nop` halts in one step from any configuration and changes nothing else. -/
theorem runFrom_nop_withState {k : ℕ} (C : Cfg k Symbol σ input) :
    (nop k Symbol).runFrom (C.withState (some ())) 1 = C.withState none := by
  rw [runFrom_one, step_of_state rfl]
  refine Cfg.ext (by simp [nop]) ?_ ?_ ?_ ?_
  · simp only [nop, tr_ofTr, Action.apply_inputPos, moveInputPos_zero, Cfg.withState]
  · funext j
    simp only [nop, tr_ofTr, Action.apply_workTapes, Cfg.withState]
  · funext j
    simp only [nop, tr_ofTr, Action.apply_workTapePos, SignType.coe_zero, add_zero, Cfg.withState]
  · simp only [nop, tr_ofTr, Action.apply_output, Option.toList_none, List.append_nil,
      Cfg.withState]

/-- **Clearing a list of work tapes** with their shadows, each ready to be cleared. -/
theorem runFrom_clearList (hm : m₀ ≠ m₁) (l : List (Fin k)) (hl : l.Nodup) (a b c : Fin k → ℕ)
    (V : Fin k → Finset ℤ) (C : Cfg (k + k) Symbol σ input)
    (hC : ∀ i ∈ l, PairReady m₀ m₁ C i (a i) (b i) (c i) (V i)) :
    (clearList m₀ m₁ l).runFrom (C.withState (some (clearList m₀ m₁ l).q₀))
        ((l.map fun i => a i + 2 * b i + c i + 5).sum + 1) = clearedCfg l C := by
  induction l generalizing C σ with
  | nil =>
    refine (runFrom_nop_withState C).trans (Cfg.ext rfl rfl ?_ ?_ rfl) <;> funext j <;>
      simp only [clearedCfg, List.not_mem_nil, ↓reduceIte, Cfg.withState]
  | cons i l ih =>
    obtain ⟨hil, hl⟩ := List.nodup_cons.1 hl
    have hmid := runFrom_clearShadowed_pairEmb hm (hC i List.mem_cons_self)
    have hrest := ih hl (clearedCfg (σ' := σ) [i] C) fun j hj => by
      have hji : j ≠ i := fun h => hil (h ▸ hj)
      obtain ⟨h₁, h₂, h₄, h₅, h₆⟩ := hC j (List.mem_cons_of_mem _ hj)
      exact ⟨by simp [-Fin.natAdd_eq_addNat, clearedCfg, hji, h₁],
        by simp [-Fin.natAdd_eq_addNat, pairIdx_natAdd, clearedCfg, hji, h₂], h₄,
        by simp [-Fin.natAdd_eq_addNat, pairIdx_natAdd, clearedCfg, hji, h₅],
        fun y hy => by simp [-Fin.natAdd_eq_addNat, clearedCfg, hji, h₆ y hy]⟩
    rw [List.map_cons, List.sum_cons, add_assoc]
    refine (runFrom_seq (tm₀ := (clearShadowed m₀ m₁).extendTapes (pairEmb i))
      (tm₁ := clearList m₀ m₁ l) (cfg := C.withState (some .start)) hmid rfl hrest rfl).trans ?_
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext j <;>
      simp only [Sequential.rightCfg, Cfg.mapState, clearedCfg, List.mem_cons] <;>
      by_cases hj : pairIdx j = i <;> by_cases hj' : pairIdx j ∈ l <;> simp [hj, hj']

/-! ### The tidy normal form -/

variable {State : Type*}

variable (m₀ m₁) in
/-- The tidy normal form of `tm`: run `tm` with shadowed work tapes, clear every work tape along
its shadow, and rewind the input head. The symbols `m₀` and `m₁` mark the shadows. -/
noncomputable def tidy (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + k) Symbol
      ((Option State ⊕ ClearListState (List.finRange k).length) ⊕ RewindState) :=
  ((shadow m₀ m₁ tm).seq (clearList m₀ m₁ (List.finRange k))).seq
    ((rewindInput Symbol).extendTapes (noTapes (k + k)))

variable {tm : MultiTapeTM k Symbol State}

omit [DecidableEq Symbol] in
/-- The configuration in which the clearing phase ends: halted, with blank work tapes and every
head on its start cell. -/
private theorem clearedCfg_finRange (C : Cfg (k + k) Symbol σ input) :
    clearedCfg (σ' := σ') (List.finRange k) C = ⟨none, C.inputPos, fun _ _ => none, fun _ => 0,
      C.output⟩ := by
  simp [clearedCfg]

/-- **The run of the tidy normal form.** If `tm` halts at step `u` having used `S` cells, then
`tidy m₀ m₁ tm` halts within `2 u + 3 S + 2 k + 4` steps, with blank work tapes, every head on its
start cell and the output of `tm`, having used at most `2 S + 2 k (3 S + 2 k + 3)` cells. -/
theorem HaltsAt.runFrom_tidy (hm : m₀ ≠ m₁) {u : ℕ} (h : tm.HaltsAt (tm.initCfg input) u) :
    ∃ T ≤ 2 * u + 3 * tm.spaceUsed (tm.initCfg input) u + 2 * k + 4,
      (tidy m₀ m₁ tm).runFrom ((tidy m₀ m₁ tm).initCfg input) T =
          wordsCfg input none (fun _ => []) (tm.runFrom (tm.initCfg input) u).output ∧
        (tidy m₀ m₁ tm).spaceUsed ((tidy m₀ m₁ tm).initCfg input) T ≤
          2 * tm.spaceUsed (tm.initCfg input) u +
            2 * k * (3 * tm.spaceUsed (tm.initCfg input) u + 2 * k + 3) := by
  set c₀ := tm.initCfg input
  set D := tm.runFrom c₀ u
  set S := tm.spaceUsed c₀ u
  set C₁ := Shadow.cfg m₀ m₁ D (Shadow.visited tm c₀ u)
  -- the visited cells of each tape form an interval `[L i, R i]` around the start cell
  choose L R hLR using fun i => exists_visitedByTapeHead_eq_Icc (tm := tm) c₀ u i
  have h0 : ∀ i, (0 : ℤ) ∈ Finset.Icc (L i) (R i) := fun i =>
    hLR i ▸ mem_visitedByTapeHead.2 ⟨0, by omega, rfl⟩
  have hp : ∀ i, D.workTapePos i ∈ Finset.Icc (L i) (R i) := fun i =>
    hLR i ▸ mem_visitedByTapeHead_self c₀ u i
  simp only [Finset.mem_Icc] at h0 hp
  set a : Fin k → ℕ := fun i => (-L i).toNat
  set b : Fin k → ℕ := fun i => (R i).toNat
  set c : Fin k → ℕ := fun i => (D.workTapePos i - L i).toNat
  have ha : ∀ i, (a i : ℤ) = -L i := fun i => Int.toNat_of_nonneg (by have := h0 i; omega)
  have hb : ∀ i, (b i : ℤ) = R i := fun i => Int.toNat_of_nonneg (h0 i).2
  have hc : ∀ i, (c i : ℤ) = D.workTapePos i - L i := fun i =>
    Int.toNat_of_nonneg (by have := hp i; omega)
  have hready : ∀ i ∈ List.finRange k,
      PairReady m₀ m₁ C₁ i (a i) (b i) (c i) (Shadow.visited tm c₀ u i) := fun i _ => by
    have hIcc : Finset.Icc (-(a i : ℤ)) (b i) = Finset.Icc (L i) (R i) := by rw [ha, hb, neg_neg]
    refine ⟨?_, ?_, ?_, ?_, fun y hy => ?_⟩
    · simp only [C₁, Shadow.cfg, Fin.append_left, ha, hc]
      ring
    · simp only [C₁, Shadow.cfg, Fin.append_right, ha, hc]
      ring
    · rw [hIcc, ← hLR, Shadow.visitedByTapeHead_eq_insert, ha, hc]
      congr 1
      ring
    · simp only [C₁, Shadow.cfg, Fin.append_right]
    · rw [hIcc, ← hLR] at hy
      simp only [C₁, Shadow.cfg, Fin.append_left]
      exact workTapes_runFrom_eq_of_notMem_visitedByTapeHead hy
  -- the three phases
  have hA : (shadow m₀ m₁ tm).runFrom ((shadow m₀ m₁ tm).initCfg input) (u + 1) = C₁ :=
    h.runFrom_shadow
  have hB := runFrom_clearList hm (List.finRange k) (List.nodup_finRange k) a b c
    (Shadow.visited tm c₀ u) C₁ hready
  rw [clearedCfg_finRange] at hB
  have hC₁ : C₁.Halted := by
    simp only [Cfg.Halted, C₁, Shadow.cfg, Option.map_eq_none_iff]
    exact h.halted
  have hAB := Turing.MultiTapeTM.runFrom_seq (tm₁ := clearList m₀ m₁ (List.finRange k)) hA hC₁
    hB rfl
  have hR : ((rewindInput Symbol).extendTapes (noTapes (k + k))).runFrom
      ((Sequential.rightCfg (State₀ := Option State)
        (⟨none, C₁.inputPos, fun _ _ => none, fun _ => 0, C₁.output⟩ :
          Cfg (k + k) Symbol (ClearListState (List.finRange k).length) input)).withState
        (some ((rewindInput Symbol).extendTapes (noTapes (k + k))).q₀))
      (C₁.inputPos.val - 1 + 2) =
      ⟨none, 1, fun _ _ => none, fun _ => 0, C₁.output⟩ := by
    rw [runFrom_noTapes]
    simp only [noTapesCfg, Cfg.withState, Sequential.rightCfg, Cfg.mapState, extendTapes_q₀,
      runFrom_rewindInput]
  have hTot := Turing.MultiTapeTM.runFrom_seq hAB rfl hR rfl
  have hinit : (tidy m₀ m₁ tm).initCfg input =
      Sequential.leftCfg ((rewindInput Symbol).extendTapes (noTapes (k + k)))
        (Sequential.leftCfg (clearList m₀ m₁ (List.finRange k))
          ((shadow m₀ m₁ tm).initCfg input)) := rfl
  -- the time bound
  set Tc := ((List.finRange k).map fun i => a i + 2 * b i + c i + 5).sum + 1
  have hcard : ∀ i, a i + b i + 1 = tm.spaceUsedByTape c₀ u i := fun i => by
    rw [spaceUsedByTape, hLR, Int.card_Icc]
    have := ha i
    have := hb i
    omega
  have hTc : Tc ≤ 3 * S + 2 * k + 1 := by
    have hsum : ((List.finRange k).map fun i => a i + 2 * b i + c i + 5).sum ≤
        ∑ i, (3 * tm.spaceUsedByTape c₀ u i + 2) := by
      rw [← Fin.sum_univ_def]
      refine Finset.sum_le_sum fun i _ => ?_
      have := hcard i
      have := hp i
      have := ha i
      have := hb i
      have := hc i
      omega
    have : ∑ i, (3 * tm.spaceUsedByTape c₀ u i + 2) = 3 * S + 2 * k := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [S, spaceUsed, mul_comm]
    omega
  have hTr : C₁.inputPos.val - 1 + 2 ≤ u + 2 := by
    have h₁ : (D.inputPos : ℕ) ≤ (c₀.inputPos : ℕ) + u := inputPos_runFrom_le tm c₀ u
    have h₂ : (c₀.inputPos : ℕ) = 1 := rfl
    change (D.inputPos : ℕ) - 1 + 2 ≤ u + 2
    omega
  refine ⟨u + 1 + Tc + (C₁.inputPos.val - 1 + 2), by omega, ?_, ?_⟩
  · rw [hinit]
    refine hTot.trans ?_
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i
    exact tapeOfList_nil.symm
  · rw [hinit]
    refine (Turing.MultiTapeTM.spaceUsed_seq_le hAB rfl (congrArg Cfg.state hR)).trans ?_
    refine (Nat.add_le_add (Turing.MultiTapeTM.spaceUsed_seq_le hA hC₁ (congrArg Cfg.state hB))
      (spaceUsed_noTapes_le _ _ _)).trans ?_
    rw [spaceUsed_shadow h]
    change 2 * S + _ + (k + k) ≤ _
    have h₁ := spaceUsed_linear (tm := clearList m₀ m₁ (List.finRange k))
      (C₁.withState (some (clearList m₀ m₁ (List.finRange k)).q₀)) Tc
    have h₂ : (k + k) * Tc ≤ 2 * k * (3 * S + 2 * k + 1) := by
      rw [← two_mul]
      exact Nat.mul_le_mul_left _ hTc
    have h₃ : 2 * k * (3 * S + 2 * k + 3) = 2 * k * (3 * S + 2 * k + 1) + 4 * k := by ring
    omega

/-- **The tidy normal form.** What `tm` computes within `t` steps and `s` cells,
`tidy m₀ m₁ tm` computes tidily within `2 t + 3 s + 2 k + 4` steps and `2 s + 2 k (3 s + 2 k + 3)`
cells, for any two distinct marks `m₀` and `m₁`. -/
theorem ComputesInTimeAndSpace.computesTidily_tidy (hm : m₀ ≠ m₁) {output : List Symbol}
    {t s : ℕ} (h : tm.ComputesInTimeAndSpace input output t s) :
    (tidy m₀ m₁ tm).ComputesTidilyInTimeAndSpace input output (2 * t + 3 * s + 2 * k + 4)
      (2 * s + 2 * k * (3 * s + 2 * k + 3)) := by
  obtain ⟨⟨u', hu', hout⟩, ht, hs⟩ := h
  obtain ⟨u, hut, hu⟩ := exists_haltsAt (halted_of_runsInTime ht)
  have hout' : (tm.runFrom (tm.initCfg input) u).output = output := by
    rw [← hout, hu.runFrom_eq (hu.le_of_halted hu')]
  have hS := spaceUsed_le_of_runsInSpace hs u
  obtain ⟨T, hT, hrun, hspace⟩ := hu.runFrom_tidy hm
  have hhalt : ((tidy m₀ m₁ tm).runFrom ((tidy m₀ m₁ tm).initCfg input) T).Halted := by
    rw [hrun]
    rfl
  have hTle : T ≤ 2 * t + 3 * s + 2 * k + 4 := by omega
  rw [computesTidily_iff, ← Cfg.init_eq_wordsCfg]
  refine ⟨by
    rw [show Cfg.init (tidy m₀ m₁ tm).q₀ input = (tidy m₀ m₁ tm).initCfg input from rfl,
      runFrom_eq_of_halt _ _ hTle hhalt, hrun, hout'], ?_⟩
  rw [show Cfg.init (tidy m₀ m₁ tm).q₀ input = (tidy m₀ m₁ tm).initCfg input from rfl,
    spaceUsed_eq_of_halt _ hTle hhalt]
  refine hspace.trans (Nat.add_le_add (Nat.mul_le_mul_left 2 hS) (Nat.mul_le_mul_left _ ?_))
  omega

/-- **Computable functions are tidily computable**, at a linear cost: a function computable within
time `t` and space `s` is computable tidily within time `2 t + 3 s + c` and space `c (s + 1)`, for a
constant `c` that depends on the number of work tapes of the machine. -/
theorem ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s) :
    ∃ c, ComputableTidilyInTimeAndSpace f encIn encOut (fun a => 2 * t a + 3 * s a + c)
      (fun a => c * (s a + 1)) := by
  obtain ⟨k, State, hfin, tm, htm⟩ := h
  refine ⟨4 * k * k + 6 * k + 4, k + k, _, inferInstance, tidy false true tm, fun a =>
    ((htm a).computesTidily_tidy Bool.false_ne_true).mono
      (by beta_reduce; generalize 4 * k * k = m; omega) ?_⟩
  beta_reduce
  have e₁ : 2 * s a + 2 * k * (3 * s a + 2 * k + 3) = (6 * k + 2) * s a + (4 * k * k + 6 * k) := by
    ring
  have e₂ : (4 * k * k + 6 * k + 4) * (s a + 1) =
      (4 * k * k + 6 * k + 4) * s a + (4 * k * k + 6 * k + 4) := by ring
  have : (6 * k + 2) * s a ≤ (4 * k * k + 6 * k + 4) * s a :=
    Nat.mul_le_mul_right _ (by generalize 4 * k * k = m; omega)
  rw [e₁, e₂]
  exact Nat.add_le_add this (by generalize 4 * k * k = m; omega)

end Turing.MultiTapeTM
