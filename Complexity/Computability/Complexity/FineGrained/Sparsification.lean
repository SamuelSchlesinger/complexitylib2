/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.Exponents
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Search
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.PolyTime
import Complexity.Logics.Propositional.ClauseSet.Sparsification
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# Algorithmic sparsification

The sparsification lemma of Impagliazzo, Paturi and Zane [ImpagliazzoPaturiZane2001] on the native
machines: a depth-first search of the sparsification tree, with a decider applied at its leaves,
runs within time `2 ^ (ε n)` times a polynomial, plus the time of the decider on formulas with at
most `c n + 1` clauses. Hence a decider for `k`-SAT within time `2 ^ (δ m)` times a polynomial,
on formulas with `m` clauses, gives one within time `2 ^ ((ε + c δ) n)` times a polynomial, on
formulas with `n` variables (`Cslib.Complexity.exists_decidableInExpTime_numVars_of_length`), and
the exponential time hypothesis says that 3SAT is not decidable in subexponential time in the
number of clauses (`Cslib.Complexity.ETH_iff_not_decidableInSubexpTime_length`).

The search (`Cslib.Complexity.Sparsify.search`) keeps a stack of formulas and an accumulator
(`Cslib.Complexity.Sparsify.step`). It starts from the normal form of the formula
(`Cslib.Logic.PL.CNF.Sparsification.normalize`); at a sparse formula on top of the stack it runs
the decider, and at any other formula it pushes the two children of the list-level step
(`Cslib.Logic.PL.CNF.Sparsification.next`), which is polynomial-time. This is the depth-first
search of the branching tree of the list-level rule
(`Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule.exists_iterate_searchStep`), so it visits
every leaf within twice the number of leaves of steps, at most `2 ^ (ε n)` up to a constant
(`Cslib.Logic.PL.ClauseSet.Sparsification.exists_sum_choose_le`); the stack holds at most
`O(n)` formulas of the tree, each with `O(n + m)` clauses; and the leaves, being sparse, have at
most `c n + 1` clauses (`Cslib.Logic.PL.ClauseSet.Sparsification.card_le_of_sparse`). The search
runs a fixed number `2 ^ (n / M + 2)` of rounds, the last ones on the empty stack.

## Main definitions

* `Cslib.Complexity.Sparsify.step`, `Cslib.Complexity.Sparsify.search`: the search.

## Main results

* `Cslib.Complexity.Sparsify.search_eq_true_iff`: the search decides satisfiability.
* `Cslib.Complexity.exists_decidableInExpTime_numVars_of_length`: from clauses to variables.
* `Cslib.Complexity.DecidableInSubexpTime.numVars_of_length`: subexponential time in the number of
  clauses gives subexponential time in the number of variables.
* `Cslib.Complexity.ETH_iff_not_decidableInSubexpTime_length`: the exponential time hypothesis in
  terms of clauses.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [C. Calabro, R. Impagliazzo, R. Paturi, *A duality between clause width and clause density for
  SAT*][CalabroImpagliazzoPaturi2006]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification Turing.MultiTapeTM
open scoped List

namespace Sparsify

open ClauseSet.Sparsification (threshold base one_le_threshold BranchingRule)

/-! ### The search -/

/-- The states of the search: a stack of formulas and an accumulator. -/
abbrev State : Type := List (CNF ℕ) × Bool

/-- States encoded as framed tuples. -/
abbrev encState : State ↪ List Bool := encPair (encList encCNF) encBool

/-- One step of the depth-first search of the sparsification tree, for width `K` and the
thresholds `threshold K α`: a sparse formula on top of the stack is popped and the decider `g` is
run on it; any other formula on top is replaced by its two children. -/
def step (K α : ℕ) (g : CNF ℕ → Bool) (s : State) : State :=
  if s.1.isEmpty then s
  else if isSparse (threshold K α) K (s.1.headD []) then (s.1.tail, s.2 || g (s.1.headD []))
  else (next (threshold K α) K (s.1.headD []) false ::
    next (threshold K α) K (s.1.headD []) true :: s.1.tail, s.2)

/-- The root of the search: the normal form of a formula of width `k`, and the formula without
clauses otherwise. -/
def root (k : ℕ) (φ : CNF ℕ) : CNF ℕ :=
  if φ.all fun c => decide (c.length ≤ k) then normalize φ else []

/-- The number of rounds of the search, `2 ^ (n / M + 2)` on formulas with `n` variables. -/
def rounds (M : ℕ) (φ : CNF ℕ) : ℕ := 2 ^ ((ThreeSAT.distinctVars φ).length / M + 2)

/-- **The sparsification search**: run the search for the given number of rounds from the root,
and report the accumulator. -/
def search (K α k M : ℕ) (g : CNF ℕ → Bool) (φ : CNF ℕ) : Bool :=
  ((step K α g)^[rounds M φ] ([root k φ], false)).2

/-! ### The search is the depth-first search of the tree -/

variable {K α : ℕ} (hK : 1 ≤ K) (hα : 1 ≤ α)

/-- The list-level branching rule for width `K` and the thresholds `threshold K α`. -/
abbrev rule : BranchingRule (threshold K α) ℕ {ψ : CNF ℕ // Good K ψ} :=
  CNF.Sparsification.rule (one_le_threshold hK hα) K

include hK hα in
theorem step_map (g : CNF ℕ → Bool) (stk : List {ψ : CNF ℕ // Good K ψ}) (acc : Bool) :
    step K α g (stk.map Subtype.val, acc) =
      Prod.map (List.map Subtype.val) id
        ((rule hK hα).searchStep (g ∘ Subtype.val) (stk, acc)) := by
  cases stk with
  | nil => rfl
  | cons s rest =>
    have hiff := isSparse_eq_true_iff (one_le_threshold hK hα) s.2
    by_cases hs : ClauseSet.Sparsification.Sparse (threshold K α) s.1.toClauseSet
    · have hs' : isSparse (threshold K α) K s.1 = true := hiff.mpr hs
      simp [step, BranchingRule.searchStep, hs, hs', CNF.Sparsification.rule]
    · have hs' : isSparse (threshold K α) K s.1 = false := by
        simpa using fun h => hs (hiff.mp h)
      simp [step, BranchingRule.searchStep, hs, hs', rule, CNF.Sparsification.rule]

include hK hα in
theorem iterate_step_map (g : CNF ℕ → Bool) (n : ℕ) (stk : List {ψ : CNF ℕ // Good K ψ})
    (acc : Bool) :
    (step K α g)^[n] (stk.map Subtype.val, acc) =
      Prod.map (List.map Subtype.val) id
        (((rule hK hα).searchStep (g ∘ Subtype.val))^[n] (stk, acc)) := by
  induction n generalizing stk acc with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, step_map hK hα]
    obtain ⟨stk', acc'⟩ := (rule hK hα).searchStep (g ∘ Subtype.val) (stk, acc)
    exact ih stk' acc'

theorem step_nil (g : CNF ℕ → Bool) (acc : Bool) : step K α g ([], acc) = ([], acc) := rfl

theorem iterate_step_nil (g : CNF ℕ → Bool) (n : ℕ) (acc : Bool) :
    (step K α g)^[n] ([], acc) = ([], acc) :=
  Function.iterate_fixed (step_nil g acc) n

/-! ### The root -/

theorem good_root {k : ℕ} (hkK : k ≤ K) (φ : CNF ℕ) : Good K (root k φ) := by
  unfold root
  split_ifs with h
  · simp only [List.all_eq_true, decide_eq_true_eq] at h
    exact good_normalize fun C hC => (h C hC).trans hkK
  · exact ⟨by simp, by simp, by simp, by simp [CNF.toClauseSet, ClauseSet.Sparsification.Reduced]⟩

/-- Every clause of the root has the literals of a clause of the formula. -/
theorem exists_of_mem_root {k : ℕ} {φ : CNF ℕ} {C : Clause ℕ} (hC : C ∈ root k φ) :
    ∃ D ∈ φ, C.toFinset = D.toFinset := by
  unfold root at hC
  split_ifs at hC
  · have hsub : normalize φ <+ φ.map dedup :=
      (reduce_sublist _).trans (dedupClauses_sublist _)
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp (hsub.subset hC)
    exact ⟨D, hD, toFinset_dedup D⟩
  · simp at hC

theorem length_root_le (k : ℕ) (φ : CNF ℕ) : (root k φ).length ≤ φ.length := by
  unfold root
  split_ifs
  · exact ((reduce_sublist _).trans (dedupClauses_sublist _)).length_le.trans
      (List.length_map _).le
  · exact Nat.zero_le _

/-- The root as a state of the list-level rule. -/
def rootState {k : ℕ} (hkK : k ≤ K) (φ : CNF ℕ) : {ψ : CNF ℕ // Good K ψ} :=
  ⟨root k φ, good_root hkK φ⟩

theorem mem_vars_of_mem_root {k : ℕ} {φ : CNF ℕ} :
    ∀ C ∈ (root k φ).toClauseSet, ∀ l ∈ C, l.1 ∈ φ.vars.toFinset := by
  intro C hC l hl
  obtain ⟨C', hC', rfl⟩ := mem_toClauseSet.mp hC
  obtain ⟨D, hD, hDeq⟩ := exists_of_mem_root hC'
  rw [hDeq, List.mem_toFinset] at hl
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨D, hD, hl⟩, rfl⟩)

/-! ### The states of the tree -/

section Tree

variable {k : ℕ} (hkK : k ≤ K) {φ : CNF ℕ} {w : List Bool}
include hK hα hkK

/-- Every clause of a state of the tree has its literals in a clause of the formula. -/
theorem exists_of_mem_walk (hw : (rule hK hα).IsNodeWord (rootState hkK φ) w) {C : Clause ℕ}
    (hC : C ∈ ((rule hK hα).walk (rootState hkK φ) w).1) :
    ∃ D ∈ φ, C.toFinset ⊆ D.toFinset := by
  obtain ⟨D', hD', hCD'⟩ := BranchingRule.IsNodeWord.refines_walk (one_le_threshold hK hα) hw
    C.toFinset (mem_toClauseSet.mpr ⟨C, hC, rfl⟩)
  obtain ⟨D'', hD'', rfl⟩ := mem_toClauseSet.mp hD'
  obtain ⟨D, hD, hDeq⟩ := exists_of_mem_root hD''
  exact ⟨D, hD, hDeq ▸ hCD'⟩

/-- The states of the tree have at most `m + n K X ^ (2 K)` clauses. -/
theorem length_walk_le (hw : (rule hK hα).IsNodeWord (rootState hkK φ) w) :
    ((rule hK hα).walk (rootState hkK φ) w).1.length ≤
      φ.length + φ.numVars * (K * base K α ^ (2 * K)) := by
  have h : (((rule hK hα).walk (rootState hkK φ) w).1.toClauseSet).card ≤
      (rootState hkK φ).1.toClauseSet.card + φ.vars.toFinset.card * (K * base K α ^ (2 * K)) :=
    BranchingRule.IsNodeWord.card_walk_le hK hα (rootState hkK φ).2.reduced
      (rootState hkK φ).2.card_le φ.vars.toFinset mem_vars_of_mem_root hw
  rw [Good.card_toClauseSet ((rule hK hα).walk (rootState hkK φ) w).2] at h
  refine h.trans (Nat.add_le_add_right ?_ _)
  rw [Good.card_toClauseSet (rootState hkK φ).2]
  exact length_root_le k φ

/-- **The leaves are small.** The sparse states of the tree have at most `c n + 1` clauses, for
`c = 2 ∑_{j < K} θ j`. -/
theorem length_walk_le_of_isSparse (hw : (rule hK hα).IsNodeWord (rootState hkK φ) w)
    (hs : isSparse (threshold K α) K ((rule hK hα).walk (rootState hkK φ) w).1 = true) :
    ((rule hK hα).walk (rootState hkK φ) w).1.length ≤
      2 * (∑ j ∈ Finset.range K, threshold K α j) * φ.numVars + 1 := by
  set ψ := (rule hK hα).walk (rootState hkK φ) w
  have hsparse := (isSparse_eq_true_iff (one_le_threshold hK hα) ψ.2).mp hs
  rw [← Good.card_toClauseSet ψ.2]
  refine ClauseSet.Sparsification.card_le_of_sparse (one_le_threshold hK hα) hsparse ψ.2.card_le
    φ.vars.toFinset fun C' hC' l hl => ?_
  obtain ⟨C, hC, rfl⟩ := mem_toClauseSet.mp hC'
  obtain ⟨D, hD, hCD⟩ := exists_of_mem_walk hK hα hkK hw hC
  have hl' := List.mem_toFinset.mp (hCD hl)
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨D, hD, hl'⟩, rfl⟩)

/-- The states of the tree from a formula of width `k` have width `k`. -/
theorem length_le_of_mem_walk (hφ : ∀ c ∈ φ, c.length ≤ k)
    (hw : (rule hK hα).IsNodeWord (rootState hkK φ) w) {C : Clause ℕ}
    (hC : C ∈ ((rule hK hα).walk (rootState hkK φ) w).1) : C.length ≤ k := by
  obtain ⟨D, hD, hCD⟩ := exists_of_mem_walk hK hα hkK hw hC
  rw [← List.toFinset_card_of_nodup (((rule hK hα).walk (rootState hkK φ) w).2.nodup C hC)]
  exact (Finset.card_le_card hCD).trans ((List.toFinset_card_le D).trans (hφ D hD))

end Tree

/-! ### The run of the search -/

/-- The number of leaves is within the number of rounds: the bound on the binomial tail that
`Cslib.Logic.PL.ClauseSet.Sparsification.exists_sum_choose_le` provides for `ε = 1 / M`. -/
def LeafBound (K α M : ℕ) : Prop :=
  ∀ N : ℕ, ∑ j ∈ Finset.range ((K - 1) * N / α + 1),
    (N * (K * base K α ^ (2 * K))).choose j ≤ 2 ^ (N / M + 1)

open Classical in
/-- **The run of the search.** After the rounds, the stack is empty and the accumulator records
whether the decider accepts a leaf of the tree. Meanwhile the stack holds at most
`n K X ^ (2 K) + 1` states of the tree. -/
theorem iterate_step {k M : ℕ} (hkK : k ≤ K) (hM : LeafBound K α M) (g : CNF ℕ → Bool)
    (φ : CNF ℕ) :
    (step K α g)^[rounds M φ] ([root k φ], false) =
      ([], decide (∃ w, (rule hK hα).IsLeafWord (rootState hkK φ) w ∧
        g ((rule hK hα).walk (rootState hkK φ) w).1 = true)) ∧
    ∀ i, ∃ (stk : List {ψ : CNF ℕ // Good K ψ}) (acc : Bool),
      (step K α g)^[i] ([root k φ], false) = (stk.map Subtype.val, acc) ∧
      stk.length ≤ φ.numVars * (K * base K α ^ (2 * K)) + 1 ∧
      ∀ t ∈ stk, ∃ w, (rule hK hα).IsNodeWord (rootState hkK φ) w ∧
        (rule hK hα).walk (rootState hkK φ) w = t := by
  set R := rule hK hα
  set s₀ := rootState hkK φ
  have hred := s₀.2.reduced
  have hk0 := s₀.2.card_le
  have hlen : ∀ w, R.IsLeafWord s₀ w → w.length ≤ φ.numVars * (K * base K α ^ (2 * K)) :=
    fun w hw => hw.length_le hK hα hred hk0 φ.vars.toFinset mem_vars_of_mem_root
  obtain ⟨W, hW, N, hN, h⟩ := BranchingRule.exists_iterate_searchStep (R := R)
    (one_le_threshold hK hα) (g ∘ Subtype.val) s₀ hlen
  have hWcard : W.card ≤ 2 ^ (φ.numVars / M + 1) :=
    (BranchingRule.card_le_of_isLeafWord hK hα hred hk0 φ.vars.toFinset mem_vars_of_mem_root W
      hW).trans (hM φ.numVars)
  have hNr : N ≤ rounds M φ := by
    rw [rounds, ThreeSAT.length_distinctVars, pow_succ]
    omega
  have hinit : ([root k φ], false) = ([s₀].map Subtype.val, false) := rfl
  obtain ⟨hfin, hmid⟩ := h [] false
  have hN' : (step K α g)^[N] ([root k φ], false) = ([], decide (∃ w, R.IsLeafWord s₀ w ∧
      g (R.walk s₀ w).1 = true)) := by
    rw [hinit, iterate_step_map hK hα, hfin]
    simp
  refine ⟨?_, fun i => ?_⟩
  · rw [show rounds M φ = (rounds M φ - N) + N by omega, Function.iterate_add_apply, hN',
      iterate_step_nil]
  · by_cases hi : i ≤ N
    · obtain ⟨stk, acc', heq, hstk, hmem⟩ := hmid i hi
      refine ⟨stk, acc', ?_, hstk, hmem⟩
      rw [hinit, iterate_step_map hK hα, heq]
      simp
    · refine ⟨[], decide (∃ w, R.IsLeafWord s₀ w ∧ g (R.walk s₀ w).1 = true), ?_, by simp,
        by simp⟩
      rw [show i = (i - N) + N by omega, Function.iterate_add_apply, hN', iterate_step_nil]
      rfl

include hK hα in
/-- **The search decides satisfiability.** If the decider decides satisfiability on formulas of
width `k`, the search decides satisfiability on formulas of width `k`. -/
theorem search_eq_true_iff {k M : ℕ} (hkK : k ≤ K) (hM : LeafBound K α M) {g : CNF ℕ → Bool}
    (hg : ∀ ψ : CNF ℕ, (∀ c ∈ ψ, c.length ≤ k) → (g ψ = true ↔ ψ.Satisfiable)) {φ : CNF ℕ}
    (hφ : ∀ c ∈ φ, c.length ≤ k) : search K α k M g φ = true ↔ φ.Satisfiable := by
  classical
  set R := rule hK hα
  set s₀ := rootState hkK φ
  rw [search, (iterate_step hK hα hkK hM g φ).1, decide_eq_true_iff]
  have hroot : (root k φ) = normalize φ := by
    rw [root, ite_eq_left (List.all_eq_true.mpr fun c hc => decide_eq_true (hφ c hc))]
  constructor
  · rintro ⟨w, hw, hgw⟩
    obtain ⟨x, hx⟩ := (hg _ fun c hc => length_le_of_mem_walk hK hα hkK hφ hw.isNodeWord hc).mp
      hgw
    refine ⟨x, ?_⟩
    have hsat : (R.toClauseSet (R.walk s₀ w)).Sat x := (CNF.sat_toClauseSet_iff _ x).mpr hx
    have := (BranchingRule.exists_isLeafWord_sat_iff (one_le_threshold hK hα) s₀ x).mp
      ⟨w, hw, hsat⟩
    change (root k φ).toClauseSet.Sat x at this
    rwa [hroot, sat_toClauseSet_normalize_iff] at this
  · rintro ⟨x, hx⟩
    have hsat : (R.toClauseSet s₀).Sat x := by
      change (root k φ).toClauseSet.Sat x
      rwa [hroot, sat_toClauseSet_normalize_iff]
    obtain ⟨w, hw, hwx⟩ :=
      (BranchingRule.exists_isLeafWord_sat_iff (one_le_threshold hK hα) s₀ x).mpr hsat
    refine ⟨w, hw, (hg _ fun c hc => length_le_of_mem_walk hK hα hkK hφ hw.isNodeWord hc).mpr
      ⟨x, (CNF.sat_toClauseSet_iff _ x).mp hwx⟩⟩

end Sparsify

end Cslib.Complexity
