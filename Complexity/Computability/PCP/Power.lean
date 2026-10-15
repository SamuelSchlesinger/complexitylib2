/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.RegularConstraintGraph
public import Complexity.Foundations.Combinatorics.Expander.KilledWalk

/-!
# Powering a constraint graph

The **powering** step of Dinur's proof of the PCP theorem [Dinur, Section 3.2][Dinur2007] trades a
larger alphabet for a larger value: on an expander, it multiplies the value of a regular constraint
graph by a factor that grows with the length of the walks it uses (see also
[Arora and Barak, Chapter 22][AroraBarak09]). This file builds the powered constraint graph along
**killed walks**, the variant of Radhakrishnan [Radhakrishnan2006] [Dinur, Section 9][Dinur2007]:
the length of a walk is random, killed before each step with probability `1 / q` and stopped after
`T` steps (`Cslib.RotationMap.killedPow`).

Given a regular constraint graph `R` over the alphabet `α` on a `D`-regular multigraph `G`, the
powered constraint graph `R.power T q`

* has the same vertices as `R`;
* has an edge for every killed walk: its darts at `v` are the walks `k : Fin T → D` from `v` with
  kill signals `c : Fin T → Fin q`, followed up to their kill time `ℓ = killTime c`, so that it is
  `|D| ^ T q ^ T`-regular;
* labels every vertex `v` with an **opinion** `WalkLabels D T → α`: a label for the end of every
  walk of length at most `T` from `v`, that is, for every vertex within distance `T` of `v`;
* checks, on a killed walk from `v` to `w` of length `ℓ`, every step `i < ℓ`: the constraint of `R`
  on the dart crossed at step `i` must hold between the opinion of `v` about the vertex reached
  after the first `i` steps and the opinion of `w` about the same vertex after the remaining
  `ℓ - (i + 1)` steps, read along the reverse walk.

The alphabet `WalkLabels D T → α` has `|α| ^ (∑ ℓ ≤ T, |D| ^ ℓ)` letters (`card_alphabet_power`),
which depends on `T`, `|D|` and `|α|` only. Walks of every length up to `T` are indexed, rather than
the walks of a fixed length, so that the opinions read by a killed walk are always about walks of
exactly the lengths that the killed walk provides.

A labelling `σ` of the vertices of `R` induces the **truthful opinions** `R.truthful T σ`, which
label the end of every walk by its label under `σ`. Between truthful opinions, the check at step `i`
of a killed walk is the constraint of `R` on the dart crossed there (`rel_truthful_iff`), so the
truthful opinions of a satisfying labelling satisfy the powered graph (`satisfiable_power`). In the
other direction, a killed walk whose ends hold the truthful opinions of `σ` at the indices read at a
step whose dart `σ` violates is itself violated (`not_satisfies_of_hit`): this is where the
soundness analysis of `Cslib.PCP.RegularConstraintGraph.le_unsatVal_power` starts.

## Main definitions

* `Cslib.PCP.WalkLabels`: the walks of length at most `T`, indexing the opinions.
* `Cslib.PCP.RegularConstraintGraph.power`: the powered constraint graph.
* `Cslib.PCP.RegularConstraintGraph.truthful`: the truthful opinions of a labelling.
* `Cslib.PCP.RegularConstraintGraph.Hit`: a killed walk is hit at a step when the dart crossed
  there is violated and both ends hold the truthful opinions at the indices read at that step.

## Main results

* `Cslib.RotationMap.neighbor_pow_take_rot_killedPow`: the reverse of a killed walk retraces it.
* `Cslib.PCP.RegularConstraintGraph.rel_truthful_iff`: between truthful opinions, the check at a
  step is the constraint on the dart crossed there.
* `Cslib.PCP.RegularConstraintGraph.satisfiable_power`,
  `Cslib.PCP.RegularConstraintGraph.satisfiable_power_iff`: completeness, and powering preserves
  satisfiability.
* `Cslib.PCP.RegularConstraintGraph.not_satisfies_of_hit`: a killed walk hit at some step is
  violated.
* `Cslib.PCP.RegularConstraintGraph.card_label_power`,
  `Cslib.PCP.RegularConstraintGraph.card_alphabet_power`: the degree and the alphabet size.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [J. Radhakrishnan, *Gap amplification in PCPs using lazy random walks*][Radhakrishnan2006]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib

open Finset

namespace RotationMap

variable {V D : Type*} (G : RotationMap V D) {T q : ℕ} [NeZero q]

/-- **The reverse of a killed walk retraces it**: its first `m` steps, for `m` at most the kill
time `ℓ`, lead to the vertex reached after `ℓ - m` steps of the original walk. -/
theorem neighbor_pow_take_rot_killedPow (p : V × (Fin T → D) × (Fin T → Fin q)) {m : ℕ}
    (hm : m ≤ killTime p.2.2) :
    (G.pow m).neighbor ((G.killedPow T q).rot p).1
        (Fin.take m (hm.trans (killTime_le _)) ((G.killedPow T q).rot p).2.1) =
      G.walkAt (p.1, p.2.1) (killTime p.2.2 - m) := by
  calc (G.pow m).neighbor ((G.killedPow T q).rot p).1
        (Fin.take m (hm.trans (killTime_le _)) ((G.killedPow T q).rot p).2.1)
      = G.walkAt (((G.killedPow T q).rot p).1,
          Fin.take _ (killTime_le p.2.2) ((G.killedPow T q).rot p).2.1) m :=
        (G.walkAt_eq_neighbor_pow (((G.killedPow T q).rot p).1,
          Fin.take _ (killTime_le p.2.2) ((G.killedPow T q).rot p).2.1) hm).symm
    _ = G.walkAt ((G.pow (killTime p.2.2)).rot (p.1, Fin.take _ (killTime_le p.2.2) p.2.1)) m := by
        rw [G.rot_pow_killTime]
    _ = G.walkAt (p.1, p.2.1) (killTime p.2.2 - m) := by
        rw [G.walkAt_rot_pow _ hm, G.walkAt_take (p.1, p.2.1) (killTime_le _) (Nat.sub_le _ _)]

end RotationMap

namespace PCP

/-- The walks of length at most `T` with labels in `D`: a length `ℓ ≤ T` and the labels of the `ℓ`
steps. In the powered constraint graph, a vertex holds an opinion about the end of every walk from
it, so its opinions are indexed by `WalkLabels D T`. -/
abbrev WalkLabels (D : Type*) (T : ℕ) : Type _ :=
  Σ ℓ : Fin (T + 1), Fin ℓ → D

namespace WalkLabels

variable {D : Type*} {T : ℕ}

/-- The walk of length `m ≤ T` along the labels `r`. -/
def mk {m : ℕ} (hm : m ≤ T) (r : Fin m → D) : WalkLabels D T :=
  ⟨⟨m, Nat.lt_succ_of_le hm⟩, r⟩

/-- The walk along the first `m ≤ T` labels of `k`. -/
def take (m : ℕ) (hm : m ≤ T) (k : Fin T → D) : WalkLabels D T :=
  mk hm (Fin.take m hm k)

/-- The walk along the first `m` labels of `k` does not depend on how `m` is written. -/
theorem take_congr {m m' : ℕ} (h : m = m') (hm : m ≤ T) (hm' : m' ≤ T) (k : Fin T → D) :
    take m hm k = take m' hm' k := by
  subst h
  rfl

/-- There are `∑ ℓ ≤ T, |D| ^ ℓ` walks of length at most `T` from a vertex. -/
theorem card_eq [Fintype D] :
    Fintype.card (WalkLabels D T) = ∑ ℓ ∈ range (T + 1), Fintype.card D ^ ℓ := by
  rw [Fintype.card_sigma, ← Fin.sum_univ_eq_sum_range]
  simp

end WalkLabels

namespace RegularConstraintGraph

open RotationMap

variable {V D α : Type*} (R : RegularConstraintGraph V D α) (T q : ℕ) [NeZero q]

/-- **The powered constraint graph** [Dinur, Section 3.2][Dinur2007], along killed walks
[Radhakrishnan2006] [Dinur, Section 9][Dinur2007]. Its vertices are those of `R`, its darts at `v`
are the killed walks from `v`, the darts of the killed power `R.graph.killedPow T q`, and the label
of a vertex is its opinion about the end of every walk of length at most `T` from it. The
constraint on a killed walk `p` from `v` to `w`, killed at step `ℓ`, holds when at every step
`i < ℓ` the constraint of `R` on the dart crossed there holds between the opinion of `v` about the
vertex reached after the first `i` steps of `p` and the opinion of `w` about the vertex reached
after the first `ℓ - (i + 1)` steps of the reverse of `p`, which is the same vertex. -/
def power : RegularConstraintGraph V ((Fin T → D) × (Fin T → Fin q)) (WalkLabels D T → α) where
  graph := R.graph.killedPow T q
  rel p a b := ∀ (i : ℕ) (hi : i < killTime p.2.2),
    R.rel (R.graph.walkDart (p.1, p.2.1) ⟨i, hi.trans_le (killTime_le _)⟩)
      (a (.take i (hi.le.trans (killTime_le _)) p.2.1))
      (b (.take (killTime p.2.2 - (i + 1)) ((Nat.sub_le _ _).trans (killTime_le _))
        ((R.graph.killedPow T q).rot p).2.1))

/-- The underlying multigraph of the powered constraint graph is the killed power. -/
@[simp]
theorem graph_power : (R.power T q).graph = R.graph.killedPow T q :=
  rfl

variable {R T q} in
/-- A labelling of the powered constraint graph satisfies the killed walk `p` when, at every step
before it is killed, the opinions of its two ends satisfy the constraint of `R` on the dart crossed
there. -/
theorem satisfies_power_iff {A : V → WalkLabels D T → α} {p : V × (Fin T → D) × (Fin T → Fin q)} :
    (R.power T q).toConstraintGraph.Satisfies A p ↔
      ∀ (i : ℕ) (hi : i < killTime p.2.2),
        R.rel (R.graph.walkDart (p.1, p.2.1) ⟨i, hi.trans_le (killTime_le _)⟩)
          (A p.1 (.take i (hi.le.trans (killTime_le _)) p.2.1))
          (A ((R.graph.killedPow T q).rot p).1
            (.take (killTime p.2.2 - (i + 1)) ((Nat.sub_le _ _).trans (killTime_le _))
              ((R.graph.killedPow T q).rot p).2.1)) :=
  Iff.rfl

/-! ### Completeness -/

/-- The **truthful opinions** of a labelling `σ` of the vertices: the opinion of `v` about the end
of a walk from `v` is the label `σ` gives to that end. -/
def truthful (σ : V → α) (v : V) (w : WalkLabels D T) : α :=
  σ ((R.graph.pow w.1).neighbor v w.2)

/-- The truthful opinion of `v` about the walk along the first `m` labels of `k` is the label of the
vertex reached after `m` steps of the walk from `v` along `k`. -/
theorem truthful_take (σ : V → α) (v : V) {m : ℕ} (hm : m ≤ T) (k : Fin T → D) :
    R.truthful T σ v (.take m hm k) = σ (R.graph.walkAt (v, k) m) := by
  rw [R.graph.walkAt_eq_neighbor_pow (v, k) hm]
  rfl

/-- The truthful opinion of the end of a killed walk, about the walk along the first `m` labels of
the reverse walk for `m` at most the kill time `ℓ`, is the label of the vertex reached after
`ℓ - m` steps of the killed walk. -/
theorem truthful_take_rot_killedPow (σ : V → α) (p : V × (Fin T → D) × (Fin T → Fin q)) {m : ℕ}
    (hm : m ≤ killTime p.2.2) :
    R.truthful T σ ((R.graph.killedPow T q).rot p).1
        (.take m (hm.trans (killTime_le _)) ((R.graph.killedPow T q).rot p).2.1) =
      σ (R.graph.walkAt (p.1, p.2.1) (killTime p.2.2 - m)) :=
  congrArg σ (R.graph.neighbor_pow_take_rot_killedPow p hm)

/-- **Between truthful opinions**, the check of the powered constraint graph at a step `i` of a
killed walk, before it is killed, is the constraint of `R` on the dart crossed at step `i`. -/
theorem rel_truthful_iff (σ : V → α) (p : V × (Fin T → D) × (Fin T → Fin q)) {i : ℕ}
    (hi : i < killTime p.2.2) :
    R.rel (R.graph.walkDart (p.1, p.2.1) ⟨i, hi.trans_le (killTime_le _)⟩)
        (R.truthful T σ p.1 (.take i (hi.le.trans (killTime_le _)) p.2.1))
        (R.truthful T σ ((R.graph.killedPow T q).rot p).1
          (.take (killTime p.2.2 - (i + 1)) ((Nat.sub_le _ _).trans (killTime_le _))
            ((R.graph.killedPow T q).rot p).2.1)) ↔
      R.toConstraintGraph.Satisfies σ
        (R.graph.walkDart (p.1, p.2.1) ⟨i, hi.trans_le (killTime_le _)⟩) := by
  rw [truthful_take, R.truthful_take_rot_killedPow T q σ p (Nat.sub_le _ _),
    Nat.sub_sub_self (Nat.succ_le_of_lt hi), satisfies_toConstraintGraph_iff, neighbor_def,
    fst_rot_walkDart]
  rfl

variable {R T q} in
/-- The truthful opinions of a labelling satisfying `R` satisfy the powered constraint graph. -/
theorem satisfies_power_truthful {σ : V → α} (hσ : ∀ d, R.toConstraintGraph.Satisfies σ d)
    (p : V × (Fin T → D) × (Fin T → Fin q)) :
    (R.power T q).toConstraintGraph.Satisfies (R.truthful T σ) p :=
  satisfies_power_iff.2 fun _ hi ↦ (R.rel_truthful_iff T q σ p hi).2 (hσ _)

variable {R} in
/-- **Completeness of powering** [Dinur, Section 3.2][Dinur2007]: if `R` is satisfiable, so is the
powered constraint graph. -/
theorem satisfiable_power (h : R.toConstraintGraph.Satisfiable) :
    (R.power T q).toConstraintGraph.Satisfiable :=
  let ⟨_, hσ⟩ := h
  ⟨_, satisfies_power_truthful hσ⟩

/-- **Powering preserves satisfiability**: for `T ≥ 1` and `q ≥ 2`, the powered constraint graph is
satisfiable exactly when `R` is. If `A` satisfies the powered constraint graph, the opinions of the
vertices about themselves satisfy `R`: the killed walk killed after one step, along a dart,
checks the constraint of `R` on that dart between them. -/
theorem satisfiable_power_iff (hT : 1 ≤ T) (hq : 2 ≤ q) :
    (R.power T q).toConstraintGraph.Satisfiable ↔ R.toConstraintGraph.Satisfiable := by
  refine ⟨fun ⟨A, hA⟩ ↦ ⟨fun v ↦ A v (.mk (Nat.zero_le T) Fin.elim0), fun d ↦ ?_⟩,
    satisfiable_power T q⟩
  -- the kill signals that kill a walk after its first step
  set c : Fin T → Fin q := fun j ↦ if (j : ℕ) = 0 then ⟨1, by omega⟩ else 0
  have hc : killTime c = 1 := by
    refine le_antisymm (Nat.find_min' _ fun h ↦ ?_) ((lt_killTime_iff c hT).2 fun j hj ↦ ?_)
    · simp [c]
    · simp [c, Nat.le_zero.1 hj, Fin.ext_iff]
  set k : Fin T → D := fun _ ↦ d.2
  have h := satisfies_power_iff.1 (hA (d.1, k, c)) 0 (by rw [hc]; exact one_pos)
  dsimp only at h
  -- the killed walk ends at the far end of `d`, and both opinions are about the walk of length `0`
  have h₁ : ((R.graph.killedPow T q).rot (d.1, k, c)).1 = R.graph.neighbor d.1 d.2 := by
    rw [← neighbor_def, neighbor_killedPow, hc, R.graph.walkAt_succ_of_lt _ hT]
    rfl
  have h₀ (k' : Fin T → D) :
      WalkLabels.take 0 (Nat.zero_le T) k' = .mk (Nat.zero_le T) Fin.elim0 :=
    congrArg (WalkLabels.mk _) (Subsingleton.elim _ _)
  rw [WalkLabels.take_congr (m := killTime c - (0 + 1)) (m' := 0) (by rw [hc]) _ (Nat.zero_le T),
    h₀, h₀, h₁] at h
  exact h

/-! ### The soundness witness -/

/-- The killed walk `p` is **hit** at its step `i` [Dinur, Definition 5.1][Dinur2007] by a
labelling `A` of the powered constraint graph, relative to a labelling `σ` of `R`, when the step
comes before `p` is killed, `σ` violates the dart crossed there, and both ends of `p` hold the
truthful opinions of `σ` at the indices read at that step. -/
def Hit (A : V → WalkLabels D T → α) (σ : V → α) (p : V × (Fin T → D) × (Fin T → Fin q))
    (i : ℕ) : Prop :=
  ∃ hi : i < killTime p.2.2,
    ¬ R.toConstraintGraph.Satisfies σ
        (R.graph.walkDart (p.1, p.2.1) ⟨i, hi.trans_le (killTime_le _)⟩) ∧
      A p.1 (.take i (hi.le.trans (killTime_le _)) p.2.1) =
        R.truthful T σ p.1 (.take i (hi.le.trans (killTime_le _)) p.2.1) ∧
      A ((R.graph.killedPow T q).rot p).1
          (.take (killTime p.2.2 - (i + 1)) ((Nat.sub_le _ _).trans (killTime_le _))
            ((R.graph.killedPow T q).rot p).2.1) =
        R.truthful T σ ((R.graph.killedPow T q).rot p).1
          (.take (killTime p.2.2 - (i + 1)) ((Nat.sub_le _ _).trans (killTime_le _))
            ((R.graph.killedPow T q).rot p).2.1)

variable {R T q} in
/-- A killed walk is hit only at steps before it is killed. -/
theorem Hit.lt_killTime {A : V → WalkLabels D T → α} {σ : V → α}
    {p : V × (Fin T → D) × (Fin T → Fin q)} {i : ℕ} (h : R.Hit T q A σ p i) : i < killTime p.2.2 :=
  h.1

variable {R T q} in
/-- **A killed walk hit at some step is violated** [Dinur, Section 5][Dinur2007]: at that step, the
opinions of its ends are truthful, so its check is the constraint of `R` on a violated dart. -/
theorem not_satisfies_of_hit {A : V → WalkLabels D T → α} {σ : V → α}
    {p : V × (Fin T → D) × (Fin T → Fin q)} {i : ℕ} (h : R.Hit T q A σ p i) :
    ¬ (R.power T q).toConstraintGraph.Satisfies A p := by
  obtain ⟨hi, hσ, h₁, h₂⟩ := h
  intro hA
  have := satisfies_power_iff.1 hA i hi
  rw [h₁, h₂, rel_truthful_iff _ _ _ _ _ hi] at this
  exact hσ this

/-! ### Bookkeeping -/

omit [NeZero q] in
/-- The powered constraint graph is `|D| ^ T q ^ T`-regular. -/
theorem card_label_power [Fintype D] :
    Fintype.card ((Fin T → D) × (Fin T → Fin q)) = Fintype.card D ^ T * q ^ T := by
  simp

omit [NeZero q] in
/-- The powered constraint graph has `|V| |D| ^ T q ^ T` darts. -/
theorem card_darts_power [Fintype V] [Fintype D] :
    Fintype.card (V × (Fin T → D) × (Fin T → Fin q)) =
      Fintype.card V * (Fintype.card D ^ T * q ^ T) := by
  rw [Fintype.card_prod, card_label_power]

/-- The alphabet of the powered constraint graph has `|α| ^ (∑ ℓ ≤ T, |D| ^ ℓ)` letters. -/
theorem card_alphabet_power [Fintype D] [DecidableEq D] [Fintype α] :
    Fintype.card (WalkLabels D T → α) =
      Fintype.card α ^ ∑ ℓ ∈ range (T + 1), Fintype.card D ^ ℓ := by
  rw [Fintype.card_fun, WalkLabels.card_eq]

end RegularConstraintGraph

end PCP

end Cslib
