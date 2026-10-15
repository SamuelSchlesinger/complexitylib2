/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Walk

/-!
# Killed walks

Walks whose length is random, killed after each step with probability `1 / q` and stopped after `T`
steps, are used in the powering step of Dinur's proof of the PCP theorem [Dinur2007]
[Radhakrishnan2006]. A killed walk on a `D`-regular multigraph `G` is presented by `T` labels of `G`
and `T` kill signals `c : Fin T → Fin q`: it follows the labels until its kill time `killTime c`,
the first step `i` with `c i = 0` (or `T` if there is none), and the remaining labels carry no
meaning. Under uniformly random signals the kill time has the geometric law truncated at `T`: it is
`m < T` with probability `(1 - 1 / q) ^ m / q` (`card_filter_killTime_eq`) and at least `m ≤ T` with
probability `(1 - 1 / q) ^ m` (`card_filter_le_killTime`).

Given that it is killed at step `ℓ < T`, a uniformly random killed walk is a uniformly random walk
of length `ℓ` (`sum_ite_killTime_eq`, `card_filter_killTime_eq_and`). Splitting it at a step
`i < ℓ` with `splitWalk` counts the killed walks crossing a given dart at step `i` by independent
factors for the `i` steps before it and the `j = ℓ - (i + 1)` steps after it, times the weight
`|D| ^ (T - ℓ) (q - 1) ^ ℓ q ^ (T - (ℓ + 1))` of the length `ℓ`
(`card_filter_killTime_eq_and_splitWalk`). The factor
`(q - 1) ^ ℓ = (q - 1) ^ i (q - 1) (q - 1) ^ j` of that weight splits between the two sides of the
crossed edge: up to the truncation at `T`, the lengths `i` and `j` of the two sides are
independent, which is what the first-moment count of the powering step uses.

The killed walks are the darts of the killed power `G.killedPow T q`, whose edge labelled `(k, c)`
at `v` is the killed walk from `v` (`neighbor_killedPow`). Its rotation map reverses a killed walk
up to its kill time (`rot_pow_killTime`) and leaves its unused labels and its signals alone, so
that the reverse is killed at the same step.

## Main definitions

* `Cslib.RotationMap.killTime`: the step at which a walk with given kill signals is killed.
* `Cslib.RotationMap.killedPow`: the killed power of a rotation map.

## Main results

* `Cslib.RotationMap.killTime_cons`: a walk survives its first step unless its first signal is `0`,
  and is then killed one step after the walk along its remaining signals.
* `Cslib.RotationMap.card_filter_killTime_eq`, `Cslib.RotationMap.card_filter_le_killTime`: the
  truncated geometric law of the kill time.
* `Cslib.RotationMap.sum_ite_killTime_eq`, `Cslib.RotationMap.card_filter_killTime_eq_and`: given
  its kill time, a killed walk is a uniformly random walk of that length.
* `Cslib.RotationMap.card_filter_killTime_eq_and_splitWalk`: the crossing count for killed walks.
* `Cslib.RotationMap.neighbor_killedPow`, `Cslib.RotationMap.rot_pow_killTime`: the edges of the
  killed power and their reverses.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [J. Radhakrishnan, *Gap amplification in PCPs using lazy random walks*][Radhakrishnan2006]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset

variable {V D : Type*} (G : RotationMap V D)

section KillTime

variable {T q : ℕ} [NeZero q]

/-- The step at which a walk with kill signals `c : Fin T → Fin q` is killed: the first step `i`
with `c i = 0`, or `T`, where the walk is stopped, if there is none. -/
def killTime (c : Fin T → Fin q) : ℕ :=
  Nat.find (p := fun m ↦ ∀ h : m < T, c ⟨m, h⟩ = 0) ⟨T, fun h ↦ absurd h (lt_irrefl T)⟩

/-- A walk of length `T` is killed by step `T`. -/
theorem killTime_le (c : Fin T → Fin q) : killTime c ≤ T :=
  Nat.find_min' _ fun h ↦ absurd h (lt_irrefl T)

/-- A walk survives its step `i < T` when none of its first `i + 1` signals is `0`. -/
theorem lt_killTime_iff (c : Fin T → Fin q) {i : ℕ} (hi : i < T) :
    i < killTime c ↔ ∀ j : Fin T, (j : ℕ) ≤ i → c j ≠ 0 := by
  rw [killTime, Nat.lt_find_iff]
  exact ⟨fun h j hj hc ↦ h j hj fun _ ↦ hc, fun h m hm hc ↦ h ⟨m, by omega⟩ hm (hc (by omega))⟩

/-- A walk is killed at its step `m < T` when its `m`-th signal is the first that is `0`. -/
theorem killTime_eq_iff (c : Fin T → Fin q) {m : ℕ} (hm : m < T) :
    killTime c = m ↔ c ⟨m, hm⟩ = 0 ∧ ∀ j : Fin T, (j : ℕ) < m → c j ≠ 0 := by
  rw [killTime, Nat.find_eq_iff]
  exact ⟨fun h ↦ ⟨h.1 hm, fun j hj hc ↦ h.2 j hj fun _ ↦ hc⟩,
    fun h ↦ ⟨fun _ ↦ h.1, fun n hn hc ↦ h.2 ⟨n, by omega⟩ hn (hc (by omega))⟩⟩

/-- A walk is killed at its first step if its first signal is `0`, and otherwise one step after
the walk along its remaining signals is killed. -/
theorem killTime_cons (a : Fin q) (c : Fin T → Fin q) :
    killTime (Fin.cons a c : Fin (T + 1) → Fin q) = if a = 0 then 0 else killTime c + 1 := by
  split_ifs with ha
  · rw [killTime, Nat.find_eq_zero]
    exact fun _ ↦ ha
  · rw [killTime,
      Nat.find_comp_succ _ ⟨T, fun h ↦ absurd h (lt_irrefl _)⟩ fun h ↦ ha (h T.succ_pos)]
    exact congrArg (· + 1) (Nat.find_congr' fun {n} ↦
      ⟨fun h hn ↦ h (Nat.succ_lt_succ hn), fun h hn ↦ h (Nat.lt_of_succ_lt_succ hn)⟩)

/-- Under uniformly random signals, a walk of length `T` is killed at its step `m < T` with
probability `(1 - 1 / q) ^ m / q`: the signals that kill it there number
`(q - 1) ^ m * q ^ (T - (m + 1))`. -/
theorem card_filter_killTime_eq {m : ℕ} (hm : m < T) :
    #{c : Fin T → Fin q | killTime c = m} = (q - 1) ^ m * q ^ (T - (m + 1)) := by
  induction T generalizing m with
  | zero => omega
  | succ T ih =>
    rw [card_filter, ← Fintype.sum_equiv (Fin.consEquiv fun _ ↦ Fin q)
      (fun x ↦ if killTime (Fin.cons x.1 x.2 : Fin (T + 1) → Fin q) = m then 1 else 0) _
      fun _ ↦ rfl, Fintype.sum_prod_type]
    simp only [killTime_cons]
    rcases m with _ | m
    · simp [sum_ite_irrel]
    · have h (a : Fin q) (c : Fin T → Fin q) :
          (if (if a = 0 then 0 else killTime c + 1) = m + 1 then 1 else 0) =
            if a = 0 then 0 else if killTime c = m then 1 else 0 := by
        split_ifs <;> simp_all
      simp only [h, sum_ite_irrel, sum_const_zero, ← card_filter, ih (by omega : m < T)]
      rw [sum_ite, sum_const_zero, zero_add, sum_const, filter_ne' univ (0 : Fin q),
        card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, smul_eq_mul,
        show T + 1 - (m + 1 + 1) = T - (m + 1) by omega]
      ring

/-- Under uniformly random signals, a walk of length `T` survives its first `m ≤ T` steps with
probability `(1 - 1 / q) ^ m`: the signals that let it number `(q - 1) ^ m * q ^ (T - m)`. -/
theorem card_filter_le_killTime {m : ℕ} (hm : m ≤ T) :
    #{c : Fin T → Fin q | m ≤ killTime c} = (q - 1) ^ m * q ^ (T - m) := by
  induction T generalizing m with
  | zero => simp [Nat.le_zero.1 hm]
  | succ T ih =>
    rw [card_filter, ← Fintype.sum_equiv (Fin.consEquiv fun _ ↦ Fin q)
      (fun x ↦ if m ≤ killTime (Fin.cons x.1 x.2 : Fin (T + 1) → Fin q) then 1 else 0) _
      fun _ ↦ rfl, Fintype.sum_prod_type]
    simp only [killTime_cons]
    rcases m with _ | m
    · simp [pow_succ']
    · have h (a : Fin q) (c : Fin T → Fin q) :
          (if m + 1 ≤ (if a = 0 then 0 else killTime c + 1) then 1 else 0) =
            if a = 0 then 0 else if m ≤ killTime c then 1 else 0 := by
        split_ifs <;> simp_all
      simp only [h, sum_ite_irrel, sum_const_zero, ← card_filter, ih (by omega : m ≤ T)]
      rw [sum_ite, sum_const_zero, zero_add, sum_const, filter_ne' univ (0 : Fin q),
        card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, smul_eq_mul,
        show T + 1 - (m + 1) = T - m by omega]
      ring

end KillTime

section Law

variable {T q : ℕ} [NeZero q] [Fintype V] [Fintype D]

/-- Summing a function of the walk along the first `ℓ` labels over the walks of length `T` sums it
`|D| ^ (T - ℓ)` times over the walks of length `ℓ`. -/
private theorem sum_comp_take {M : Type*} [AddCommMonoid M] {ℓ : ℕ} (h : ℓ ≤ T)
    (f : V × (Fin ℓ → D) → M) :
    ∑ p : V × (Fin T → D), f (p.1, Fin.take ℓ h p.2) = Fintype.card D ^ (T - ℓ) • ∑ w, f w := by
  refine (Fintype.sum_equiv ((Equiv.refl V).prodCongr
    (((finCongr (Nat.add_sub_of_le h).symm).arrowCongr (Equiv.refl D)).trans
      (Fin.appendEquiv ℓ (T - ℓ)).symm)) _ (fun x ↦ f (x.1, x.2.1)) fun _ ↦ rfl).trans ?_
  simp only [Fintype.sum_prod_type, sum_const, card_univ, smul_sum, Fintype.card_pi, prod_const,
    Fintype.card_fin]

/-- **The law of a killed walk.** Given that it is killed at its step `ℓ < T`, a uniformly random
walk of length `T` with uniformly random kill signals is, up to that step, a uniformly random walk
of length `ℓ`: summing a function of its first `ℓ` steps over the walks and signals killed at step
`ℓ` sums it `|D| ^ (T - ℓ) (q - 1) ^ ℓ q ^ (T - (ℓ + 1))` times over the walks of length `ℓ`. -/
theorem sum_ite_killTime_eq {M : Type*} [AddCommMonoid M] {ℓ : ℕ} (hℓ : ℓ < T)
    (F : V × (Fin ℓ → D) → M) :
    ∑ x : V × (Fin T → D) × (Fin T → Fin q),
        (if killTime x.2.2 = ℓ then F (x.1, Fin.take ℓ hℓ.le x.2.1) else 0) =
      (Fintype.card D ^ (T - ℓ) * ((q - 1) ^ ℓ * q ^ (T - (ℓ + 1)))) • ∑ w, F w := by
  refine (Fintype.sum_equiv (Equiv.prodAssoc V (Fin T → D) (Fin T → Fin q)).symm _
    (fun x ↦ if killTime x.2 = ℓ then F (x.1.1, Fin.take ℓ hℓ.le x.1.2) else 0)
    fun _ ↦ rfl).trans ?_
  rw [Fintype.sum_prod_type]
  simp only [sum_ite, sum_const_zero, add_zero, sum_const, card_filter_killTime_eq hℓ]
  rw [← smul_sum, sum_comp_take hℓ.le F, smul_smul, mul_comm]

/-- **The law of a killed walk**, counting form: the walks of length `T` and kill signals for which
the walk is killed at its step `ℓ < T` and its first `ℓ` steps satisfy `P` number
`#{w | P w} |D| ^ (T - ℓ) (q - 1) ^ ℓ q ^ (T - (ℓ + 1))`. -/
theorem card_filter_killTime_eq_and {ℓ : ℕ} (hℓ : ℓ < T) (P : V × (Fin ℓ → D) → Prop)
    [DecidablePred P] :
    #{x : V × (Fin T → D) × (Fin T → Fin q) |
        killTime x.2.2 = ℓ ∧ P (x.1, Fin.take ℓ hℓ.le x.2.1)} =
      #{w | P w} * (Fintype.card D ^ (T - ℓ) * ((q - 1) ^ ℓ * q ^ (T - (ℓ + 1)))) := by
  rw [card_filter, card_filter, mul_comm, ← smul_eq_mul, ← sum_ite_killTime_eq hℓ]
  simp only [ite_and]

/-- **The crossing count for killed walks.** Counted by the dart `d` crossed at step `i`, the walks
of length `T` and kill signals for which the walk is killed at its step `ℓ < T`, crosses `d` at its
step `i < ℓ`, the reverse of its first `i` steps satisfies `P d` and its steps from `i + 1` to `ℓ`
satisfy `Q d` are counted by independent factors and the weight of the length `ℓ`. -/
theorem card_filter_killTime_eq_and_splitWalk {ℓ : ℕ} (hℓ : ℓ < T) (i : Fin ℓ)
    (P : V × D → (Fin i → D) → Prop) (Q : V × D → (Fin (ℓ - (i + 1)) → D) → Prop)
    [∀ d, DecidablePred (P d)] [∀ d, DecidablePred (Q d)] :
    #{x : V × (Fin T → D) × (Fin T → Fin q) | killTime x.2.2 = ℓ ∧
        (P (G.walkDart (x.1, Fin.take ℓ hℓ.le x.2.1) i)
            ((G.pow i).rot (x.1, Fin.take i i.isLt.le (Fin.take ℓ hℓ.le x.2.1))).2 ∧
          Q (G.walkDart (x.1, Fin.take ℓ hℓ.le x.2.1) i)
            (G.walkDrop (x.1, Fin.take ℓ hℓ.le x.2.1) (i + 1)).2)} =
      (∑ d, #{r | P d r} * #{s | Q d s}) *
        (Fintype.card D ^ (T - ℓ) * ((q - 1) ^ ℓ * q ^ (T - (ℓ + 1)))) := by
  rw [← G.card_filter_splitWalk i P Q]
  exact card_filter_killTime_eq_and hℓ fun w ↦
    P (G.walkDart w i) ((G.pow i).rot (w.1, Fin.take i i.isLt.le w.2)).2 ∧
      Q (G.walkDart w i) (G.walkDrop w (i + 1)).2

end Law

section KilledPow

/-- Overwriting the first `n` labels with `r` leaves `r` as the first `n` labels. -/
private theorem take_dite {T n : ℕ} (h : n ≤ T) (r : Fin n → D) (k : Fin T → D) :
    Fin.take n h (fun i ↦ if h' : (i : ℕ) < n then r ⟨i, h'⟩ else k i) = r := by
  funext j
  simp [Fin.take_apply, j.isLt]

variable (T q : ℕ) [NeZero q]

/-- The **killed power** `G.killedPow T q`: the multigraph on the vertices of `G` with
an edge for every walk in `G` of length `T` with kill signals in `Fin q`. The edge labelled `(k, c)`
at `v` is the walk from `v` along the labels `k`, stopped when it is killed at step `killTime c`;
its rotation map reverses the walk up to that step and leaves the unused labels and the signals
alone, so that the reverse is killed at the same step. A step of its random walk is a random walk
on `G` killed after each step with probability `1 / q`, and stopped after `T` steps. -/
def killedPow : RotationMap V ((Fin T → D) × (Fin T → Fin q)) where
  rot x :=
    (((G.pow (killTime x.2.2)).rot (x.1, Fin.take _ (killTime_le x.2.2) x.2.1)).1,
      fun i ↦ if h : (i : ℕ) < killTime x.2.2 then
        ((G.pow (killTime x.2.2)).rot (x.1, Fin.take _ (killTime_le x.2.2) x.2.1)).2 ⟨i, h⟩
        else x.2.1 i,
      x.2.2)
  rot_involutive := by
    rintro ⟨v, k, c⟩
    dsimp only
    have hR := (G.pow (killTime c)).rot_rot (v, Fin.take _ (killTime_le c) k)
    generalize (G.pow (killTime c)).rot (v, Fin.take _ (killTime_le c) k) = R at hR ⊢
    rw [take_dite, Prod.mk.eta, hR]
    refine Prod.ext rfl (Prod.ext (funext fun i ↦ ?_) rfl)
    dsimp only
    split_ifs <;> rfl

/-- The edge labelled `(k, c)` at `v` in the killed power leads to the vertex where the walk from
`v` along `k` is killed. -/
theorem neighbor_killedPow (v : V) (x : (Fin T → D) × (Fin T → Fin q)) :
    (G.killedPow T q).neighbor v x = G.walkAt (v, x.1) (killTime x.2) :=
  G.fst_rot_pow_take (v, x.1) (killTime_le x.2)

/-- The rotation map of the killed power leaves the kill signals alone. -/
@[simp]
theorem snd_snd_rot_killedPow (p : V × (Fin T → D) × (Fin T → Fin q)) :
    ((G.killedPow T q).rot p).2.2 = p.2.2 :=
  rfl

/-- The rotation map of the killed power reverses the walk up to the step at which it is killed. -/
theorem rot_pow_killTime (p : V × (Fin T → D) × (Fin T → Fin q)) :
    (G.pow (killTime p.2.2)).rot (p.1, Fin.take _ (killTime_le p.2.2) p.2.1) =
      (((G.killedPow T q).rot p).1,
        Fin.take _ (killTime_le p.2.2) ((G.killedPow T q).rot p).2.1) :=
  Prod.ext rfl (take_dite _ _ _).symm

end KilledPow

end Cslib.RotationMap
