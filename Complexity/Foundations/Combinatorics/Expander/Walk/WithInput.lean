/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.KilledWalk

/-!
# Walk programs carrying an immutable input

An encoded graph supplies a total rotation program with the graph data as an extra input. The
programs here carry that input through each call. Their interpretation lemmas require agreement
only on encoded vertices of the mathematical graph, so malformed inputs and unused vertex names
may have any total behavior.

## Main definitions

* `Cslib.RotationMap.walkAtWithInput`: a vertex reached along a walk.
* `Cslib.RotationMap.powRotWithInput`: a walk and its complete reversed return labels.
* `Cslib.RotationMap.killedPowRotWithInput`: a stopped walk, retaining unused labels and signals.

## Main results

* `Cslib.RotationMap.walkAtWithInput_eq`: agreement with a mathematical trajectory.
* `Cslib.RotationMap.powRotWithInput_eq`: agreement with a mathematical power rotation.
* `Cslib.RotationMap.killedPowRotWithInput_eq`: agreement with a killed power rotation.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [J. Radhakrishnan, *Gap amplification in PCPs using lazy random walks*][Radhakrishnan2006]
-/

@[expose] public section

namespace Cslib.RotationMap

variable {P V W D : Type*} (rotate : P × (W × D) → W × D)

/-- Follow the labels, retaining the original graph input at every rotation call. After all labels
have been used, the walk stays at its endpoint. -/
def walkAtWithInput {T : ℕ} (p : P × (W × (Fin T → D))) : ℕ → W
  | 0 => p.2.1
  | i + 1 => if h : i < T then
      (rotate (p.1, walkAtWithInput p i, p.2.2 ⟨i, h⟩)).1
    else walkAtWithInput p i

/-- A power rotation carries the immutable input and reverses all return labels. -/
def powRotWithInput : (T : ℕ) → P × (W × (Fin T → D)) → W × (Fin T → D)
  | 0, p => p.2
  | T + 1, p =>
    let first := rotate (p.1, p.2.1, p.2.2 0)
    let rest := powRotWithInput T (p.1, first.1, Fin.tail p.2.2)
    (rest.1, Fin.snoc rest.2 first.2)

/-- A killed power reverses only the used prefix, preserving unused labels and kill signals. -/
def killedPowRotWithInput (T q : ℕ) [NeZero q]
    (p : P × (W × ((Fin T → D) × (Fin T → Fin q)))) : W × ((Fin T → D) × (Fin T → Fin q)) :=
  let stopped := powRotWithInput rotate (killTime p.2.2.2)
    (p.1, p.2.1, Fin.take _ (killTime_le p.2.2.2) p.2.2.1)
  (stopped.1, fun i => if h : i.val < killTime p.2.2.2 then stopped.2 ⟨i.val, h⟩ else p.2.2.1 i,
    p.2.2.2)

/-- Once the stopping time is known, the dependent prefix has that concrete length. -/
theorem killedPowRotWithInput_of_killTime {T q : ℕ} [NeZero q]
    (p : P × (W × ((Fin T → D) × (Fin T → Fin q)))) {n : ℕ} (hn : n ≤ T)
    (hc : killTime p.2.2.2 = n) :
    killedPowRotWithInput rotate T q p =
      let stopped := powRotWithInput rotate n (p.1, p.2.1, Fin.take n hn p.2.2.1)
      (stopped.1, fun i => if h : i.val < n then stopped.2 ⟨i.val, h⟩ else p.2.2.1 i, p.2.2.2) := by
  subst n
  rfl

variable (input : P) (G : RotationMap V D) (encode : V → W)
  (hrotate : ∀ v d, rotate (input, encode v, d) = (encode (G.rot (v, d)).1, (G.rot (v, d)).2))

include hrotate in
/-- Agreement of one rotation on encoded vertices gives agreement of every trajectory. -/
theorem walkAtWithInput_eq {T : ℕ} (v : V) (k : Fin T → D) (m : ℕ) :
    walkAtWithInput rotate (input, encode v, k) m = encode (G.walkAt (v, k) m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    by_cases hm : m < T
    · simp only [walkAtWithInput, dite_eq_left hm, ih, hrotate,
        walkAt_succ_of_lt _ _ hm, neighbor_def]
    · simp only [walkAtWithInput, dite_eq_right hm, ih,
        walkAt_succ_of_le _ _ (Nat.le_of_not_gt hm)]

include hrotate in
/-- A power program returns both the encoded endpoint and exactly the reversed mathematical
return labels. No hypothesis is needed on rotations of unused vertex names. -/
theorem powRotWithInput_eq (T : ℕ) (v : V) (k : Fin T → D) :
    powRotWithInput rotate T (input, encode v, k) =
      (encode ((G.pow T).rot (v, k)).1, ((G.pow T).rot (v, k)).2) := by
  induction T generalizing v with
  | zero => rfl
  | succ T ih =>
    simp only [powRotWithInput, hrotate, ih, pow, powRot]

include hrotate in
/-- A killed power program agrees with the mathematical stopped walk, including its unused
labels and original kill signals. -/
theorem killedPowRotWithInput_eq (T q : ℕ) [NeZero q]
    (v : V) (k : Fin T → D) (c : Fin T → Fin q) :
    killedPowRotWithInput rotate T q (input, encode v, k, c) =
      (encode ((G.killedPow T q).rot (v, k, c)).1, ((G.killedPow T q).rot (v, k, c)).2) := by
  simp only [killedPowRotWithInput, powRotWithInput_eq rotate input G encode hrotate, killedPow]

end Cslib.RotationMap
