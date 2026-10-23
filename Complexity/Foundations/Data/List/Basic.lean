/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD

/-!
# List identities and fold invariants

## Main results

* `List.foldl_take_invariant`: an index-dependent invariant holds after every prefix of a fold.
* `List.foldr_ite_eq_of_mem`: a chain of equality tests selects the branch of a contained tag.
  Used by deterministic and probabilistic finite-control certificates.
* `List.getD_mem_or`, `List.getD_idxOf`: a defaulted lookup returns a list member or the default
  value, and returns a member at its first index.
* `List.getD_map_range`: look up a function tabulated over a bounded range.
* `List.countP_and_not_add_countP_and`: the members satisfying `p` split by whether they satisfy
  `q`.
* `List.length_flatMap_le`: blocks of bounded length have bounded total length.
* `List.decide_mem_eq_any`: membership as a scan of the list.
* `List.getD_set_self`, `List.getD_set_ne`, `List.forall_mem_set_of_forall_mem`,
  `List.getD_le_of_forall_le`: lists as register files, updated by `List.set` and read by
  `List.getD`.
* `List.replicate_not_append_cons_inj`, `List.replicate_true_append_false_inj`: a unary block
  followed by a delimiter bit determines both its length and the remaining suffix.

## References

Adapts the selection identity from `Computability/Probabilistic/Finite.lean` on the cslib
`crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

/-- An invariant depending on the number of consumed elements holds after every bounded prefix
fold if it holds initially and is preserved by the next list element. Unlike `List.foldlRecOn`,
preservation may depend on the position. This is a semantic rule with no resource assumptions. -/
theorem List.foldl_take_invariant {α β : Type*} (l : List α) (step : β → α → β) (init : β)
    (P : ℕ → β → Prop) (hbase : P 0 init)
    (hstep : ∀ i (hi : i < l.length) state, P i state → P (i + 1) (step state l[i])) :
    ∀ i, i ≤ l.length → P i ((l.take i).foldl step init) := by
  intro i
  induction i with
  | zero => intro _; simpa only [List.take_zero, List.foldl_nil] using hbase
  | succ i ih =>
    intro hi
    have hlt : i < l.length := Nat.lt_of_succ_le hi
    simpa only [List.take_succ_eq_append_getElem hlt, List.foldl_append,
      List.foldl_cons, List.foldl_nil] using hstep i hlt _ (ih (Nat.le_of_lt hlt))

/-- A chain of equality tests selects a contained tag, regardless of duplicates or fallback. -/
theorem List.foldr_ite_eq_of_mem {Tag Value : Type*} [DecidableEq Tag]
    (tags : List Tag) (tag : Tag) (branch : Tag → Value) (fallback : Value) (h : tag ∈ tags) :
    tags.foldr (fun candidate rest => if tag = candidate then branch candidate else rest)
      fallback = branch tag := by
  induction tags with
  | nil => simp at h
  | cons candidate tags ih =>
    by_cases heq : tag = candidate
    · simp [heq]
    · simp only [List.foldr_cons, heq, ↓reduceIte]
      exact ih (List.mem_cons.mp h |>.resolve_left heq)

/-- Blocks of at most `k` elements each, one for each element of `l`, have at most `|l| k`
elements in total. -/
theorem List.length_flatMap_le {α β : Type*} {l : List α} {f : α → List β} {k : ℕ}
    (h : ∀ a ∈ l, (f a).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have hl := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

/-- Membership in a list as a scan of the list, the form in which polynomial-time membership tests
are certified. -/
theorem List.decide_mem_eq_any {α : Type*} [DecidableEq α] (a : α) (l : List α) :
    decide (a ∈ l) = l.any fun u => decide (u = a) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, List.any_eq_true]
  simp

/-! ### Lists as register files -/

/-- Reading the updated entry of a list. -/
theorem List.getD_set_self {α : Type*} {l : List α} {i : ℕ} {x d : α} (h : i < l.length) :
    (l.set i x).getD i d = x := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_set_self]

/-- Reading another entry of an updated list. -/
theorem List.getD_set_ne {α : Type*} {l : List α} {i j : ℕ} {x d : α} (h : i ≠ j) :
    (l.set i x).getD j d = l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

/-- A property of all the entries of a list holds of all the entries of an update by a value
having it. -/
theorem List.forall_mem_set_of_forall_mem {α : Type*} {p : α → Prop} {l : List α} {i : ℕ} {x : α}
    (h : ∀ a ∈ l, p a) (hx : p x) : ∀ a ∈ l.set i x, p a := fun a ha => by
  rcases List.mem_or_eq_of_mem_set ha with ha | rfl
  · exact h a ha
  · exact hx

/-- The entries of a list of numbers at most `B`, read with default `0`, are at most `B`. -/
theorem List.getD_le_of_forall_le {l : List ℕ} {B : ℕ} (h : ∀ a ∈ l, a ≤ B) (j : ℕ) :
    l.getD j 0 ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  rcases hj : l[j]? with _ | a
  · exact Nat.zero_le _
  · exact h a (List.mem_of_getElem? hj)

/-- A defaulted lookup returns a member of the list or the default value. -/
theorem List.getD_mem_or {α : Type*} (l : List α) (j : ℕ) (d : α) :
    l.getD j d ∈ l ∨ l.getD j d = d := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : l[j]? with _ | a
  · exact Or.inr rfl
  · exact Or.inl (List.mem_of_getElem? h)

/-- Looking up the first index of a member of a list returns that member. -/
theorem List.getD_idxOf {α : Type*} [BEq α] [LawfulBEq α] {l : List α} {x : α} (hx : x ∈ l)
    (d : α) : l.getD (l.idxOf x) d = x := by
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.2 hx), List.getElem_idxOf]

/-- Reading a mapped range at a valid index applies the map to that index. -/
theorem List.getD_map_range {α : Type*} (f : ℕ → α) (d : α) {n i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

/-- Partitioning the elements of a list satisfying `p` by whether they satisfy `q`. -/
theorem List.countP_and_not_add_countP_and {α : Type*} (p q : α → Prop) [DecidablePred p]
    [DecidablePred q] (l : List α) :
    l.countP (fun a => ¬ q a ∧ p a) + l.countP (fun a => p a ∧ q a) = l.countP (fun a => p a) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    by_cases hp : p a <;> by_cases hq : q a <;>
      simp only [hp, hq, not_true_eq_false, not_false_eq_true, and_true, and_false,
        decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] <;> omega

/-! ### Unary headers -/

/-- A unary block of copies of `!a` followed by the delimiter `a` determines both its length and the
remaining suffix. -/
theorem List.replicate_not_append_cons_inj {a : Bool} {m m' : ℕ} {l l' : List Bool}
    (h : List.replicate m (!a) ++ a :: l = List.replicate m' (!a) ++ a :: l') :
    m = m' ∧ l = l' := by
  induction m generalizing m' <;> cases m' <;> simp_all [List.replicate_succ]

/-- A unary block of `true` bits followed by `false` determines both its length and the remaining
suffix. -/
theorem List.replicate_true_append_false_inj {m m' : ℕ} {l l' : List Bool}
    (h : List.replicate m true ++ false :: l = List.replicate m' true ++ false :: l') :
    m = m' ∧ l = l' :=
  List.replicate_not_append_cons_inj (a := false) h
