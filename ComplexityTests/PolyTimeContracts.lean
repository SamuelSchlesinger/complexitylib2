/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Tactic.PolyTime

/-!
# Encoding inference and input-dependent loop contracts

Fixed scans need no encoding of their indices. Runtime scans retain joint certificates, while
loop bounds charge the full framed state on every reachable iteration.
-/

namespace ComplexityTests.PolyTimeContracts

open Turing.MultiTapeTM

-- Fixed lists may contain higher-universe objects for which no bit encoding is supplied.
example {ι : Type 1} (indices : List ι) (test : List Bool → ι → Bool)
    (htest : ∀ i ∈ indices,
      ComputableTidilyInPolyTime (fun word => test word i) encBits encBool) :
    ComputableTidilyInPolyTime (fun word => indices.all (test word)) encBits encBool := by
  fun_prop

example {ι : Type 1} (indices : List ι) (test : List Bool → ι → Bool)
    (htest : ∀ i ∈ indices,
      ComputableTidilyInPolyTime (fun word => test word i) encBits encBool) :
    ComputableTidilyInPolyTime (fun word => indices.any fun i => test word i)
      encBits encBool := by
  polytime

-- No callback certificate is needed when there are no indices.
example (test : List Bool → Fin 0 → Bool) :
    ComputableTidilyInPolyTime (fun word => ([] : List (Fin 0)).all (test word))
      encBits encBool := by
  exact ComputableTidilyInPolyTime.allConst [] (by simp)

-- The same runtime scan supports unrelated element representations.
example {α β : Type} (input : α ↪ List Bool) (element : β ↪ List Bool)
    (values : α → List β) (test : α × β → Bool)
    (hvalues : ComputableTidilyInPolyTime values input (encList element))
    (htest : ComputableTidilyInPolyTime test (encPair input element) encBool) :
    ComputableTidilyInPolyTime
      (fun x => let entries := values x; entries.all fun value => test (x, value))
      input encBool := by
  fail_if_success (clear hvalues; polytime)
  fail_if_success (clear htest; polytime)
  polytime

example {α β : Type} (input : α ↪ List Bool) (element : β ↪ List Bool)
    (values : α → List β) (test : α × β → Bool)
    (hvalues : ComputableTidilyInPolyTime values input (encList element))
    (htest : ComputableTidilyInPolyTime test (encPair input element) encBool) :
    ComputableTidilyInPolyTime (fun x => (values x).any fun value => test (x, value))
      input encBool := by
  polytime

-- Raw and framed Boolean words use their existing list interfaces.
example : ComputableTidilyInPolyTime
    (fun p : List Bool × Bool => p.1.all fun bit => bit == p.2)
    (encPair encBits encBool) encBool := by polytime

example : ComputableTidilyInPolyTime
    (fun p : List Bool × Bool => p.1.all (fun bit => bit == p.2))
    (encPair (encList encBool) encBool) encBool := by polytime

example : ComputableTidilyInPolyTime
    (fun p : List ℕ × ℕ => p.1.any fun n => n == p.2)
    (encPair (encList encNat) encNat) encBool := by polytime

example : ComputableTidilyInPolyTime
    (fun p : List ℕ × ℕ => p.1.any fun n => n == p.2)
    (encPair (encList encUnary) encUnary) encBool := by polytime

-- Separate certificates at each fixed index give no uniform runtime-index certificate.
example (test : List Bool → ℕ → Bool)
    (_hfixed : ∀ n, ComputableTidilyInPolyTime (fun word => test word n) encBits encBool) :
    True := by
  fail_if_success
    have : ComputableTidilyInPolyTime
        (fun word => (List.range word.length).all (test word)) encBits encBool := by polytime
  trivial

-- An arbitrary mathematical bound need not have a computation certificate.
example {α β : Type} {input : α ↪ List Bool} {stateEncoding : β ↪ List Bool}
    {initial : α → β} {step : β → β} {count bound : α → ℕ}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (hstep : ComputableTidilyInPolyTime step stateEncoding stateEncoding)
    (invariant : α → ℕ → β → Prop)
    (hbase : ∀ x, invariant x 0 (initial x))
    (hpreserve : ∀ x i state, i < count x → invariant x i state →
      invariant x (i + 1) (step state))
    (hsize : PolyBounded (fun x => (input x).length) bound)
    (hbound : ∀ x i state, i ≤ count x → invariant x i state →
      (stateEncoding state).length ≤ bound x) :
    ComputableTidilyInPolyTime (fun x => step^[count x] (initial x)) input stateEncoding := by
  exact (ComputableTidilyInPolyTime.iterate_spec hcount hinitial hstep invariant
    hbase hpreserve hsize hbound).1

-- Accumulating rows charges each copied row and every outer list frame.
private def repeatRows (p : List Bool × ℕ) : List (List Bool) :=
  (fun rows => p.1 :: rows)^[p.2] []

private theorem repeatRows_spec :
    ComputableTidilyInPolyTime repeatRows (encPair encBits encUnary) (encList encBits) ∧
      ∀ p, (repeatRows p).length = p.2 ∧ ∀ row ∈ repeatRows p, row = p.1 := by
  unfold repeatRows
  refine ComputableTidilyInPolyTime.iterateWith_spec (par := Prod.fst)
    (count := Prod.snd) (init := fun _ => []) (step := List.cons)
    (by polytime) (by polytime) (by polytime) (by polytime)
    (invariant := fun p i rows => rows.length = i ∧ ∀ row ∈ rows, row = p.1)
    (by simp) ?_ (size := fun p => p.2 * (2 * p.1.length + 1)) ?_ ?_
  · intro p i rows _ h
    simpa only [List.length_cons, h.1, List.mem_cons, forall_eq_or_imp, true_and]
      using h.2
  · exact ComputableTidilyInPolyTime.polyBounded (by polytime)
  · intro p i rows hi h
    calc
      (encList encBits rows).length ≤ rows.length * (2 * p.1.length + 1) :=
        length_encList_le encBits rows fun row hrow => by simp [h.2 row hrow]
      _ ≤ _ := by simpa only [h.1] using Nat.mul_le_mul_right (2 * p.1.length + 1) hi

-- A nested loop composes the row certificate; no intermediate representation is supplied here.
example : ComputableTidilyInPolyTime (fun p : List Bool × ℕ =>
    (List.range p.2).flatMap fun n => repeatRows (p.1, n))
    (encPair encBits encUnary) (encList encBits) := by
  have h := repeatRows_spec.1
  polytime

example : repeatRows ([true, false], 0) = [] := rfl
example : (encList encBits (repeatRows ([true, false], 3))).length = 15 := by decide

-- A standard outer operation leaves the fold's meaningful step and growth contracts usable.
example (step : List Bool → Bool → List Bool) (growth : ℕ)
    (hstep : ComputableTidilyInPolyTime (fun pair : List Bool × Bool => step pair.1 pair.2)
      (encPair encBits encBool) encBits)
    (hgrowth : ∀ word bit, (step word bit).length ≤ word.length + growth) :
    ComputableTidilyInPolyTime (fun word : List Bool => (word.foldl step []).reverse)
      encBits encBits := by
  fail_if_success (clear hstep; polytime)
  fail_if_success (clear hgrowth; polytime)
  polytime

-- Framed input and state elements may have unrelated encodings; let notation needs no annotation.
example {α β : Type} (item : α ↪ List Bool) (stateElement : β ↪ List Bool)
    (step : List β → α → List β) (growth : ℕ)
    (hstep : ComputableTidilyInPolyTime (fun pair : List β × α => step pair.1 pair.2)
      (encPair (encList stateElement) item) (encList stateElement))
    (hgrowth : ∀ state value, (encList stateElement (step state value)).length ≤
      (encList stateElement state).length + growth) :
    ComputableTidilyInPolyTime
      (fun list : List α => let accumulated := list.foldl step []; accumulated.reverse)
      (encList item) (encList stateElement) := by polytime

-- Growth outside the reachable invariant does not matter; the step still has a uniform certificate.
example : ComputableTidilyInPolyTime
    (fun n : ℕ => (fun word : List Bool => if word.isEmpty then [] else word ++ word)^[n] [])
    encUnary encBits := by
  refine (ComputableTidilyInPolyTime.iterate_spec (by polytime) (by polytime) (by polytime)
    (fun _ _ word => word = []) (by simp) ?_ (.const 0) ?_).1
  · intros
    simp_all
  · intros
    simp_all

-- A small final projection supplies no bound on a loop's intermediate storage.
example : True := by
  fail_if_success
    have : ComputableTidilyInPolyTime (fun n : ℕ =>
        ((fun p : ℕ × List Bool =>
          if p.1 = 0 then (0, []) else (p.1 - 1, p.2 ++ p.2))^[n + 1] (n, [true])).2)
        encUnary encBits := by polytime
  trivial

end ComplexityTests.PolyTimeContracts
