/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Multigraph
public import Complexity.Computability.Circuit.Frontier.Sweep
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Constraint networks and their sweeps

A *constraint network* is a multigraph whose edges carry values in an alphabet `U` and whose
vertices impose *local constraints*: the constraint at `v` sees only the values on the edges at
`v` and the inputs read at `v`. Each input is read at no more than one vertex. An input is
*accepted* when some assignment of values to the edges satisfies every constraint.

Networks are a semantics-free form of computation. Nothing in them is directed: a gate
`z = g(x, y)` becomes the relation `{(x, y, z) | z = g(x, y)}` between three edge values, and
the network never needs to invert `g`.

**The separator lemma** (`Network.Satisfies.splice`). Cut the vertices into a set `L` and its
complement. If two satisfying assignments, for inputs `x` and `y`, agree on the edge cut of `L`,
then taking the first assignment near `L` and the second away from it satisfies the network for
the input that reads like `x` at `L` and like `y` elsewhere. Once the values on the cut are
fixed, the two sides of the network are independent.

**Sweeping a network.** Process the vertices in the order of a layout. At time `t` the inputs
read by the first `t` vertices are revealed, and the message is the list of values on the
frontier, the edge cut after the first `t` vertices (`Network.sweep`). By the separator lemma
this is a sweep of the accepted set. A transition is determined by the values on two consecutive
frontiers and the inputs read at the vertex processed in between, so a layout of width `w` in a
network of degree at most `d`, reading at most `m` inputs per vertex, yields at most
`|U| ^ (w + d + m)` transitions per step (`Network.ncard_accepted_le`). One last step reveals the
inputs that the network does not read.

The sweep is built from a more general one (`Network.frontierSweep`): any values `val x` on the
edges, not necessarily satisfying, together with an *extra* message at each time, form a sweep
as soon as the inputs sending the same messages splice.

## Main definitions

* `Cslib.Circuits.Frontier.Network U ι V E`: a constraint network.
* `Cslib.Circuits.Frontier.Network.accepted`: its accepted inputs.
* `Cslib.Circuits.Frontier.Network.frontierSweep`: frontier values and extra messages along a
  layout, as a sweep.
* `Cslib.Circuits.Frontier.Network.sweep`: the sweep of the accepted set along a layout.

## Main results

* `Cslib.Circuits.Frontier.Network.Satisfies.splice`: the separator lemma.
* `Cslib.Circuits.Frontier.Network.dependsOn_read`: acceptance depends only on the inputs read.
* `Cslib.Circuits.Frontier.Network.ncard_transition_le`: transitions at a step by width.
* `Cslib.Circuits.Frontier.Network.ncard_accepted_le`: the frontier counting lemma for networks.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

/-- A *constraint network* over the alphabet `U` with inputs indexed by `ι`: a multigraph on
vertices `V` and edges `E`, the vertex at which each input is read (if any), and a constraint at
each vertex that sees only the values on the edges at that vertex and the inputs read there. -/
structure Network (U ι V E : Type*) extends Multigraph V E where
  /-- The vertex at which each input is read, if it is read at all. -/
  site : ι → Option V
  /-- The constraint at a vertex, on the input and the values on the edges. -/
  Constraint : V → (ι → U) → (E → U) → Prop
  /-- Constraints are local: the constraint at `v` sees only the inputs read at `v` and the
  values on the edges incident to `v`. -/
  constraint_congr : ∀ v x x' α α', (∀ i, site i = some v → x i = x' i) →
    (∀ e, src e = v ∨ tgt e = v → α e = α' e) → Constraint v x α → Constraint v x' α'

namespace Network

variable {U ι V E : Type*} (N : Network U ι V E)

/-- An assignment of values to the edges satisfies every constraint on the input `x`. -/
def Satisfies (x : ι → U) (α : E → U) : Prop :=
  ∀ v, N.Constraint v x α

/-- The *accepted* inputs: those with a satisfying assignment. -/
def accepted : Set (ι → U) :=
  {x | ∃ α, N.Satisfies x α}

/-- The inputs read at a vertex. -/
def readAt (v : V) : Set ι :=
  {i | N.site i = some v}

/-- The inputs read at the vertices of `L`. -/
def readIn (L : Set V) : Set ι :=
  {i | ∃ v ∈ L, N.site i = some v}

/-- The inputs read by the network. -/
def read : Set ι :=
  N.readIn univ

@[simp] theorem readIn_empty : N.readIn ∅ = ∅ := by
  ext i; simp [readIn]

/-- **The separator lemma.** Let `α` satisfy the network on the input `x` and `β` on the input
`y`, and suppose that they agree on the edge cut of `L`. Then the network is satisfied on any
input `z` that agrees with `x` on the inputs read in `L` and with `y` on the others, by an
assignment that agrees with `α` on the edges touching `L` and with `β` on the remaining edges. -/
theorem Satisfies.splice {N : Network U ι V E} {L : Set V} {x y z : ι → U} {α β : E → U}
    (hx : N.Satisfies x α) (hy : N.Satisfies y β) (hcut : EqOn α β (N.edgeCut L))
    (hzx : EqOn z x (N.readIn L)) (hzy : EqOn z y (N.readIn L)ᶜ) :
    ∃ γ, N.Satisfies z γ ∧ EqOn γ α (N.touching L) ∧ EqOn γ β (N.touching L)ᶜ := by
  classical
  refine ⟨(N.touching L).piecewise α β, fun v => ?_, piecewise_eqOn _ _ _,
    piecewise_eqOn_compl _ _ _⟩
  by_cases hv : v ∈ L
  · -- Near `L`, the spliced assignment is `α` and the input reads like `x`.
    refine N.constraint_congr v x z α _ (fun i hi => (hzx ⟨v, hv, hi⟩).symm) (fun e he => ?_)
      (hx v)
    have : e ∈ N.touching L := by rcases he with h | h <;> [left; right] <;> rw [h] <;> exact hv
    exact (piecewise_eq_of_mem _ _ _ this).symm
  · -- Away from `L`, it is `β` and the input reads like `y`; the two agree on the cut.
    have hinputs : ∀ i, N.site i = some v → y i = z i := by
      intro i hi
      refine (hzy fun hiL => ?_).symm
      obtain ⟨u, hu, hiu⟩ := hiL
      exact hv (Option.some_injective _ (hiu.symm.trans hi) ▸ hu)
    have hedges : ∀ e, N.src e = v ∨ N.tgt e = v → β e = (N.touching L).piecewise α β e := by
      intro e he
      by_cases ht : e ∈ N.touching L
      · rw [piecewise_eq_of_mem _ _ _ ht]
        refine (hcut ?_).symm
        rcases he with h | h <;> rcases ht with h' | h' <;>
          simp_all [Multigraph.mem_edgeCut]
      · exact (piecewise_eq_of_notMem _ _ _ ht).symm
    exact N.constraint_congr v y z β _ hinputs hedges (hy v)

/-- Acceptance depends only on the inputs that the network reads. -/
theorem dependsOn_read : DependsOn (· ∈ N.accepted) N.read := by
  have key : ∀ x y : ι → U, (∀ i ∈ N.read, x i = y i) → x ∈ N.accepted → y ∈ N.accepted :=
    fun x y hxy ⟨α, hα⟩ => ⟨α, fun v => N.constraint_congr v x y α α
      (fun i hi => hxy i ⟨v, mem_univ v, hi⟩) (fun _ _ => rfl) (hα v)⟩
  exact fun x y hxy => propext ⟨key x y hxy, key y x fun i hi => (hxy i hi).symm⟩

/-! ### Sweeping along a layout -/

section Sweep

variable (π : Layout V)

open Classical in
/-- The values of an assignment on the frontier at time `t`, and nothing elsewhere. -/
noncomputable def frontierValues (t : ℕ) (α : E → U) : E → Option U := fun e =>
  if e ∈ N.frontier π t then some (α e) else none

theorem frontierValues_eq_iff {t : ℕ} {α β : E → U} :
    N.frontierValues π t α = N.frontierValues π t β ↔ EqOn α β (N.frontier π t) := by
  refine ⟨fun h e he => ?_, fun h => funext fun e => ?_⟩
  · simpa [frontierValues, he] using congrFun h e
  · by_cases he : e ∈ N.frontier π t
    · simp [frontierValues, he, h he]
    · simp [frontierValues, he]

/-- The inputs revealed by time `t`: those read by the first `t` vertices, and after the last
vertex, all inputs, including those the network does not read. -/
def revealedBy (t : ℕ) : Set ι :=
  if t ≤ Nat.card V then N.readIn (π.initial t) else univ

variable {S : Set (ι → U)} {R : Type*}

/-- **Sweeping along a layout.** Fix values `val x` on the edges for every input `x`, and an
extra message `extra t x` at every time. The messages `(extra t x, val x on the frontier at
time t)` form a sweep of `S` as soon as inputs of `S` with the same messages splice, and the last
extra message is the same for all inputs of `S`. -/
noncomputable def frontierSweep (val : (ι → U) → E → U) (extra : ℕ → (ι → U) → R)
    (hlast : ∀ x ∈ S, ∀ y ∈ S, extra (Nat.card V + 1) x = extra (Nat.card V + 1) y)
    (hsplice : ∀ t ≤ Nat.card V, ∀ x ∈ S, ∀ y ∈ S, extra t x = extra t y →
      EqOn (val x) (val y) (N.frontier π t) →
      ∀ z, EqOn z x (N.readIn (π.initial t)) → EqOn z y (N.readIn (π.initial t))ᶜ → z ∈ S) :
    Sweep S (R × (E → Option U)) where
  length := Nat.card V + 1
  revealed := N.revealedBy π
  revealed_zero := by simp [revealedBy]
  revealed_length := by simp [revealedBy]
  message t x := (extra t x, N.frontierValues π t (val x))
  message_length x hx y hy := by
    rw [Prod.mk.injEq, frontierValues_eq_iff, Multigraph.frontier_of_card_le _ _ (by omega)]
    exact ⟨hlast x hx y hy, eqOn_empty _ _⟩
  splice t x hx y hy hxy z hzx hzy := by
    rw [Prod.mk.injEq, frontierValues_eq_iff] at hxy
    unfold revealedBy at hzx hzy
    split_ifs at hzx hzy with ht
    · exact hsplice t ht x hx y hy hxy.1 hxy.2 z hzx hzy
    · rwa [show z = x from funext fun i => hzx (mem_univ i)]

/-- The inputs revealed while processing the vertex numbered `t` are read at that vertex. -/
theorem revealedBy_succ_diff_subset {t : ℕ} (ht : t < Nat.card V) :
    N.revealedBy π (t + 1) \ N.revealedBy π t ⊆ N.readAt (π.symm ⟨t, ht⟩) := by
  rintro i ⟨hi, hi'⟩
  simp only [revealedBy, show t + 1 ≤ Nat.card V by omega, ht.le, ite_true] at hi hi'
  obtain ⟨u, hu, hiu⟩ := hi
  have hut : (π u : ℕ) = t := by
    by_contra hne
    exact hi' ⟨u, show (π u : ℕ) < t by have := π.mem_initial.mp hu; omega, hiu⟩
  simp only [readAt, mem_ofPred_eq, hiu, Option.some.injEq]
  exact (π.symm_apply_eq.mpr (Fin.ext hut.symm)).symm

/-- After the last vertex, the inputs revealed are those the network does not read. -/
theorem revealedBy_card_succ_diff :
    N.revealedBy π (Nat.card V + 1) \ N.revealedBy π (Nat.card V) = N.readᶜ := by
  simp [revealedBy, read, π.initial_of_card_le le_rfl, compl_eq_univ_sdiff]

variable {π} {val : (ι → U) → E → U} {extra : ℕ → (ι → U) → R}
  {hlast : ∀ x ∈ S, ∀ y ∈ S, extra (Nat.card V + 1) x = extra (Nat.card V + 1) y}
  {hsplice : ∀ t ≤ Nat.card V, ∀ x ∈ S, ∀ y ∈ S, extra t x = extra t y →
      EqOn (val x) (val y) (N.frontier π t) →
      ∀ z, EqOn z x (N.readIn (π.initial t)) → EqOn z y (N.readIn (π.initial t))ᶜ → z ∈ S}

/-- **Transitions by width.** At a step that processes a vertex, the transition is determined by
the extra messages, the values on the two frontiers, and the inputs read at the vertex. -/
theorem ncard_transition_le [Finite ι] [Finite U] [Finite E] {t : ℕ} (ht : t < Nat.card V) :
    ((N.frontierSweep π val extra hlast hsplice).transition t '' S).ncard ≤
      ((fun x => (extra t x, extra (t + 1) x)) '' S).ncard *
        Nat.card U ^ ((N.frontier π t ∪ N.frontier π (t + 1)).ncard +
          (N.readAt (π.symm ⟨t, ht⟩)).ncard) := by
  set C := N.frontier π t ∪ N.frontier π (t + 1)
  set Q := N.readAt (π.symm ⟨t, ht⟩)
  have h := (N.frontierSweep π val extra hlast hsplice).ncard_transition_le_of_factorsThrough
    (t := t) (D := (C → U) × (Q → U)) (fun x => (extra t x, extra (t + 1) x))
    (fun x => (C.domRestrict (val x), Q.domRestrict x)) fun x _ y _ h₀ hg => by
      simp only [Prod.mk.injEq, domRestrict_eq_domRestrict_iff] at h₀ hg
      simp only [Sweep.transition, frontierSweep, Prod.mk.injEq, frontierValues_eq_iff,
        domRestrict_eq_domRestrict_iff]
      exact ⟨⟨h₀.1, hg.1.mono subset_union_left⟩, ⟨h₀.2, hg.1.mono subset_union_right⟩,
        hg.2.mono (N.revealedBy_succ_diff_subset π ht)⟩
  rwa [Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    ← pow_add] at h

/-- At the last step nothing is left on the frontier, and the transition is determined by the
extra messages and the inputs that the network does not read. -/
theorem ncard_transition_last_le [Finite ι] [Finite U] :
    ((N.frontierSweep π val extra hlast hsplice).transition (Nat.card V) '' S).ncard ≤
      ((fun x => (extra (Nat.card V) x, extra (Nat.card V + 1) x)) '' S).ncard *
        Nat.card U ^ N.readᶜ.ncard := by
  have h := (N.frontierSweep π val extra hlast hsplice).ncard_transition_le_of_factorsThrough
    (t := Nat.card V) (D := ↥N.readᶜ → U)
    (fun x => (extra (Nat.card V) x, extra (Nat.card V + 1) x))
    (fun x => N.readᶜ.domRestrict x) fun x _ y _ h₀ hg => by
      simp only [Prod.mk.injEq] at h₀
      rw [domRestrict_eq_domRestrict_iff, ← N.revealedBy_card_succ_diff π] at hg
      simp only [Sweep.transition, frontierSweep, Prod.mk.injEq, frontierValues_eq_iff,
        domRestrict_eq_domRestrict_iff, Multigraph.frontier_of_card_le _ _ le_rfl,
        Multigraph.frontier_of_card_le _ _ (Nat.le_succ _), eqOn_empty, and_true]
      exact ⟨h₀.1, h₀.2, hg⟩
  rwa [Nat.card_fun, Nat.card_coe_set_eq] at h

/-! ### The sweep of a network -/

variable (π) [Nonempty U]

/-- A satisfying assignment for an accepted input, chosen once and for all. -/
noncomputable def witness (x : ι → U) : E → U :=
  Classical.epsilon (N.Satisfies x)

theorem satisfies_witness {x : ι → U} (hx : x ∈ N.accepted) : N.Satisfies x (N.witness x) :=
  Classical.epsilon_spec hx

/-- **The sweep of a network** along a layout: the messages are the values of a satisfying
assignment on the frontier, and splicing is the separator lemma. -/
noncomputable def sweep : Sweep N.accepted (Unit × (E → Option U)) :=
  N.frontierSweep π N.witness (fun _ _ => ()) (fun _ _ _ _ => rfl)
    fun _ _ _ hx _ hy _ hxy _ hzx hzy =>
      ((N.satisfies_witness hx).splice (N.satisfies_witness hy) hxy hzx hzy).imp fun _ h => h.1

/-- **The frontier counting lemma for networks.** Let the accepted inputs of a network be
`K`-rectangle-free, with at least `K` of them. If a layout has width at most `w`, every vertex
has degree at most `d` and reads at most `m` inputs, then

`|accepted| ≤ (K - 1) ^ 2 · (|V| · |U| ^ (w + d + m) + |U| ^ #(unread inputs))`. -/
theorem ncard_accepted_le [Finite ι] [Finite U] [Finite E] {K : ℕ}
    (hfree : RectangleFree N.accepted K) (hK : K ≤ N.accepted.ncard)
    {w d m : ℕ} (hw : N.width π ≤ w) (hd : N.MaxDegreeLE d)
    (hm : ∀ v, (N.readAt v).ncard ≤ m) :
    N.accepted.ncard ≤
      (K - 1) ^ 2 * (Nat.card V * Nat.card U ^ (w + d + m) + Nat.card U ^ N.readᶜ.ncard) := by
  have hq : 1 ≤ Nat.card U := Nat.card_pos
  -- The extra messages carry no information.
  have hunit : ((fun _ : ι → U => ((), ())) '' N.accepted).ncard ≤ 1 :=
    (ncard_le_one (toFinite _)).mpr fun _ _ _ _ => Subsingleton.elim _ _
  refine ((N.sweep π).ncard_le hfree hK).trans (Nat.mul_le_mul_left _ ?_)
  rw [Sweep.transitionCount, show (N.sweep π).length = Nat.card V + 1 from rfl,
    Finset.sum_range_succ]
  refine add_le_add ?_ ((N.ncard_transition_last_le).trans ?_)
  · calc ∑ t ∈ Finset.range (Nat.card V), ((N.sweep π).transition t '' N.accepted).ncard
        ≤ ∑ _t ∈ Finset.range (Nat.card V), Nat.card U ^ (w + d + m) := by
          refine Finset.sum_le_sum fun t ht => ?_
          have ht : t < Nat.card V := Finset.mem_range.mp ht
          refine (N.ncard_transition_le ht).trans ?_
          refine (Nat.mul_le_mul_right _ hunit).trans ?_
          rw [one_mul]
          refine Nat.pow_le_pow_right hq ?_
          -- Both frontiers lie in the first one and the edges at the vertex processed.
          have hC : (N.frontier π t ∪ N.frontier π (t + 1)).ncard ≤ w + d :=
            calc (N.frontier π t ∪ N.frontier π (t + 1)).ncard
                ≤ (N.frontier π t ∪ N.incidenceSet (π.symm ⟨t, ht⟩)).ncard :=
                  ncard_le_ncard
                    (union_subset subset_union_left (N.frontier_succ_subset π ht))
                    (toFinite _)
              _ ≤ (N.frontier π t).ncard + (N.incidenceSet (π.symm ⟨t, ht⟩)).ncard :=
                  ncard_union_le _ _
              _ ≤ w + d := add_le_add ((N.ncard_frontier_le_width π t).trans hw) (hd _)
          have := hm (π.symm ⟨t, ht⟩)
          omega
      _ = Nat.card V * Nat.card U ^ (w + d + m) := by simp
  · exact (Nat.mul_le_mul_right _ hunit).trans (by rw [one_mul])

end Sweep

end Network

end Cslib.Circuits.Frontier
