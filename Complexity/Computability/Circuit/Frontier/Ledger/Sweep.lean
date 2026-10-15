/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Compiler
public import Complexity.Computability.Circuit.Frontier.Ledger.Basic
import Complexity.Foundations.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Sweeping a program with a ledger

Let the special gates of a program `p` have a ledger in `M`, and let `p` accept the inputs whose
value at a wire `o` lies in a set `Acc`. Erase the special gates. A wire is *live*
(`Frontier.Live`) if it is an input or an ordinary gate of positive arity; the others are
constants, among them the placeholders. The *live circuit* (`Frontier.liveCircuit`) is the erased
program with every live wire as an output. For a guess `m ∈ M`, the constraint network of the
live circuit accepting every value (`Frontier.Ledger.network`) is satisfied exactly by the run
with guess `m`; its graph and its sites do not depend on `m`.

**The ledger sweep** (`Frontier.Ledger.sweep`) is the sweep along a layout
(`Frontier.Network.frontierSweep`) whose extra message has two parts: the product `m` of the
contributions of the true run (its consistent guess) and the product of the contributions of the
wires whose vertices come first (the *ledger so far*). Two inputs with the same message can be
spliced (`Frontier.Ledger.mem_of_splice`): the network with guess `m` splices their runs (the
separator lemma); the two parts of the ledger multiply back to `m`, because the constant wires
contribute the same for every input; and a consistent guess yields the true run.

**Transitions.** The extra messages take at most `|M| ^ 3` pairs of values at each step
(`Frontier.Ledger.ncard_extra_le`). Inside a closed set of vertices `W`, the values of the run on
the edges at `W` depend only on the guess and the inputs read in `W`
(`Frontier.Ledger.run_eq_of_eqOn_readIn`), so the transitions inside `W` are bounded by the
inputs that `W` reads, however wide the layout is there. Along a layout of the components one
after another, some step therefore bounds the accepted set both by its width and by the inputs of
its component (`Frontier.Ledger.exists_ncard_le`).

## Main definitions

* `Cslib.Circuits.Frontier.Live`: the live wires of a program with erased special gates.
* `Cslib.Circuits.Frontier.liveCircuit`: the erased program with every live wire as an output.
* `Cslib.Circuits.Frontier.Ledger.network`: its constraint network on a guess.
* `Cslib.Circuits.Frontier.Ledger.sweep`: the sweep of a program with a ledger.

## Main results

* `Cslib.Circuits.Frontier.Ledger.mem_of_splice`: splicing two inputs with the same message.
* `Cslib.Circuits.Frontier.Ledger.run_eq_of_eqOn_readIn`: locality inside a closed set.
* `Cslib.Circuits.Frontier.Ledger.ncard_transition_le_width`,
  `Cslib.Circuits.Frontier.Ledger.ncard_transition_le_readIn`: transitions by width and by the
  inputs read in a closed set.
* `Cslib.Circuits.Frontier.Ledger.exists_ncard_le`: counting along a layout of the components.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

universe v

variable {σ : Signature.{v}} {n s : ℕ} {U : Type*}

/-! ### The live circuit -/

variable (p : Program σ n s) (special : ℕ → Prop)

/-- A wire is *live*, once the special gates of `p` are erased, when it is an input or an
ordinary gate of positive arity. The other wires are constants of the erased program: the
placeholders of the special gates and the gates of arity zero. -/
def Live : Wire n s → Prop
  | .input _ => True
  | .gate g => ¬special g ∧ σ.Arity (p.lines g).op ≠ 0

variable [DecidablePred special]

/-- The *live circuit*: the program `p` with its special gates erased, and with every live wire
as an output. -/
noncomputable def liveCircuit :
    Circuit (guessSignature σ) n (Nat.card {w // Live p special w}) where
  program := erase special p
  outputs i := ((Finite.equivFin {w // Live p special w}).symm i).1

variable {p special}

/-- The live wires are signals of the live circuit. -/
theorem reach_of_live {w : Wire n s} (hw : Live p special w) :
    Compiler.Reach (liveCircuit p special) w := by
  have h := Compiler.Reach.output (c := liveCircuit p special)
    (Finite.equivFin {w // Live p special w} ⟨w, hw⟩)
  simpa [liveCircuit] using h

/-- The inputs are signals of the live circuit. -/
theorem reach_input (i : Fin n) : Compiler.Reach (liveCircuit p special) (.input i) :=
  reach_of_live trivial

/-- The inner gates of the live circuit are the ordinary inner gates. -/
theorem innerSize_liveCircuit :
    (liveCircuit p special).innerSize = (p.innerGates.filter fun g : Fin s => ¬special g).card := by
  rw [Circuit.innerSize, ← innerGates_erase]
  rfl

/-- There are at most `n + s'` live wires, where `s'` counts the ordinary inner gates. -/
theorem card_live_le :
    Nat.card {w // Live p special w} ≤ n + (liveCircuit p special).innerSize := by
  rw [innerSize_liveCircuit, ← Nat.card_eq_finsetCard]
  calc Nat.card {w // Live p special w}
      ≤ Nat.card (Fin n ⊕ ↥(p.innerGates.filter fun g : Fin s => ¬special g)) := by
        refine Nat.card_le_card_of_injective (fun w => match w with
          | ⟨.input i, _⟩ => .inl i
          | ⟨.gate g, h⟩ => .inr ⟨g, Finset.mem_filter.2 ⟨Program.mem_innerGates.2 h.2, h.1⟩⟩) ?_
        rintro ⟨w | w, hw⟩ ⟨w' | w', hw'⟩ h <;> simp_all
    _ = n + Nat.card ↥(p.innerGates.filter fun g : Fin s => ¬special g) := by
        rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]

/-- The live circuit reads every input. -/
theorem read_network_liveCircuit (J : Interpretation (guessSignature σ) U)
    (Acc : Fin (Nat.card {w // Live p special w}) → Set U) :
    (Compiler.network (liveCircuit p special) J Acc).read = univ := by
  rw [Compiler.read_network]
  exact eq_univ_of_forall reach_input

/-- When there are inputs, the graph of the live circuit has a vertex. -/
theorem card_vertex_liveCircuit_pos (hn : 0 < n) :
    0 < Nat.card (Compiler.Vertex (liveCircuit p special)) :=
  have : Nonempty (Compiler.Vertex (liveCircuit p special)) :=
    ⟨.signal ⟨.input ⟨0, hn⟩, reach_input _⟩⟩
  Nat.card_pos

/-- The wires whose vertices lie in `P`. -/
def wiresIn (P : Set (Compiler.Vertex (liveCircuit p special))) : Set (Wire n s) :=
  {w | ∃ hw, (.signal ⟨w, hw⟩ : Compiler.Vertex (liveCircuit p special)) ∈ P}

namespace Ledger

variable {I : Interpretation σ U} {M : Type*} [CommMonoid M] (L : Ledger special p I M)

/-- The constraint network of the live circuit on the guess `m`, accepting every value. Its
satisfying assignments are the runs with guess `m`. Its graph is `Compiler.graph` of the live
circuit and its sites are those of the live circuit, whatever the guess. -/
noncomputable abbrev network (m : M) :
    Network U (Fin n) (Compiler.Vertex (liveCircuit p special))
      (Compiler.Edge (liveCircuit p special)) :=
  Compiler.network (liveCircuit p special) (guessInterpretation I (L.readout m)) fun _ => univ

/-- The run with guess `m` satisfies the network on the guess `m`. -/
theorem satisfies_network (m : M) (x : Fin n → U) :
    (L.network m).Satisfies x fun e => L.run m x e.signal.1 :=
  Compiler.satisfies_trace fun _ => mem_univ _

/-- A satisfying assignment of the network on the guess `m` is the run with guess `m`. -/
theorem eq_run_of_satisfies {m : M} {x : Fin n → U} {α : Compiler.Edge (liveCircuit p special) → U}
    (h : (L.network m).Satisfies x α) (e : Compiler.Edge (liveCircuit p special)) :
    α e = L.run m x e.signal.1 :=
  Compiler.eq_trace h e

/-- A wire that is not a signal of the live circuit is a constant of the erased program, so its
value in a run depends only on the guess. -/
theorem run_eq_of_not_reach (m : M) {w : Wire n s}
    (hw : ¬Compiler.Reach (liveCircuit p special) w) (x y : Fin n → U) :
    L.run m x w = L.run m y w := by
  have hlive : ¬Live p special w := fun h => hw (reach_of_live h)
  cases w with
  | input i => exact absurd trivial hlive
  | gate g =>
    rw [run_gate, run_gate]
    by_cases hs : special g
    · simp only [hs, ↓reduceIte]
    · have h0 : σ.Arity (p.lines g).op = 0 := by
        by_contra h
        exact hlive ⟨hs, h⟩
      simp only [hs, ↓reduceIte]
      congr 1
      funext a
      have := a.isLt
      omega

/-! ### Splicing -/

/-- **Splicing two inputs with the same message.** Let `x` and `y` be inputs whose value at the
wire `o` lies in `Acc`. If their runs have the same consistent guess, the same ledger on the
wires of a set of vertices `P`, and the same values on the edge cut of `P`, then every input `z`
that reads like `x` at `P` and like `y` elsewhere has its value at `o` in `Acc` as well. -/
theorem mem_of_splice {o : Wire n s} {Acc : Set U}
    {P : Set (Compiler.Vertex (liveCircuit p special))} {x y z : Fin n → U}
    (hx : p.trace I x o ∈ Acc) (hy : p.trace I y o ∈ Acc)
    (hm : L.total (p.trace I x) = L.total (p.trace I y))
    (hpart : L.ledgerOn (wiresIn P) (p.trace I x) = L.ledgerOn (wiresIn P) (p.trace I y))
    (hcut : EqOn (fun e => p.trace I x e.signal.1) (fun e => p.trace I y e.signal.1)
      ((Compiler.graph (liveCircuit p special)).edgeCut P))
    (hzx : EqOn z x ((L.network 1).readIn P)) (hzy : EqOn z y ((L.network 1).readIn P)ᶜ) :
    p.trace I z o ∈ Acc := by
  have hαx := L.satisfies_network (L.total (p.trace I x)) x
  rw [L.run_total_trace, hm] at hαx
  have hαy := L.satisfies_network (L.total (p.trace I y)) y
  rw [L.run_total_trace] at hαy
  generalize hmdef : L.total (p.trace I y) = m at hαx hαy
  obtain ⟨γ, hγ, hγx, hγy⟩ := hαx.splice hαy hcut hzx hzy
  -- The run of `z` with the guess `m` agrees with `x` on the wires of `P` and with `y` on the
  -- other wires.
  have hwire (w : Wire n s) : (w ∈ wiresIn P → L.run m z w = p.trace I x w) ∧
      (w ∉ wiresIn P → L.run m z w = p.trace I y w) := by
    by_cases hreach : Compiler.Reach (liveCircuit p special) w
    · rw [← show γ (Compiler.head ⟨w, hreach⟩) = L.run m z w from L.eq_run_of_satisfies hγ _]
      refine ⟨fun ⟨_, hw⟩ => hγx (Or.inl hw), fun hw => ?_⟩
      have hw' : (.signal ⟨w, hreach⟩ : Compiler.Vertex (liveCircuit p special)) ∉ P :=
        fun h => hw ⟨hreach, h⟩
      by_cases ht : Compiler.head ⟨w, hreach⟩ ∈ (L.network m).touching P
      · rw [hγx ht]
        refine hcut ?_
        rcases ht with ht | ht
        · exact absurd ht hw'
        · exact fun h => hw' (h.mpr ht)
      · exact hγy ht
    · refine ⟨fun ⟨h, _⟩ => absurd h hreach, fun _ => ?_⟩
      rw [L.run_eq_of_not_reach m hreach z y, ← hmdef, L.run_total_trace]
  -- The ledger of the run of `z` is `m`, so the guess is consistent.
  have htotal : L.total (L.run m z) = m := by
    rw [L.total_eq_mul (wiresIn P)]
    conv_rhs => rw [← hmdef, L.total_eq_mul (wiresIn P) (p.trace I y)]
    congr 1
    · rw [← hpart, ledgerOn, ledgerOn]
      exact Finset.prod_congr rfl fun w hw => by rw [(hwire w).1 (by simpa using hw)]
    · rw [ledgerOn, ledgerOn]
      exact Finset.prod_congr rfl fun w hw => by rw [(hwire w).2 (by simpa using hw)]
  rw [← L.run_eq_trace htotal]
  by_cases ho : o ∈ wiresIn P
  · rw [(hwire o).1 ho]
    exact hx
  · rw [(hwire o).2 ho]
    exact hy

/-- **Locality inside a closed set.** For a fixed guess, the values of the run on the edges at a
closed set of vertices `W` depend only on the inputs read in `W`. -/
theorem run_eq_of_eqOn_readIn (m : M) {W : Set (Compiler.Vertex (liveCircuit p special))}
    (hW : (Compiler.graph (liveCircuit p special)).edgeCut W = ∅) {x x' : Fin n → U}
    (hxx' : EqOn x x' ((L.network 1).readIn W)) {e : Compiler.Edge (liveCircuit p special)}
    (he : e ∈ (Compiler.graph (liveCircuit p special)).touching W) :
    L.run m x e.signal.1 = L.run m x' e.signal.1 := by
  have hW' : (L.network m).edgeCut W = ∅ := hW
  obtain ⟨γ, hγ, hγx, -⟩ := (L.satisfies_network m x).splice (L.satisfies_network m x')
    (by rw [hW']; exact eqOn_empty _ _) hxx'.symm (eqOn_refl _ _)
  rw [← L.eq_run_of_satisfies hγ e]
  exact (hγx he).symm

/-! ### The sweep -/

section Sweep

variable (o : Wire n s) (Acc : Set U) (π : Layout (Compiler.Vertex (liveCircuit p special)))

/-- The extra message at time `t`: the consistent guess and the ledger of the first `t`
vertices. After the last vertex it is trivial. -/
noncomputable def extra (t : ℕ) (x : Fin n → U) : M × M :=
  if t ≤ Nat.card (Compiler.Vertex (liveCircuit p special)) then
    (L.total (p.trace I x), L.ledgerOn (wiresIn (π.initial t)) (p.trace I x))
  else (1, 1)

/-- **The sweep of a program with a ledger**, along a layout of the graph of its live circuit:
the frontier sweep of the values of the run, whose extra message is the guess and the ledger so
far. -/
noncomputable def sweep : Sweep {x | p.trace I x o ∈ Acc}
    ((M × M) × (Compiler.Edge (liveCircuit p special) → Option U)) :=
  (L.network 1).frontierSweep π (fun x e => p.trace I x e.signal.1) (L.extra π)
    (fun _ _ _ _ => by simp [extra])
    fun t ht x hx y hy hxy hval z hzx hzy => by
      simp only [extra, ht, ↓reduceIte, Prod.mk.injEq] at hxy
      exact L.mem_of_splice hx hy hxy.1 hxy.2 hval hzx hzy

variable {o Acc}

/-- The extra messages take at most `|M| ^ 3` pairs of values at each step. -/
theorem ncard_extra_le [Finite U] [Finite M] (t : ℕ) :
    ((fun x => (L.extra π t x, L.extra π (t + 1) x)) '' {x | p.trace I x o ∈ Acc}).ncard ≤
      Nat.card M ^ 3 := by
  calc _ ≤ ((fun x => (L.total (p.trace I x),
        L.ledgerOn (wiresIn (π.initial t)) (p.trace I x),
        L.ledgerOn (wiresIn (π.initial (t + 1))) (p.trace I x))) ''
          {x | p.trace I x o ∈ Acc}).ncard := by
        refine ncard_image_le_ncard_image_of_factorsThrough (toFinite _) fun x _ y _ hxy => ?_
        simp only [Prod.mk.injEq] at hxy
        simp only [extra, hxy.1, hxy.2.1, hxy.2.2]
    _ ≤ Nat.card (M × M × M) := ncard_le_card _
    _ = Nat.card M ^ 3 := by simp only [Nat.card_prod]; ring

/-- **Transitions by width.** A transition is determined by the guess, the two ledgers, the
values on the two frontiers, and the input read at the vertex processed. -/
theorem ncard_transition_le_width [Finite U] [Finite M] {t : ℕ}
    (ht : t < Nat.card (Compiler.Vertex (liveCircuit p special))) :
    ((L.sweep o Acc π).transition t '' {x | p.trace I x o ∈ Acc}).ncard ≤
      Nat.card M ^ 3 * Nat.card U ^ (((L.network 1).frontier π t ∪
        (L.network 1).frontier π (t + 1)).ncard + ((L.network 1).readAt (π.symm ⟨t, ht⟩)).ncard) :=
  ((L.network 1).ncard_transition_le ht).trans (Nat.mul_le_mul_right _ (L.ncard_extra_le π t))

/-- **Transitions inside a closed set.** If the vertex processed at step `t` lies in a closed
set `W` whose edges contain both frontiers of the step, a transition is determined by the guess,
the two ledgers, and the inputs read in `W`. -/
theorem ncard_transition_le_readIn [Finite U] [Finite M] {t : ℕ}
    (ht : t < Nat.card (Compiler.Vertex (liveCircuit p special)))
    {W : Set (Compiler.Vertex (liveCircuit p special))}
    (hW : (Compiler.graph (liveCircuit p special)).edgeCut W = ∅) (hv : π.symm ⟨t, ht⟩ ∈ W)
    (hC : (L.network 1).frontier π t ∪ (L.network 1).frontier π (t + 1) ⊆
      (L.network 1).touching W) :
    ((L.sweep o Acc π).transition t '' {x | p.trace I x o ∈ Acc}).ncard ≤
      Nat.card M ^ 3 * Nat.card U ^ ((L.network 1).readIn W).ncard := by
  set Q := (L.network 1).readIn W
  have h := (L.sweep o Acc π).ncard_transition_le_of_factorsThrough (t := t) (D := Q → U)
    (fun x => (L.extra π t x, L.extra π (t + 1) x)) (fun x => Q.domRestrict x)
    fun x _ y _ h₀ hg => by
      rw [domRestrict_eq_domRestrict_iff] at hg
      simp only [Prod.mk.injEq] at h₀
      have hm : L.total (p.trace I x) = L.total (p.trace I y) := by
        have := h₀.1
        simp only [extra, ht.le, ↓reduceIte, Prod.mk.injEq] at this
        exact this.1
      -- The values on the edges at `W` depend only on the guess and the inputs read in `W`.
      have hval : EqOn (fun e => p.trace I x e.signal.1) (fun e => p.trace I y e.signal.1)
          ((L.network 1).touching W) := fun e he => by
        change p.trace I x e.signal.1 = p.trace I y e.signal.1
        rw [← L.run_total_trace x, ← L.run_total_trace y, ← hm]
        exact L.run_eq_of_eqOn_readIn _ hW hg he
      simp only [Sweep.transition, sweep, Network.frontierSweep, Prod.mk.injEq,
        Network.frontierValues_eq_iff, domRestrict_eq_domRestrict_iff]
      refine ⟨⟨h₀.1, hval.mono (subset_union_left.trans hC)⟩,
        ⟨h₀.2, hval.mono (subset_union_right.trans hC)⟩, fun i hi => hg ?_⟩
      exact ⟨_, hv, (L.network 1).revealedBy_succ_diff_subset π ht hi⟩
  refine h.trans (Nat.mul_le_mul (L.ncard_extra_le π t) ?_)
  rw [Nat.card_fun, Nat.card_coe_set_eq]

/-- At the last step the transition is determined by the guess and the two ledgers, since every
input is read. -/
theorem ncard_transition_last_le [Finite U] [Finite M] :
    ((L.sweep o Acc π).transition (Nat.card (Compiler.Vertex (liveCircuit p special))) ''
      {x | p.trace I x o ∈ Acc}).ncard ≤ Nat.card M ^ 3 := by
  have h : ((L.sweep o Acc π).transition (Nat.card (Compiler.Vertex (liveCircuit p special))) ''
      {x | p.trace I x o ∈ Acc}).ncard ≤
      ((fun x => (L.extra π (Nat.card (Compiler.Vertex (liveCircuit p special))) x,
        L.extra π (Nat.card (Compiler.Vertex (liveCircuit p special)) + 1) x)) ''
          {x | p.trace I x o ∈ Acc}).ncard * Nat.card U ^ (L.network 1).readᶜ.ncard :=
    (L.network 1).ncard_transition_last_le
  replace h := h.trans (Nat.mul_le_mul_right _ (L.ncard_extra_le π _))
  rwa [read_network_liveCircuit, compl_univ, ncard_empty, pow_zero, mul_one] at h

/-- **Counting along a layout of the components.** Suppose that, at each step of a layout, the
frontiers lie among the edges of the component of the vertex processed. Then some step `t`
bounds the set accepted by `p` by `(K - 1) ^ 2 (|V| + 1) |M| ^ 3 q ^ e`, where `q = |U|` and the
exponent `e` is the smaller of the width of the step (the two frontiers and the input read) and
the number of inputs read in the component of the vertex processed. -/
theorem exists_ncard_le [Finite U] [Nonempty U] [Finite M] {K : ℕ}
    (hfree : RectangleFree {x | p.trace I x o ∈ Acc} K)
    (hK : K ≤ {x | p.trace I x o ∈ Acc}.ncard)
    (hV : 0 < Nat.card (Compiler.Vertex (liveCircuit p special)))
    (hC : ∀ t (ht : t < Nat.card (Compiler.Vertex (liveCircuit p special))),
      (L.network 1).frontier π t ∪ (L.network 1).frontier π (t + 1) ⊆
        (L.network 1).touching ((L.network 1).component (π.symm ⟨t, ht⟩))) :
    ∃ t, ∃ ht : t < Nat.card (Compiler.Vertex (liveCircuit p special)),
      {x | p.trace I x o ∈ Acc}.ncard ≤
        (K - 1) ^ 2 * (Nat.card (Compiler.Vertex (liveCircuit p special)) + 1) *
          Nat.card M ^ 3 * Nat.card U ^ min (((L.network 1).frontier π t ∪
            (L.network 1).frontier π (t + 1)).ncard +
              ((L.network 1).readAt (π.symm ⟨t, ht⟩)).ncard)
            ((L.network 1).readIn ((L.network 1).component (π.symm ⟨t, ht⟩))).ncard := by
  set S := {x | p.trace I x o ∈ Acc}
  set N := Nat.card (Compiler.Vertex (liveCircuit p special))
  have hq : 1 ≤ Nat.card U := Nat.card_pos
  -- The exponent at each step: the smaller of its width and the inputs of its component.
  let f : ℕ → ℕ := fun t => if ht : t < N then
    min (((L.network 1).frontier π t ∪ (L.network 1).frontier π (t + 1)).ncard +
      ((L.network 1).readAt (π.symm ⟨t, ht⟩)).ncard)
      ((L.network 1).readIn ((L.network 1).component (π.symm ⟨t, ht⟩))).ncard else 0
  obtain ⟨t, htmem, hmax⟩ := Finset.exists_max_image (Finset.range N) f
    ⟨0, Finset.mem_range.mpr hV⟩
  have ht : t < N := Finset.mem_range.mp htmem
  refine ⟨t, ht, ?_⟩
  have hstep : ∀ t' ∈ Finset.range (N + 1),
      ((L.sweep o Acc π).transition t' '' S).ncard ≤ Nat.card M ^ 3 * Nat.card U ^ f t := by
    intro t' ht'mem
    rcases Nat.lt_or_ge t' N with ht' | ht'
    · calc ((L.sweep o Acc π).transition t' '' S).ncard
          ≤ Nat.card M ^ 3 * Nat.card U ^ f t' := by
            simp only [f, ht', ↓reduceDIte]
            rcases min_cases (((L.network 1).frontier π t' ∪
                (L.network 1).frontier π (t' + 1)).ncard +
                ((L.network 1).readAt (π.symm ⟨t', ht'⟩)).ncard)
              ((L.network 1).readIn ((L.network 1).component (π.symm ⟨t', ht'⟩))).ncard with
              ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
            · exact L.ncard_transition_le_width π ht'
            · exact L.ncard_transition_le_readIn π ht'
                ((L.network 1).edgeCut_component _) ((L.network 1).mem_component_self _)
                (hC t' ht')
        _ ≤ Nat.card M ^ 3 * Nat.card U ^ f t :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq (hmax t' (Finset.mem_range.mpr ht')))
    · obtain rfl : t' = N := by have := Finset.mem_range.mp ht'mem; omega
      exact (L.ncard_transition_last_le π).trans
        (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _))
  have hft : f t = min (((L.network 1).frontier π t ∪
      (L.network 1).frontier π (t + 1)).ncard + ((L.network 1).readAt (π.symm ⟨t, ht⟩)).ncard)
      ((L.network 1).readIn ((L.network 1).component (π.symm ⟨t, ht⟩))).ncard := by
    simp only [f, ht, ↓reduceDIte]
  calc S.ncard ≤ (K - 1) ^ 2 * ∑ t ∈ Finset.range (N + 1),
        ((L.sweep o Acc π).transition t '' S).ncard := (L.sweep o Acc π).ncard_le hfree hK
    _ ≤ (K - 1) ^ 2 * ((N + 1) * (Nat.card M ^ 3 * Nat.card U ^ f t)) := by
        gcongr
        simpa using Finset.sum_le_card_nsmul (Finset.range (N + 1)) _ _ hstep
    _ = _ := by rw [← hft]; ring

end Sweep

end Ledger

end Cslib.Circuits.Frontier
