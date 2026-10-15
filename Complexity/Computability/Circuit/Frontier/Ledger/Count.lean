/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Computability/Circuit/Frontier/Compiler.lean`)

public import Complexity.Computability.Circuit.Frontier.Compiler
import Complexity.Computability.Circuit.Program

/-!
# Counting inside a closed set of vertices

The count of the compiler (`Cslib.Circuits.Frontier.Compiler.card_edge_add_ncard_read_le`) holds
inside every closed set of vertices `W` of the graph of a circuit, that is, every set with no
edge leaving it. The edges at `W` and the inputs read in `W` number at most `(r - 1) s` more than
the vertices of `W`, for `s` inner gates of fan-in at most `r`. So the cycle rank of `W` and the
number of inputs it reads add up to at most `(r - 1) s + 1`, when `W` has at least `|W| - 1`
edges, as a connected component does.

Inside `W`: the edges are the feed and deliver edges of the junctions in `W`; the junctions in
`W` are those of the consumers whose owner is in `W`, that is, the slots of the gates in `W` and
the outputs in `W`; and the vertices of `W` are its signals, junctions, and outputs. A circuit
with several outputs may have a disconnected graph, and this count applies to each component.

## Main results

* `Cslib.Circuits.Frontier.Compiler.readIn_network`: the inputs read in a set of vertices.
* `Cslib.Circuits.Frontier.Compiler.ncard_touching_add_ncard_readIn_le`: the count inside a
  closed set.
* `Cslib.Circuits.Frontier.Compiler.cycleRankOn_add_ncard_readIn_le`: the cycle rank of a closed
  set and the inputs it reads.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.Compiler

open Set

variable {σ : Signature} {n m : ℕ} {c : Circuit σ n m} {U : Type*} (I : Interpretation σ U)
  (Acc : Fin m → Set U)

/-- Counting along a decomposition `α ≃ β ⊕ γ`: the elements satisfying `P` are those coming
from `β` and those coming from `γ`. -/
private theorem card_subtype_eq_add {α β γ : Type*} [Finite β] [Finite γ] (e : α ≃ β ⊕ γ)
    (P : α → Prop) :
    Nat.card {a // P a} =
      Nat.card {b // P (e.symm (.inl b))} + Nat.card {c // P (e.symm (.inr c))} := by
  rw [← Nat.card_sum]
  exact Nat.card_congr
    ((e.subtypeEquiv (q := fun x => P (e.symm x)) fun a => by rw [e.symm_apply_apply]).trans
      Equiv.subtypeSum)

/-- The vertices of `W` are its signals, its junctions, and its outputs. -/
private theorem ncard_eq_add (W : Set (Vertex c)) :
    W.ncard = Nat.card {w // Vertex.signal w ∈ W} + Nat.card {j // Vertex.junction j ∈ W} +
      Nat.card {o // Vertex.output o ∈ W} := by
  rw [← Nat.card_coe_set_eq, add_assoc]
  exact (card_subtype_eq_add Vertex.equiv _).trans
    (congrArg _ (card_subtype_eq_add (Equiv.refl _) _))

/-- The edges at a closed set `W` are the feed and deliver edges of the junctions in `W`. -/
private theorem ncard_touching_eq {W : Set (Vertex c)} (hW : (graph c).edgeCut W = ∅) :
    ((graph c).touching W).ncard = 2 * Nat.card {j // Vertex.junction j ∈ W} := by
  have hW := (graph c).edgeCut_eq_empty_iff.1 hW
  rw [← Nat.card_coe_set_eq, card_subtype_eq_add Edge.equiv, two_mul]
  congr 1 <;> refine Nat.card_congr (Equiv.subtypeEquivRight fun j => ?_)
  · -- The feed edge of `j` ends at `j`.
    exact or_iff_right_of_imp (hW (.feed j)).1
  · -- The deliver edge of `j` starts at `j`.
    exact or_iff_left_of_imp (hW (.deliver j)).2

/-- The junctions in a closed set `W` are those of the consumers whose owner is in `W`: the
slots of the gates in `W` and the outputs in `W`. -/
private theorem card_junction_eq {W : Set (Vertex c)} (hW : (graph c).edgeCut W = ∅) :
    Nat.card {j // Vertex.junction j ∈ W} =
      Nat.card {t : Slot c // owner (.inl t) ∈ W} + Nat.card {o // Vertex.output o ∈ W} := by
  -- The deliver edge of a junction joins it to the owner of its consumer.
  have hJ (j : Junction c) : Vertex.junction j ∈ W ↔ owner (junctionEquiv c j) ∈ W :=
    (graph c).edgeCut_eq_empty_iff.1 hW (.deliver j)
  rw [Nat.card_congr ((junctionEquiv c).subtypeEquiv (q := fun t => owner t ∈ W) hJ)]
  exact card_subtype_eq_add (Equiv.refl _) _

variable (c) in
/-- The reachable inner gates whose vertex lies in `W`. -/
abbrev InnerGateIn (W : Set (Vertex c)) : Type :=
  {g : InnerGate c // Vertex.signal ⟨.gate g.1, g.2.1⟩ ∈ W}

/-- There are at most `r` slots per reachable inner gate in `W`. -/
private theorem card_slot_mem_le {r : ℕ} (hfan : c.FanInAtMost r) (W : Set (Vertex c)) :
    Nat.card {t : Slot c // owner (.inl t) ∈ W} ≤ r * Nat.card (InnerGateIn c W) := by
  calc Nat.card {t : Slot c // owner (.inl t) ∈ W}
      ≤ Nat.card (InnerGateIn c W × Fin r) := by
        refine Nat.card_le_card_of_injective
          (fun t => (⟨⟨t.1.1.1, t.1.2, Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt t.1.1.2.isLt)⟩,
            t.2⟩, ⟨t.1.1.2.val,
              t.1.1.2.isLt.trans_le (Program.fanInAtMost_iff.mp hfan t.1.1.1)⟩)) ?_
        rintro ⟨⟨⟨g, a⟩, hg⟩, hgW⟩ ⟨⟨⟨g', a'⟩, hg'⟩, hgW'⟩ h
        obtain rfl : g = g' := congrArg (fun x => x.1.1.1) h
        obtain rfl : a = a' := Fin.ext (congrArg (fun x => x.2.val) h)
        rfl
    _ = r * Nat.card (InnerGateIn c W) := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin, mul_comm]

/-- The inputs read in a set of vertices are the reachable inputs whose vertex lies in it. -/
theorem readIn_network (W : Set (Vertex c)) :
    (network c I Acc).readIn W = {i | ∃ hi : Reach c (.input i), .signal ⟨.input i, hi⟩ ∈ W} := by
  ext i
  constructor
  · rintro ⟨v, hv, hi⟩
    obtain ⟨hr, rfl⟩ := site_eq_some hi
    exact ⟨hr, hv⟩
  · rintro ⟨hi, hv⟩
    exact ⟨_, hv, site_of_reach hi⟩

/-- The signals in `W` include the inputs read in `W` and the reachable inner gates in `W`. -/
private theorem ncard_readIn_add_card_le (W : Set (Vertex c)) :
    ((network c I Acc).readIn W).ncard + Nat.card (InnerGateIn c W) ≤
      Nat.card {w // Vertex.signal w ∈ W} := by
  have hread : ((network c I Acc).readIn W).ncard =
      Nat.card {i : {i // Reach c (.input i)} // Vertex.signal ⟨.input i.1, i.2⟩ ∈ W} := by
    rw [readIn_network, ← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeExists _
      fun i : {i // Reach c (.input i)} => Vertex.signal ⟨.input i.1, i.2⟩ ∈ W).symm
  rw [card_subtype_eq_add signalEquiv, hread]
  refine Nat.add_le_add le_rfl ?_
  exact Nat.card_le_card_of_injective (fun g => ⟨⟨g.1.1, g.1.2.1⟩, g.2⟩) fun _ _ h =>
    Subtype.ext (Subtype.ext (congrArg (fun g => g.1.1) h))

/-- **The local count inside a closed set.** For fan-in at most `r`, the edges at a closed set
of vertices `W` and the inputs read in `W` number at most `(r - 1) s_W` more than the vertices
of `W`, where `s_W` counts the reachable inner gates in `W`. -/
theorem ncard_touching_add_ncard_readIn_le_local {r : ℕ} (hfan : c.FanInAtMost r)
    {W : Set (Vertex c)} (hW : (graph c).edgeCut W = ∅) :
    ((graph c).touching W).ncard + ((network c I Acc).readIn W).ncard ≤
      W.ncard + (r - 1) * Nat.card (InnerGateIn c W) := by
  have hE := ncard_touching_eq hW
  have hJ := card_junction_eq hW
  have hV := ncard_eq_add W
  have hslot := card_slot_mem_le hfan W
  have hsig := ncard_readIn_add_card_le I Acc W
  have hr : r * Nat.card (InnerGateIn c W) ≤
      (r - 1) * Nat.card (InnerGateIn c W) + Nat.card (InnerGateIn c W) := by
    rcases r with _ | r
    · simp
    · simp [add_mul]
  omega

/-- **The count inside a closed set.** For fan-in at most `r`, the edges at a closed set of
vertices `W` and the inputs read in `W` number at most `(r - 1) s` more than the vertices of `W`,
where `s` counts the inner gates. -/
theorem ncard_touching_add_ncard_readIn_le {r : ℕ} (hfan : c.FanInAtMost r)
    {W : Set (Vertex c)} (hW : (graph c).edgeCut W = ∅) :
    ((graph c).touching W).ncard + ((network c I Acc).readIn W).ncard ≤
      W.ncard + (r - 1) * c.innerSize := by
  have hG : Nat.card (InnerGateIn c W) ≤ c.innerSize :=
    (Finite.card_subtype_le _).trans card_innerGate_le
  exact (ncard_touching_add_ncard_readIn_le_local I Acc hfan hW).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hG) _)

/-- **The cycle rank of a closed set.** For fan-in at most `r`, the cycle rank of a closed set of
vertices `W` with at least `|W| - 1` edges, for instance a connected component, and the number of
inputs read in `W` add up to at most `(r - 1) s + 1`, where `s` counts the inner gates. -/
theorem cycleRankOn_add_ncard_readIn_le {r : ℕ} (hfan : c.FanInAtMost r)
    {W : Set (Vertex c)} (hW : (graph c).edgeCut W = ∅)
    (hconn : W.ncard ≤ ((graph c).touching W).ncard + 1) :
    (graph c).cycleRankOn W + ((network c I Acc).readIn W).ncard ≤ (r - 1) * c.innerSize + 1 := by
  have := ncard_touching_add_ncard_readIn_le I Acc hfan hW
  unfold Multigraph.cycleRankOn
  omega

end Cslib.Circuits.Frontier.Compiler
