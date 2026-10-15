/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Computability/Circuit/Frontier/Compiler.lean`)

public import Complexity.Computability.Circuit.Frontier.Compiler

/-!
# Outputs across a cut

A circuit with many outputs computes a function; its network (`Cslib.Circuits.Frontier.Compiler`)
accepts every value at every output. Cut the vertices of the network into a set `P` and its
complement. If the runs of the circuit on two inputs `x` and `y` agree on the edge cut of `P`,
then the separator lemma splices them: on any input `z` that reads like `x` at `P` and like `y`
elsewhere, the outputs held in `P` are those of `x` and the other outputs are those of `y`
(`Compiler.eval_splice`).

Two consequences for the shape of the graph. Cutting along the connected component of an output
vertex, which has an empty edge cut, shows that an output that depends on an input is joined to
the vertex of that input (`Compiler.exists_reachable_of_eval_ne`); in particular the input is
read by the network. And the graph is connected as soon as one vertex is joined to every output
vertex (`Compiler.connected_of_reachable`). For a circuit with one output this is
`Compiler.connected`.

## Main results

* `Cslib.Circuits.Frontier.Compiler.eval_splice`: outputs across a cut.
* `Cslib.Circuits.Frontier.Compiler.exists_reachable_of_eval_ne`: an output depending on an
  input is joined to its vertex.
* `Cslib.Circuits.Frontier.Compiler.connected_of_reachable`: connectivity from a common vertex.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.Compiler

open Set

variable {σ : Signature} {n m : ℕ} {c : Circuit σ n m} {U : Type*} {I : Interpretation σ U}

/-- **Outputs across a cut.** In the network of a circuit computing a function, let the runs on
two inputs `x` and `y` agree on the edge cut of a set of vertices `P`, and let `z` read like `x`
at `P` and like `y` elsewhere. Then the outputs of `z` are those of `x` at the output vertices in
`P`, and those of `y` at the others. -/
theorem eval_splice {P : Set (Vertex c)} {x y z : Fin n → U}
    (hcut : ∀ e ∈ (graph c).edgeCut P,
      c.program.trace I x e.signal.1 = c.program.trace I y e.signal.1)
    (hzx : EqOn z x ((network c I fun _ => univ).readIn P))
    (hzy : EqOn z y ((network c I fun _ => univ).readIn P)ᶜ) (o : Fin m) :
    (Vertex.output o ∈ P → c.eval I z o = c.eval I x o) ∧
      (Vertex.output o ∉ P → c.eval I z o = c.eval I y o) := by
  have hx : (network c I fun _ => univ).Satisfies x fun e => c.program.trace I x e.signal.1 :=
    satisfies_trace fun _ => mem_univ _
  have hy : (network c I fun _ => univ).Satisfies y fun e => c.program.trace I y e.signal.1 :=
    satisfies_trace fun _ => mem_univ _
  obtain ⟨γ, hγ, hγx, hγy⟩ := hx.splice hy hcut hzx hzy
  -- Every value at the output `o` is read off the edge delivering it.
  have hval : ∀ v, c.program.trace I v (outEdge c o).signal.1 = c.eval I v o := fun v => by
    rw [signal_deliverEdge]
    rfl
  have htgt : (network c I fun _ => univ).tgt (outEdge c o) = .output o := tgt_deliverEdge _
  rw [← hval z, ← eq_trace hγ, ← hval x, ← hval y]
  refine ⟨fun ho => hγx (Or.inr (htgt ▸ ho)), fun ho => ?_⟩
  by_cases ht : outEdge c o ∈ (network c I fun _ => univ).touching P
  · -- The edge reaches into `P` from outside, so it lies on the cut.
    have hsrc : src (outEdge c o) ∈ P := ht.resolve_right fun h => ho (htgt ▸ h)
    refine (hγx ht).trans (hcut _ ?_)
    exact fun h => ho (htgt ▸ h.mp hsrc)
  · exact hγy ht

/-- **An output depending on an input is joined to it.** If changing only the input `i` changes
the output `o` of a circuit, then the input `i` is read by its network, and its vertex is joined
to the vertex of the output `o`. -/
theorem exists_reachable_of_eval_ne {o : Fin m} {i : Fin n} {x y : Fin n → U}
    (hxy : ∀ k, k ≠ i → x k = y k) (hne : c.eval I x o ≠ c.eval I y o) :
    ∃ hi : Reach c (.input i),
      (graph c).toSimpleGraph.Reachable (.signal ⟨.input i, hi⟩) (.output o) := by
  -- Cut along the connected component of the output vertex: its edge cut is empty.
  set P : Set (Vertex c) := {v | (graph c).toSimpleGraph.Reachable v (.output o)}
  by_contra! h
  have hcut : ∀ e ∈ (graph c).edgeCut P,
      c.program.trace I x e.signal.1 = c.program.trace I y e.signal.1 := by
    intro e he
    have hst := (graph c).reachable_src_tgt e
    exact absurd ⟨fun hs => hst.symm.trans hs, fun ht => hst.trans ht⟩ he
  have hi : i ∉ (network c I fun _ => univ).readIn P := by
    rintro ⟨v, hv, hiv⟩
    obtain ⟨hi, rfl⟩ := site_eq_some hiv
    exact h hi hv
  refine hne (eval_splice hcut (z := y) (fun k hk => (hxy k ?_).symm) (fun _ _ => rfl) o
    |>.1 (SimpleGraph.Reachable.refl _)).symm
  rintro rfl
  exact hi hk

/-- **The graph is connected** when some vertex is joined to every output vertex. -/
theorem connected_of_reachable {v₀ : Vertex c}
    (h : ∀ o, (graph c).toSimpleGraph.Reachable v₀ (.output o)) :
    (graph c).toSimpleGraph.Connected := by
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨v₀, fun v => ?_⟩
  obtain ⟨o, ho⟩ := exists_reachable_output v
  exact (h o).trans ho.symm

end Cslib.Circuits.Frontier.Compiler
