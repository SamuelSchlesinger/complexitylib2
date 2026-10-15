/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Network
public import Complexity.Computability.Circuit.InnerSize
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
public import Mathlib.SetTheory.Cardinal.NatCard
import Complexity.Computability.Circuit.Program
import Complexity.Foundations.Data.Nat.Card

/-!
# Compiling a circuit into a constraint network

Fix a circuit `c` with `m` outputs over any signature, an interpretation `I` of the signature in
an alphabet `U`, and for each output `o` a set `Acc o ⊆ U` of *accepting* values. We build a
constraint network (`Compiler.network c I Acc`) whose accepted inputs are exactly those on which
every output `o` of the circuit lies in `Acc o`. A circuit deciding a set has one output; a
circuit computing a function accepts every value at each of its outputs.

Only the *reachable* wires matter: the outputs and, recursively, the wires read by reachable
gates. We call them *signals*. A signal is *consumed* by each argument slot of a reachable gate
that reads it, and each output is also consumed by its own *output vertex*. A circuit has
unbounded fan-out, but a network of bounded degree cannot give a signal one edge per consumer.
So each signal `w` with consumers `t₀, t₁, ...` is routed through a chain of *junctions*
`j₀, j₁, ...`, one per consumer:

```
  w --- j₀ --- j₁ --- j₂ --- ...
        |      |      |
        t₀     t₁     t₂
```

Each junction has one *feed* edge from its predecessor in the chain (the signal itself for
`j₀`) and one *deliver* edge to its consumer. The constraints are:

* the vertex of an input `x_i` reads `x_i` and puts it on its outgoing edge;
* the vertex of a gate `g` puts `g` applied to its incoming argument edges on its outgoing edge;
* a junction puts its incoming value on both of its outgoing edges;
* the vertex of the output `o` requires its incoming value to lie in `Acc o`.

The network records gates as *relations*: it never evaluates anything, and the constraint of a
gate does not care which of its edges a layout reaches first.

**Exactness** (`Compiler.satisfies_iff`). The values of the circuit satisfy the network.
Conversely, in a satisfying assignment the junction constraints force all edges of a signal to
carry one value, and the gate constraints, read in program order, force that value to be the
value of the signal in the circuit (`Compiler.eq_trace`). So the satisfying assignment, if any,
is unique, and along any layout the read-once branching program of the network
(`Cslib.Circuits.Frontier.Network.branchingProgram`) is unambiguous
(`Compiler.unambiguous_branchingProgram`).

**Outputs across a cut.** A circuit with many outputs computes a function; its network
accepts every value at every output. If the runs of the circuit on two inputs `x` and `y` agree
on the edge cut of a set of vertices `P`, the separator lemma splices them: on an input that reads
like `x` at `P` and like `y` elsewhere, the outputs held in `P` are those of `x` and the others
are those of `y` (`Compiler.eval_splice`). Cutting along the connected component of an output
vertex shows that an output depending on an input is joined to the vertex of that input
(`Compiler.exists_reachable_of_eval_ne`).

**Counting.** With `C` consumers, `W` signals and `m` outputs, the graph has `2 C` edges and
`W + C + m` vertices, so its cycle rank is `C - W - m + 1`: the number of argument slots minus
the number of signals, plus one. A gate of arity `k` has `k` slots, so it contributes `k - 1` to
the cycle rank, and a reachable input contributes `-1`. Hence, when the graph is connected, its
cycle rank is at most `(r - 1) s + 1 - |read|` for `s` gates of positive arity and fan-in at most
`r` (`Compiler.cycleRank_add_ncard_read_le`). Gates of arity zero, the constants, only lower the
cycle rank, so the count charges only the *inner* gates (`Circuit.innerSize`). Sharing creates
cycles; gates create local constraints. The count holds inside every closed set of vertices, for
instance a connected component (`Compiler.cycleRankOn_add_ncard_readIn_le`), and the count of
the whole graph is its case for the set of all vertices.

## Main definitions

* `Cslib.Circuits.Frontier.Compiler.graph c`: the graph of a circuit.
* `Cslib.Circuits.Frontier.Compiler.network c I Acc`: the constraint network of a circuit.

## Main results

* `Cslib.Circuits.Frontier.Compiler.satisfies_iff`, `Compiler.accepted_network`: exactness.
* `Cslib.Circuits.Frontier.Compiler.unambiguous_branchingProgram`: the branching program of every
  layout is unambiguous.
* `Cslib.Circuits.Frontier.Compiler.eval_splice`: outputs across a cut.
* `Cslib.Circuits.Frontier.Compiler.loopless`, `Compiler.connected`: the graph is loopless, and
  connected when the circuit has one output.
* `Cslib.Circuits.Frontier.Compiler.connected_of_reachable`,
  `Cslib.Circuits.Frontier.Compiler.exists_reachable_of_eval_ne`: connectivity from a common
  vertex; an output depending on an input is joined to its vertex.
* `Cslib.Circuits.Frontier.Compiler.maxDegreeLE`: for fan-in at most `r ≥ 2`, the degrees are at
  most `r + 1`; for fan-in two the graph is subcubic.
* `Cslib.Circuits.Frontier.Compiler.cycleRank_add_ncard_read_le`: the cycle rank and the number
  of inputs read add up to at most `(r - 1) s + 1`, where `s` counts the inner gates.
* `Cslib.Circuits.Frontier.Compiler.readIn_network`: the inputs read in a set of vertices.
* `Cslib.Circuits.Frontier.Compiler.ncard_touching_add_ncard_readIn_le`,
  `Cslib.Circuits.Frontier.Compiler.cycleRankOn_add_ncard_readIn_le`: the count inside a closed
  set of vertices.
* `Cslib.Circuits.Frontier.Compiler.card_vertex_le`: there are at most `2 r s + 3 m` vertices.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.Compiler

open Set

variable {σ : Signature} {n m : ℕ} (c : Circuit σ n m)

/-! ### Signals, consumers, and junctions -/

/-- A wire of a circuit is *reachable* when it is an output or is read by a reachable gate. -/
inductive Reach : Wire n c.size → Prop
  /-- The outputs are reachable. -/
  | output (o : Fin m) : Reach (c.outputs o)
  /-- The wires read by a reachable gate are reachable. -/
  | arg {g : Fin c.size} (a : Fin (σ.Arity (c.program.lines g).op)) :
      Reach (.gate g) → Reach ((c.program.lines g).wires a)

/-- The *signals* of a circuit: its reachable wires. -/
abbrev Signal : Type :=
  {w : Wire n c.size // Reach c w}

/-- An argument slot of a reachable gate. -/
abbrev Slot : Type :=
  {a : Σ g : Fin c.size, Fin (σ.Arity (c.program.lines g).op) // Reach c (.gate a.1)}

/-- A *consumer*: an argument slot of a reachable gate, or an output. -/
abbrev Consumer : Type :=
  Slot c ⊕ Fin m

variable {c}

/-- The signal read by a consumer. -/
def consumed : Consumer c → Signal c
  | .inl a => ⟨(c.program.lines a.1.1).wires a.1.2, .arg a.1.2 a.2⟩
  | .inr o => ⟨c.outputs o, .output o⟩

variable (c) in
/-- The number of consumers of a signal. -/
noncomputable def fanout (w : Signal c) : ℕ :=
  Nat.card {t : Consumer c // consumed t = w}

variable (c) in
/-- A *junction*: a copy of a signal for one of its consumers. The junctions of a signal `w` are
numbered `0, ..., fanout c w - 1`. -/
abbrev Junction : Type :=
  Σ w : Signal c, Fin (fanout c w)

variable (c) in
/-- Junctions correspond to consumers. -/
noncomputable def junctionEquiv : Junction c ≃ Consumer c :=
  (Equiv.sigmaCongrRight fun w =>
      (Finite.equivFin {t : Consumer c // consumed t = w}).symm).trans
    (Equiv.sigmaFiberEquiv consumed)

/-- The consumer of a junction reads the signal of the junction. -/
@[simp] theorem consumed_junctionEquiv (j : Junction c) : consumed (junctionEquiv c j) = j.1 :=
  ((Finite.equivFin {t : Consumer c // consumed t = j.1}).symm j.2).2

/-- The junction of a consumer belongs to the signal it reads. -/
@[simp] theorem fst_junctionEquiv_symm (t : Consumer c) :
    ((junctionEquiv c).symm t).1 = consumed t := by
  rw [← consumed_junctionEquiv, Equiv.apply_symm_apply]

/-- Every signal has a consumer. -/
theorem fanout_pos (w : Signal c) : 0 < fanout c w := by
  obtain ⟨w, hw⟩ := w
  refine Nat.card_pos_iff.mpr ⟨?_, inferInstance⟩
  cases hw with
  | output o => exact ⟨⟨.inr o, rfl⟩⟩
  | arg a hg => exact ⟨⟨.inl ⟨⟨_, a⟩, hg⟩, rfl⟩⟩

/-! ### The graph -/

variable (c) in
/-- The vertices: one per signal, one per junction, and one per output. -/
inductive Vertex : Type
  /-- The vertex of a signal: an input vertex or a gate vertex. -/
  | signal (w : Signal c)
  /-- A junction. -/
  | junction (j : Junction c)
  /-- The vertex of an output, which consumes it. -/
  | output (o : Fin m)

variable (c) in
/-- The edges: two per junction. -/
inductive Edge : Type
  /-- The edge into a junction from its predecessor in the chain. -/
  | feed (j : Junction c)
  /-- The edge from a junction to its consumer. -/
  | deliver (j : Junction c)

/-- Vertices are signals, junctions, and outputs. -/
def Vertex.equiv : Vertex c ≃ Signal c ⊕ Junction c ⊕ Fin m where
  toFun
    | .signal w => .inl w
    | .junction j => .inr (.inl j)
    | .output o => .inr (.inr o)
  invFun
    | .inl w => .signal w
    | .inr (.inl j) => .junction j
    | .inr (.inr o) => .output o
  left_inv v := by cases v <;> rfl
  right_inv v := by rcases v with w | j | o <;> rfl

/-- Edges are two copies of the junctions. -/
def Edge.equiv : Edge c ≃ Junction c ⊕ Junction c where
  toFun
    | .feed j => .inl j
    | .deliver j => .inr j
  invFun
    | .inl j => .feed j
    | .inr j => .deliver j
  left_inv e := by cases e <;> rfl
  right_inv e := by rcases e with j | j <;> rfl

instance : Finite (Vertex c) :=
  .of_equiv _ Vertex.equiv.symm

instance : Finite (Edge c) :=
  .of_equiv _ Edge.equiv.symm

/-- The vertex that consumes through a consumer: a gate vertex or an output vertex. -/
def owner : Consumer c → Vertex c
  | .inl a => .signal ⟨.gate a.1.1, a.2⟩
  | .inr o => .output o

/-- The vertex feeding a junction: the signal itself for its first junction, and the previous
junction of the chain otherwise. -/
def feeder : Junction c → Vertex c
  | ⟨w, ⟨0, _⟩⟩ => .signal w
  | ⟨w, ⟨k + 1, hk⟩⟩ => .junction ⟨w, ⟨k, Nat.lt_of_succ_lt hk⟩⟩

/-- No junction feeds itself. -/
theorem feeder_ne_junction : ∀ j : Junction c, feeder j ≠ .junction j
  | ⟨_, ⟨0, _⟩⟩, h => by cases h
  | ⟨_, ⟨k + 1, _⟩⟩, h => by
    have := congrArg (fun j : Junction c => (j.2 : ℕ)) (Vertex.junction.inj h)
    simp at this

/-- The source of an edge. -/
def src : Edge c → Vertex c
  | .feed j => feeder j
  | .deliver j => .junction j

/-- The target of an edge. -/
noncomputable def tgt : Edge c → Vertex c
  | .feed j => .junction j
  | .deliver j => owner (junctionEquiv c j)

/-- The signal carried by an edge. -/
def Edge.signal : Edge c → Signal c
  | .feed j | .deliver j => j.1

variable (c) in
/-- **The graph of a circuit**: the signals, junctions and outputs, joined by the feed and
deliver edges of the junctions. -/
noncomputable def graph : Multigraph (Vertex c) (Edge c) where
  src := src
  tgt := tgt

@[simp] theorem graph_src : (graph c).src = src :=
  rfl

@[simp] theorem graph_tgt : (graph c).tgt = tgt :=
  rfl

/-- The edge delivering a signal to one of its consumers. -/
noncomputable def deliverEdge (t : Consumer c) : Edge c :=
  .deliver ((junctionEquiv c).symm t)

/-- The edge delivering argument `a` to the reachable gate `g`. -/
noncomputable abbrev argEdge {g : Fin c.size} (hg : Reach c (.gate g))
    (a : Fin (σ.Arity (c.program.lines g).op)) : Edge c :=
  deliverEdge (.inl ⟨⟨g, a⟩, hg⟩)

variable (c) in
/-- The edge delivering an output to its output vertex. -/
noncomputable abbrev outEdge (o : Fin m) : Edge c :=
  deliverEdge (.inr o)

/-- The first edge of a signal: the feed edge of its first junction. -/
def head (w : Signal c) : Edge c :=
  .feed ⟨w, ⟨0, fanout_pos w⟩⟩

@[simp] theorem signal_deliverEdge (t : Consumer c) : (deliverEdge t).signal = consumed t :=
  fst_junctionEquiv_symm t

@[simp] theorem tgt_deliverEdge (t : Consumer c) : tgt (deliverEdge t) = owner t := by
  simp [deliverEdge, tgt]

@[simp] theorem src_head (w : Signal c) : src (head w) = .signal w :=
  rfl

@[simp] theorem signal_head (w : Signal c) : (head w).signal = w :=
  rfl

/-- An edge leaving the vertex of a signal is the first edge of that signal. -/
theorem eq_head_of_src_eq_signal : ∀ {e : Edge c} {w : Signal c}, src e = .signal w → e = head w
  | .feed ⟨_, ⟨0, _⟩⟩, _, h => by cases h; rfl
  | .feed ⟨_, ⟨_ + 1, _⟩⟩, _, h => by cases h
  | .deliver _, _, h => by cases h

/-- An edge leaving a junction carries the signal of the junction. -/
theorem signal_of_src_eq_junction :
    ∀ {e : Edge c} {j : Junction c}, src e = .junction j → e.signal = j.1
  | .feed ⟨_, ⟨0, _⟩⟩, _, h => by cases h
  | .feed ⟨_, ⟨_ + 1, _⟩⟩, _, h => by cases h; rfl
  | .deliver _, _, h => by cases h; rfl

/-- An edge entering the vertex of a signal delivers one of the argument slots of its gate. -/
theorem exists_slot_of_tgt_eq_signal {e : Edge c} {w : Signal c} (h : tgt e = .signal w) :
    ∃ a : Slot c, Wire.gate a.1.1 = w.1 ∧ e = deliverEdge (.inl a) := by
  rcases e with j | j
  · cases h
  · change owner (junctionEquiv c j) = _ at h
    obtain ⟨t, rfl⟩ := (junctionEquiv c).symm.surjective j
    rw [Equiv.apply_symm_apply] at h
    rcases t with a | o
    · exact ⟨a, congrArg Subtype.val (Vertex.signal.inj h), rfl⟩
    · cases h

/-- An edge entering the vertex of an output delivers that output. -/
theorem eq_outEdge_of_tgt_eq_output {e : Edge c} {o : Fin m} (h : tgt e = .output o) :
    e = outEdge c o := by
  rcases e with j | j
  · cases h
  · change owner (junctionEquiv c j) = _ at h
    obtain ⟨t, rfl⟩ := (junctionEquiv c).symm.surjective j
    rw [Equiv.apply_symm_apply] at h
    rcases t with a | o'
    · cases h
    · cases h
      rfl

/-! ### The network -/

variable {U : Type*} (I : Interpretation σ U) (Acc : Fin m → Set U)

/-- The value that the vertex of a signal puts on its outgoing edge: the input itself for an
input wire, and the operation of the gate applied to its incoming edges for a gate wire. -/
noncomputable def emit : Signal c → (Fin n → U) → (Edge c → U) → U
  | ⟨.input i, _⟩, x, _ => x i
  | ⟨.gate g, hg⟩, _, α => I (c.program.lines g).op fun a => α (argEdge hg a)

/-- The constraint at each vertex: the vertex of a signal emits the value of the signal, a
junction copies its incoming value onto its outgoing edges, and the vertex of an output requires
its incoming value to be accepting. -/
def Constraint : Vertex c → (Fin n → U) → (Edge c → U) → Prop
  | .signal w, x, α => α (head w) = emit I w x α
  | .junction j, _, α => ∀ e, src e = .junction j → α e = α (.feed j)
  | .output o, _, α => α (outEdge c o) ∈ Acc o

open Classical in
variable (c) in
/-- Each reachable input is read at the vertex of its signal. -/
noncomputable def site (i : Fin n) : Option (Vertex c) :=
  if h : Reach c (.input i) then some (.signal ⟨.input i, h⟩) else none

/-- An input is read only at the vertex of its signal. -/
theorem site_eq_some {i : Fin n} {v : Vertex c} (h : site c i = some v) :
    ∃ hi : Reach c (.input i), v = .signal ⟨.input i, hi⟩ := by
  unfold site at h
  split_ifs at h with hi
  exact ⟨hi, (Option.some_injective _ h).symm⟩

/-- A reachable input is read at the vertex of its signal. -/
theorem site_of_reach {i : Fin n} (hi : Reach c (.input i)) :
    site c i = some (.signal ⟨.input i, hi⟩) := by
  simp [site, hi]

variable (c) in
/-- **The constraint network of a circuit**, accepting at the output `o` the values in
`Acc o`. -/
noncomputable def network : Network U (Fin n) (Vertex c) (Edge c) where
  toMultigraph := graph c
  site := site c
  Constraint := Constraint I Acc
  constraint_congr v x x' α α' hx hα h := by
    cases v with
    | signal w =>
      obtain ⟨w, hw⟩ := w
      have h : α (head ⟨w, hw⟩) = emit I ⟨w, hw⟩ x α := h
      change α' (head ⟨w, hw⟩) = emit I ⟨w, hw⟩ x' α'
      rw [← hα (head ⟨w, hw⟩) (Or.inl rfl), h]
      cases w with
      | input i => exact hx i (site_of_reach hw)
      | gate g =>
        change I _ (fun a => α (argEdge hw a)) = I _ (fun a => α' (argEdge hw a))
        exact congrArg _ (funext fun a => hα _ (Or.inr (tgt_deliverEdge _)))
    | junction j =>
      intro e he
      rw [← hα e (Or.inl he), ← hα (.feed j) (Or.inr rfl)]
      exact h e he
    | output o =>
      change α' (outEdge c o) ∈ Acc o
      rw [← hα (outEdge c o) (Or.inr (tgt_deliverEdge (.inr o)))]
      exact h

@[simp] theorem network_toMultigraph : (network c I Acc).toMultigraph = graph c :=
  rfl

@[simp] theorem network_site : (network c I Acc).site = site c :=
  rfl

variable {I Acc}

/-! ### Exactness -/

/-- The values of the circuit satisfy the network: every edge carries the value of its
signal. -/
theorem satisfies_trace {x : Fin n → U} (hx : ∀ o, c.eval I x o ∈ Acc o) :
    (network c I Acc).Satisfies x fun e => c.program.trace I x e.signal.1 := by
  intro v
  cases v with
  | signal w =>
    obtain ⟨w, hw⟩ := w
    change c.program.trace I x w = emit I ⟨w, hw⟩ x _
    cases w with
    | input i => rfl
    | gate g =>
      rw [Program.trace_gate]
      simp only [emit, argEdge, signal_deliverEdge, consumed]
  | junction j =>
    intro e he
    change c.program.trace I x e.signal.1 = c.program.trace I x j.1.1
    rw [signal_of_src_eq_junction he]
  | output o =>
    change c.program.trace I x (outEdge c o).signal.1 ∈ Acc o
    rw [signal_deliverEdge]
    exact hx o

section Satisfying

variable {x : Fin n → U} {α : Edge c → U} (hα : (network c I Acc).Satisfies x α)
include hα

/-- In a satisfying assignment, the feed edges along the chain of junctions of a signal carry
the value of its first edge. -/
theorem feed_eq_head (w : Signal c) :
    ∀ (k : ℕ) (hk : k < fanout c w), α (.feed ⟨w, ⟨k, hk⟩⟩) = α (head w)
  | 0, _ => rfl
  | k + 1, hk => (hα (.junction ⟨w, ⟨k, by omega⟩⟩) _ rfl).trans (feed_eq_head w k _)

/-- In a satisfying assignment, every edge carries the value of the first edge of its
signal. -/
theorem eq_head (e : Edge c) : α e = α (head e.signal) := by
  rcases e with ⟨w, k⟩ | ⟨w, k⟩
  · exact feed_eq_head hα w k k.isLt
  · exact (hα (.junction ⟨w, k⟩) (.deliver ⟨w, k⟩) rfl).trans (feed_eq_head hα w k k.isLt)

/-- In a satisfying assignment, the first edge of every signal carries its value in the
circuit. -/
theorem head_eq_trace :
    ∀ (w : Wire n c.size) (hw : Reach c w), α (head ⟨w, hw⟩) = c.program.trace I x w := by
  refine c.program.wire_induction (fun i hw => hα (.signal ⟨.input i, hw⟩)) fun g ih hw => ?_
  have h : α (head ⟨.gate g, hw⟩) = I _ fun a => α (argEdge hw a) := hα (.signal ⟨.gate g, hw⟩)
  rw [h, Program.trace_gate]
  refine congrArg _ (funext fun a => ?_)
  rw [eq_head hα, argEdge, signal_deliverEdge]
  exact ih a _

/-- **Uniqueness.** A satisfying assignment puts on every edge the value of its signal in the
circuit. -/
theorem eq_trace (e : Edge c) : α e = c.program.trace I x e.signal.1 :=
  (eq_head hα e).trans (head_eq_trace hα _ e.signal.2)

end Satisfying

/-- **Exactness.** An assignment satisfies the network exactly when every output of the circuit
is accepted and the assignment puts on every edge the value of its signal in the circuit. -/
theorem satisfies_iff {x : Fin n → U} {α : Edge c → U} :
    (network c I Acc).Satisfies x α ↔
      (∀ o, c.eval I x o ∈ Acc o) ∧ α = fun e => c.program.trace I x e.signal.1 := by
  refine ⟨fun hα => ⟨fun o => ?_, funext (eq_trace hα)⟩, ?_⟩
  · have h : α (outEdge c o) ∈ Acc o := hα (.output o)
    rwa [eq_trace hα, signal_deliverEdge] at h
  · rintro ⟨hx, rfl⟩
    exact satisfies_trace hx

/-- **Exactness.** The network accepts exactly the inputs on which every output `o` of the
circuit lies in `Acc o`. -/
theorem accepted_network : (network c I Acc).accepted = {x | ∀ o, c.eval I x o ∈ Acc o} := by
  ext x
  exact ⟨fun ⟨_, hα⟩ => (satisfies_iff.mp hα).1, fun hx => ⟨_, satisfies_trace hx⟩⟩

/-- **Uniqueness.** An input has at most one satisfying assignment. -/
theorem satisfies_unique {x : Fin n → U} {α β : Edge c → U}
    (hα : (network c I Acc).Satisfies x α) (hβ : (network c I Acc).Satisfies x β) : α = β :=
  (satisfies_iff.mp hα).2.trans (satisfies_iff.mp hβ).2.symm

/-- The branching program of the network along any layout is unambiguous. -/
theorem unambiguous_branchingProgram (π : Layout (Vertex c)) :
    ((network c I Acc).branchingProgram π).Unambiguous :=
  (network c I Acc).unambiguous_branchingProgram π fun _ _ _ => satisfies_unique

/-! ### Outputs across a cut -/

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

/-! ### The shape of the graph -/

/-- The graph has no loops. -/
theorem loopless : (graph c).Loopless := by
  rintro (j | j) h
  · exact feeder_ne_junction j h
  · change Vertex.junction j = owner (junctionEquiv c j) at h
    generalize junctionEquiv c j = t at h
    rcases t with a | o <;> cases h

/-- A gate has at most `r` argument slots when the fan-in is at most `r`. -/
theorem ncard_slot_le {r : ℕ} (hfan : c.FanInAtMost r) (w : Wire n c.size) :
    {a : Slot c | Wire.gate a.1.1 = w}.ncard ≤ r := by
  calc {a : Slot c | Wire.gate a.1.1 = w}.ncard
      ≤ ((Finset.range r : Finset ℕ) : Set ℕ).ncard := by
        refine ncard_le_ncard_of_injOn (fun a => a.1.2.val) (fun a _ => ?_) ?_ (toFinite _)
        · simpa using a.1.2.isLt.trans_le (Program.fanInAtMost_iff.mp hfan a.1.1)
        · rintro ⟨⟨g, a⟩, hg⟩ hw ⟨⟨g', a'⟩, hg'⟩ hw' haa'
          obtain rfl : g = g' := Wire.gate.inj (hw.trans hw'.symm)
          obtain rfl : a = a' := Fin.ext haa'
          rfl
    _ = r := by rw [ncard_coe_finset, Finset.card_range]

/-- Two junctions fed by the same junction are equal. -/
theorem eq_of_feeder_eq_junction :
    ∀ {j₁ j₂ j : Junction c}, feeder j₁ = .junction j → feeder j₂ = .junction j → j₁ = j₂
  | ⟨_, ⟨0, _⟩⟩, _, _, h₁, _ => by cases h₁
  | ⟨_, ⟨_ + 1, _⟩⟩, ⟨_, ⟨0, _⟩⟩, _, _, h₂ => by cases h₂
  | ⟨_, ⟨_ + 1, _⟩⟩, ⟨_, ⟨_ + 1, _⟩⟩, _, h₁, h₂ => by
    have h := (Vertex.junction.inj h₁).trans (Vertex.junction.inj h₂).symm
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
    cases Fin.mk.inj_iff.mp (eq_of_heq h)
    rfl

/-- **The degrees are bounded.** When the gates have fan-in at most `r ≥ 2`, every vertex has
degree at most `r + 1`: a gate vertex has its argument edges and one outgoing edge, a junction
has three edges, and input vertices and output vertices have one. For fan-in two the graph is
subcubic. -/
theorem maxDegreeLE {r : ℕ} (hr : 2 ≤ r) (hfan : c.FanInAtMost r) :
    (graph c).MaxDegreeLE (r + 1) := by
  intro v
  cases v with
  | signal w =>
    -- The first edge of the signal, and the edges delivering the slots of its gate.
    calc ((graph c).incidenceSet (.signal w)).ncard
        ≤ (insert (head w)
            ((fun a => deliverEdge (.inl a)) '' {a : Slot c | Wire.gate a.1.1 = w.1})).ncard := by
          refine ncard_le_ncard (fun e he => ?_) (toFinite _)
          rcases he with he | he
          · exact Or.inl (eq_head_of_src_eq_signal he)
          · obtain ⟨a, ha, rfl⟩ := exists_slot_of_tgt_eq_signal he
            exact Or.inr ⟨a, ha, rfl⟩
      _ ≤ {a : Slot c | Wire.gate a.1.1 = w.1}.ncard + 1 :=
          (ncard_insert_le _ _).trans (Nat.add_le_add_right (ncard_image_le (toFinite _)) 1)
      _ ≤ r + 1 := Nat.add_le_add_right (ncard_slot_le hfan w.1) 1
  | junction j =>
    -- Its feed and deliver edges, and the feed edge of the next junction.
    calc ((graph c).incidenceSet (.junction j)).ncard
        ≤ (insert (Edge.feed j) (insert (Edge.deliver j)
            {e | ∃ j', feeder j' = .junction j ∧ e = Edge.feed j'})).ncard := by
          refine ncard_le_ncard (fun e he => ?_) (toFinite _)
          rcases he with he | he
          · rcases e with j' | j'
            · exact Or.inr (Or.inr ⟨j', he, rfl⟩)
            · cases he
              exact Or.inr (Or.inl rfl)
          · rcases e with j' | j'
            · cases he
              exact Or.inl rfl
            · change owner (junctionEquiv c j') = _ at he
              generalize junctionEquiv c j' = t at he
              rcases t with a | o <;> cases he
      _ ≤ {e | ∃ j', feeder j' = .junction j ∧ e = Edge.feed j'}.ncard + 1 + 1 :=
          (ncard_insert_le _ _).trans (Nat.add_le_add_right (ncard_insert_le _ _) 1)
      _ ≤ r + 1 := by
          have : {e | ∃ j', feeder j' = .junction j ∧ e = Edge.feed j'}.ncard ≤ 1 :=
            (ncard_le_one (toFinite _)).mpr fun _ ⟨j₁, h₁, he₁⟩ _ ⟨j₂, h₂, he₂⟩ =>
              he₁.trans ((eq_of_feeder_eq_junction h₁ h₂) ▸ he₂.symm)
          omega
  | output o =>
    -- Only the edge delivering the output.
    calc ((graph c).incidenceSet (.output o)).ncard
        ≤ ({outEdge c o} : Set (Edge c)).ncard := by
          refine ncard_le_ncard (fun e he => ?_) (toFinite _)
          rcases he with he | he
          · rcases e with ⟨_, ⟨_ | _, _⟩⟩ | j <;> cases he
          · exact eq_outEdge_of_tgt_eq_output he
      _ ≤ r + 1 := by simp

/-! ### Connectivity -/

/-- The junctions of a signal are joined to its vertex along their chain. -/
theorem reachable_junction_signal (w : Signal c) :
    ∀ (k : ℕ) (hk : k < fanout c w),
      (graph c).toSimpleGraph.Reachable (.junction ⟨w, ⟨k, hk⟩⟩) (.signal w)
  | 0, hk => ((graph c).reachable_src_tgt (.feed ⟨w, ⟨0, hk⟩⟩)).symm
  | k + 1, hk => ((graph c).reachable_src_tgt (.feed ⟨w, ⟨k + 1, hk⟩⟩)).symm.trans
      (reachable_junction_signal w k (by omega))

/-- Every junction is joined to the vertex of its signal. -/
theorem reachable_junction (j : Junction c) :
    (graph c).toSimpleGraph.Reachable (.junction j) (.signal j.1) :=
  reachable_junction_signal j.1 j.2 j.2.isLt

/-- The vertex of a signal is joined to each of its consumers. -/
theorem reachable_owner (t : Consumer c) :
    (graph c).toSimpleGraph.Reachable (.signal (consumed t)) (owner t) := by
  have h := ((graph c).reachable_src_tgt (deliverEdge t)).symm
  rw [graph_tgt, tgt_deliverEdge] at h
  rw [← fst_junctionEquiv_symm]
  exact (h.trans (reachable_junction _)).symm

/-- The vertex of every signal is joined to the vertex of some output. -/
theorem exists_reachable_signal_output (w : Signal c) :
    ∃ o, (graph c).toSimpleGraph.Reachable (.signal w) (.output o) := by
  obtain ⟨w, hw⟩ := w
  induction hw with
  | output o => exact ⟨o, reachable_owner (.inr o)⟩
  | arg a hg ih =>
    obtain ⟨o, ho⟩ := ih
    exact ⟨o, (reachable_owner (.inl ⟨⟨_, a⟩, hg⟩)).trans ho⟩

/-- Every vertex is joined to the vertex of some output. -/
theorem exists_reachable_output (v : Vertex c) :
    ∃ o, (graph c).toSimpleGraph.Reachable v (.output o) := by
  cases v with
  | signal w => exact exists_reachable_signal_output w
  | junction j =>
    obtain ⟨o, ho⟩ := exists_reachable_signal_output j.1
    exact ⟨o, (reachable_junction j).trans ho⟩
  | output o => exact ⟨o, .refl _⟩

/-- **The graph is connected** when some vertex is joined to every output vertex. -/
theorem connected_of_reachable {v₀ : Vertex c}
    (h : ∀ o, (graph c).toSimpleGraph.Reachable v₀ (.output o)) :
    (graph c).toSimpleGraph.Connected := by
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨v₀, fun v => ?_⟩
  obtain ⟨o, ho⟩ := exists_reachable_output v
  exact (h o).trans ho.symm

/-- **The graph of a circuit with one output is connected.** -/
theorem connected (c : Circuit σ n 1) : (graph c).toSimpleGraph.Connected :=
  connected_of_reachable (v₀ := .output 0) fun o => Subsingleton.elim (0 : Fin 1) o ▸ .refl _

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

/-! ### Counting -/

variable (I Acc)

/-- The inputs read by the network are the reachable inputs. -/
theorem read_network : (network c I Acc).read = {i | Reach c (.input i)} := by
  ext i
  simp only [Network.read, Network.readIn, mem_univ, true_and, mem_ofPred_eq, network_site]
  exact ⟨fun ⟨_, hv⟩ => (site_eq_some hv).1, fun hi => ⟨_, site_of_reach hi⟩⟩

/-- Each vertex reads at most one input. -/
theorem ncard_readAt_le (v : Vertex c) : ((network c I Acc).readAt v).ncard ≤ 1 := by
  refine (ncard_le_one (toFinite _)).mpr fun i hi i' hi' => ?_
  obtain ⟨_, rfl⟩ := site_eq_some hi
  obtain ⟨_, h⟩ := site_eq_some hi'
  exact Wire.input.inj (congrArg Subtype.val (Vertex.signal.inj h))

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

/-- Signals are reachable inputs and reachable gates. -/
def signalEquiv :
    Signal c ≃ {i : Fin n // Reach c (.input i)} ⊕ {g : Fin c.size // Reach c (.gate g)} where
  toFun
    | ⟨.input i, h⟩ => .inl ⟨i, h⟩
    | ⟨.gate g, h⟩ => .inr ⟨g, h⟩
  invFun
    | .inl i => ⟨.input i.1, i.2⟩
    | .inr g => ⟨.gate g.1, g.2⟩
  left_inv w := by rcases w with ⟨w | w, h⟩ <;> rfl
  right_inv w := by rcases w with w | w <;> rfl

variable (c) in
/-- The reachable inner gates: the reachable gates of positive arity. -/
abbrev InnerGate : Type :=
  {g : Fin c.size // Reach c (.gate g) ∧ σ.Arity (c.program.lines g).op ≠ 0}

variable (c) in
/-- The reachable inner gates whose vertex lies in `W`. -/
abbrev InnerGateIn (W : Set (Vertex c)) : Type :=
  {g : InnerGate c // Vertex.signal ⟨.gate g.1, g.2.1⟩ ∈ W}

/-- The reachable inner gates are inner gates. -/
theorem card_innerGate_le : Nat.card (InnerGate c) ≤ c.innerSize := by
  rw [Circuit.innerSize, ← Nat.card_eq_finsetCard]
  exact Nat.card_le_card_of_injective (fun g => ⟨g.1, Program.mem_innerGates.mpr g.2.2⟩)
    fun _ _ h => Subtype.ext (congrArg Subtype.val h :)

/-- The reachable inner gates in `W` are inner gates. -/
theorem card_innerGateIn_le (W : Set (Vertex c)) : Nat.card (InnerGateIn c W) ≤ c.innerSize :=
  (Finite.card_subtype_le _).trans card_innerGate_le

/-- There are at least as many reachable gates as reachable inner gates. -/
theorem card_innerGate_le_card_gate :
    Nat.card (InnerGate c) ≤ Nat.card {g : Fin c.size // Reach c (.gate g)} :=
  Nat.card_le_card_of_injective (fun g => ⟨g.1, g.2.1⟩) fun _ _ h =>
    Subtype.ext (congrArg Subtype.val h :)

/-- There are at most `r` slots per reachable inner gate in `W`; constant gates have none. -/
theorem card_slot_le {r : ℕ} (hfan : c.FanInAtMost r) (W : Set (Vertex c)) :
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

/-- There are two edges per consumer. -/
theorem card_edge : Nat.card (Edge c) = 2 * Nat.card (Consumer c) := by
  rw [Nat.card_congr Edge.equiv, Nat.card_sum, Nat.card_congr (junctionEquiv c), two_mul]

/-- There is one vertex per signal, per consumer, and per output. -/
theorem card_vertex :
    Nat.card (Vertex c) = Nat.card (Signal c) + Nat.card (Consumer c) + m := by
  rw [Nat.card_congr Vertex.equiv, Nat.card_sum, Nat.card_sum, Nat.card_congr (junctionEquiv c),
    Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin, add_assoc]

/-- The consumers are the argument slots of reachable gates and the outputs. -/
theorem card_consumer : Nat.card (Consumer c) = Nat.card (Slot c) + m := by
  rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin]

/-- Every signal has a consumer, so there are at least as many consumers as signals. -/
theorem card_signal_le_card_consumer : Nat.card (Signal c) ≤ Nat.card (Consumer c) := by
  rw [← Nat.card_congr (junctionEquiv c)]
  exact Nat.card_le_card_of_injective (fun w => ⟨w, ⟨0, fanout_pos w⟩⟩) fun w w' h =>
    congrArg Sigma.fst h

/-! ### Counting inside a closed set of vertices

Let `W` be a closed set of vertices, one with no edge leaving it. The edges at `W` are the feed
and deliver edges of the junctions in `W`; the junctions in `W` are those of the consumers whose
owner is in `W`, that is, the slots of the gates in `W` and the outputs in `W`; and the vertices
of `W` are its signals, junctions, and outputs. A circuit with several outputs may have a
disconnected graph, and the count applies to each component. -/

/-- The vertices of `W` are its signals, its junctions, and its outputs. -/
private theorem ncard_eq_add (W : Set (Vertex c)) :
    W.ncard = Nat.card {w // Vertex.signal w ∈ W} + Nat.card {j // Vertex.junction j ∈ W} +
      Nat.card {o // Vertex.output o ∈ W} := by
  rw [← Nat.card_coe_set_eq, add_assoc]
  exact (Nat.card_subtype_eq_add Vertex.equiv _).trans
    (congrArg _ (Nat.card_subtype_eq_add (Equiv.refl _) _))

/-- The edges at a closed set `W` are the feed and deliver edges of the junctions in `W`. -/
private theorem ncard_touching_eq {W : Set (Vertex c)} (hW : (graph c).edgeCut W = ∅) :
    ((graph c).touching W).ncard = 2 * Nat.card {j // Vertex.junction j ∈ W} := by
  have hW := (graph c).edgeCut_eq_empty_iff.1 hW
  rw [← Nat.card_coe_set_eq, Nat.card_subtype_eq_add Edge.equiv, two_mul]
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
  exact Nat.card_subtype_eq_add (Equiv.refl _) _

/-- The signals in `W` include the inputs read in `W` and the reachable inner gates in `W`. -/
private theorem ncard_readIn_add_card_le (W : Set (Vertex c)) :
    ((network c I Acc).readIn W).ncard + Nat.card (InnerGateIn c W) ≤
      Nat.card {w // Vertex.signal w ∈ W} := by
  have hread : ((network c I Acc).readIn W).ncard =
      Nat.card {i : {i // Reach c (.input i)} // Vertex.signal ⟨.input i.1, i.2⟩ ∈ W} := by
    rw [readIn_network, ← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeExists _
      fun i : {i // Reach c (.input i)} => Vertex.signal ⟨.input i.1, i.2⟩ ∈ W).symm
  rw [Nat.card_subtype_eq_add signalEquiv, hread]
  refine Nat.add_le_add le_rfl ?_
  exact Nat.card_le_card_of_injective (fun g => ⟨⟨g.1.1, g.1.2.1⟩, g.2⟩) fun _ _ h =>
    Subtype.ext (Subtype.ext (congrArg (fun g => g.1.1) h))

/-- **The count inside a closed set, gate by gate.** For fan-in at most `r`, the edges at a
closed set of vertices `W` and the inputs read in `W` number at most `(r - 1) s_W` more than the
vertices of `W`, where `s_W` counts the reachable inner gates in `W`. -/
theorem ncard_touching_add_ncard_readIn_le_card_innerGateIn {r : ℕ} (hfan : c.FanInAtMost r)
    {W : Set (Vertex c)} (hW : (graph c).edgeCut W = ∅) :
    ((graph c).touching W).ncard + ((network c I Acc).readIn W).ncard ≤
      W.ncard + (r - 1) * Nat.card (InnerGateIn c W) := by
  have hE := ncard_touching_eq hW
  have hJ := card_junction_eq hW
  have hV := ncard_eq_add W
  have hslot := card_slot_le hfan W
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
      W.ncard + (r - 1) * c.innerSize :=
  (ncard_touching_add_ncard_readIn_le_card_innerGateIn I Acc hfan hW).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (card_innerGateIn_le W)) _)

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

/-! ### Counting in the whole graph -/

/-- **The edge count.** For fan-in at most `r`, the edges of the graph and the inputs read by
the network number at most `(r - 1) s` more than the vertices, where `s` counts the inner
gates. This is the count inside the closed set of all vertices. -/
theorem card_edge_add_ncard_read_le {r : ℕ} (hfan : c.FanInAtMost r) :
    Nat.card (Edge c) + (network c I Acc).read.ncard ≤
      Nat.card (Vertex c) + (r - 1) * c.innerSize := by
  have h := ncard_touching_add_ncard_readIn_le I Acc hfan (graph c).edgeCut_univ
  have htouch : (graph c).touching univ = univ := eq_univ_of_forall fun _ => Or.inl (mem_univ _)
  rw [htouch, ncard_univ, ncard_univ] at h
  exact h

/-- **The cycle rank.** For fan-in at most `r`, if the graph is connected (as it is for one
output), its cycle rank and the number of inputs read by the network add up to at most
`(r - 1) s + 1`, where `s` counts the inner gates. -/
theorem cycleRank_add_ncard_read_le {r : ℕ} (hfan : c.FanInAtMost r)
    (hconn : (graph c).toSimpleGraph.Connected) :
    (graph c).cycleRank + (network c I Acc).read.ncard ≤ (r - 1) * c.innerSize + 1 := by
  have h := card_edge_add_ncard_read_le I Acc hfan
  have hV := (graph c).card_le_card_add_one_of_connected hconn
  unfold Multigraph.cycleRank
  omega

/-- **The number of vertices** is at most `2 r s + 3 m` for fan-in at most `r`, where `s` counts
the inner gates and `m` the outputs. -/
theorem card_vertex_le {r : ℕ} (hfan : c.FanInAtMost r) :
    Nat.card (Vertex c) ≤ 2 * r * c.innerSize + 3 * m := by
  have hcons := card_consumer (c := c)
  have hslot : Nat.card (Slot c) ≤ r * c.innerSize := by
    have h := (card_slot_le hfan univ).trans (Nat.mul_le_mul_left r (card_innerGateIn_le univ))
    rwa [Nat.card_congr (Equiv.subtypeUnivEquiv fun t => mem_univ (owner (.inl t)))] at h
  have := card_signal_le_card_consumer (c := c)
  rw [card_vertex, mul_assoc]
  omega

end Cslib.Circuits.Frontier.Compiler
