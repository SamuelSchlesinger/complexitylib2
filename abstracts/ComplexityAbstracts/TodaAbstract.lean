/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.TodaBridge

/-! # Toda's theorem

Counting accepting certificates can be much more powerful than asking whether even one exists.
Toda shows that a deterministic algorithm with an exact counting oracle can decide every problem
specified by a fixed finite alternation of polynomially bounded existential and universal choices.
The proof first expresses these choices through randomized parity tests, then encodes their
majority verdict in a binary digit of a witness count. This gives containment of the polynomial
hierarchy in polynomial time with counting access, without asserting the reverse containment.

The oracle counts certificates accepted by a deterministic verifier in polynomial time and answers
queries about individual binary digits. One native polynomial clock governs the entire stateful
interaction, including constructing queries and reading replies. Correctness holds for every
extension of valid bit answers to words outside the query encoding's image; the model below also
separates finite-uniform program syntax from fair-coin efficiency.

Lean checks the bridge, and the audit permits only the listed foundational program and machine
modules, with no complexity-class or Toda-theorem allowance.

## References

* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

namespace ComplexityTests.Abstracts.TodaAbstract

/-- Frame each bit as `[true, b]` and terminate the word with `[false]`. -/
def frame (w : List Bool) : List Bool := w.flatMap (fun b => [true, b]) ++ [false]

/-- Encode a pair by framing its first component and appending its second component. -/
def encodePair {α β : Type} (a : α → List Bool) (b : β → List Bool) (p : α × β) :
    List Bool := frame (a p.1) ++ b p.2

theorem encodePair_injective {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) :
    Function.Injective (encodePair a b) := TodaBridge.encodePair_injective a b

theorem bits_injective : Function.Injective Nat.bits := TodaBridge.bits_injective

/-- Natural numbers are encoded by their canonical little-endian binary digits. -/
def encNat : ℕ ↪ List Bool := ⟨Nat.bits, bits_injective⟩

/-- Pair encoding; `↪` records injectivity. -/
def encPair {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) : α × β ↪ List Bool :=
  ⟨encodePair a b, encodePair_injective a b⟩

/-- A Boolean is encoded by a single bit. -/
def encBool : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; injection h⟩

/-- Bitstrings encode themselves. -/
def encBits : List Bool ↪ List Bool := Function.Embedding.refl _

/-- A single finite-state binary multi-tape machine computes `f` on every encoded input,
within polynomial time and work space. Inputs are read-only; outputs are write-only.
`Cslib.PolynomiallyBounded` means bounded above by some polynomial. -/
def ComputableInPolyTime {α β : Type} (f : α → β)
    (a : α ↪ List Bool) (b : β ↪ List Bool) : Prop :=
  ∃ t s : ℕ → ℕ, Cslib.PolynomiallyBounded t ∧ Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength f a b t s

/-- A terminating return/request tree. A private request indexed by `n` draws a fresh uniform
`Fin (n+1)`; an external request sends `((), word)` and receives a word. Private draws do not
change the oracle's state. Bare syntax imposes no efficiency or fair-coin implementability:
those are required separately by `StrictOraclePPT`. -/
abbrev InteractiveProgram (β : Type) :=
  Cslib.ProbOracleComp (fun _ : Unit × List Bool => List Bool) β

/-- One fixed finite fair-coin machine and one polynomial clock realize the entire joint law
of the program's encoded result and the oracle's final state, against every stateful oracle.
Each live instruction consumes one fresh fair bit to select between two transitions. Ordinary
steps perform an upstream tape action, append at most one bit to a query buffer and move a
read-only reply head by at most one cell. A query step submits the buffer, installs the reply,
resets the reply head and clears the buffer. Each instruction costs one unit; the oracle's
computation is external. The bounded run observes its written output on halting or clock
exhaustion, so the definition does not pretend the unclocked machine has already halted. -/
def StrictOraclePPT {α β : Type} (enc : α ↪ List Bool) (out : β ↪ List Bool)
    (program : α → InteractiveProgram β) : Prop :=
  ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : Turing.MultiTapePTM k Bool Control Unit) (c d : ℕ),
    ∀ a (State : Type)
      (oracle : Unit × List Bool → StateT State PMF (List Bool)) s,
      Cslib.ProbOracleComp.runWith oracle (out <$> program a) s =
        Cslib.ProbOracleComp.runWith oracle
          (machine.runOracle (c * ((enc a).length + 1) ^ d) (enc a)) s

/-- Deterministic word-query programs; the syntax has queries but no random operation. -/
abbrev QueryProgram (β : Type) := Cslib.OracleComp (fun _ : Unit × List Bool => List Bool) β

/-- An oracle language replies to each requested word with its one-bit membership verdict. -/
noncomputable def languageOracle (B : Set (List Bool)) (q : Unit × List Bool) : List Bool :=
  [@decide (q.2 ∈ B) (Classical.propDecidable _)]

/-- Count the accepted binary strings of exactly `n` bits. -/
def acceptCount {α : Type} (V : α × List Bool → Bool) (a : α) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin n → Bool => V (a, List.ofFn w) = true).card

/-- A #P function counts witnesses of a fixed polynomial length accepted by one total
polynomial-time deterministic verifier. Counts are natural numbers in binary. -/
def SharpP {α : Type} (enc : α ↪ List Bool) : Set (α → ℕ) :=
  {f | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
    ∀ a, f a = acceptCount V a (p.eval (enc a).length)}

/-- Alternating quantifiers over fixed-length blocks of bits, with an existential first
quantifier when `q=true`. Each subsequent block has the opposite quantifier. -/
def Alternation : Bool → List ℕ → (List Bool → Prop) → Prop
  | _, [], V => V []
  | true, n :: ns, V => ∃ w : List Bool, w.length = n ∧ Alternation false ns (fun v => V (w ++ v))
  | false, n :: ns, V => ∀ w : List Bool, w.length = n → Alternation true ns (fun v => V (w ++ v))

/-- The polynomial hierarchy: a fixed finite number of alternating polynomial-length
certificate blocks followed by a total polynomial-time verifier. The number of alternations
and the length polynomials are fixed for the language, not supplied as part of an instance. -/
def PH {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (ps : List (Polynomial ℕ)) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
    ∀ a, a ∈ A ↔ Alternation true (ps.map (fun p => p.eval (enc a).length))
      (fun w => V (a, w) = true)}

/-- An oracle language answers the bits of `f`: every valid query `(b,i)` returns the `i`th
binary digit. Answers to words outside the encoding image are unrestricted. -/
def AnswersBits {β : Type} (enc : β ↪ List Bool) (f : β → ℕ)
    (B : Set (List Bool)) : Prop :=
  ∀ b i, encPair enc encNat (b, i) ∈ B ↔ (f b).testBit i

/-- Deterministic polynomial time with a #P oracle, via bit queries. The program must decide
the language against every extension of the valid bit answers to malformed query words.
Its native machine clock is polynomial uniformly over every stateful oracle. -/
def PWithSharpPOracle {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (β : Type) (b : β ↪ List Bool) (f : β → ℕ), f ∈ SharpP b ∧
    ∃ program : α → QueryProgram Bool,
      StrictOraclePPT enc encBool
        (fun a => Cslib.OracleComp.interpret Cslib.ProbOracleComp.query (program a)) ∧
      ∀ B : Set (List Bool), AnswersBits b f B →
        ∀ a, a ∈ A ↔ Cslib.OracleComp.interpret (m := Id) (languageOracle B) (program a) = true}

/-- Every problem in the polynomial hierarchy is decidable by a deterministic polynomial-time
oracle program with bit access to a #P function, with uniform native efficiency. -/
theorem toda {α : Type} (enc : α ↪ List Bool) : PH enc ⊆ PWithSharpPOracle enc := by
  have hgame (q : Bool) (ns : List ℕ) (V : List Bool → Prop) :
      Alternation q ns V ↔ TodaBridge.Alternation q ns V := by
    induction ns generalizing q V with
    | nil => cases q <;> rfl
    | cons n ns ih =>
      cases q
      · exact forall_congr' fun w => imp_congr_right fun _ => ih _ _
      · exact exists_congr fun w => and_congr_right fun _ => ih _ _
  have hclass : PH enc = TodaBridge.PH enc := by
    ext A
    exact exists_congr fun ps => exists_congr fun V => and_congr_right fun _ =>
      forall_congr' fun a => iff_congr Iff.rfl (hgame _ _ _)
  rw [hclass]
  exact TodaBridge.toda enc

/--
info: abstract audit passed for `ComplexityTests.Abstracts.TodaAbstract`:
25 root declarations, 237 dependencies checked
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.TodaAbstract allowing [
  Complexity.Computability.Machines.Turing.MultiTape.Machine,
  Complexity.Computability.Machines.Turing.MultiTape.Machine.Program,
  Complexity.Computability.Machines.Turing.MultiTape.Probabilistic,
  Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle,
  Complexity.Languages.Probabilistic.Basic,
  Complexity.Languages.Probabilistic.Oracle,
  Complexity.Languages.Probabilistic.Oracle.Interaction
]

end ComplexityTests.Abstracts.TodaAbstract
