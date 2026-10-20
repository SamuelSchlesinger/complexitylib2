/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Feature
public import Mathlib.Tactic.DeriveFintype

/-!
# The uniform tableau circuit of a multi-tape machine

The run of a multi-tape machine over `Bool` for `T` steps on inputs of length `n` is simulated by
a De Morgan circuit written down gate by gate (`Cslib.Circuits.Boolean.Tableau.gates`), in the
format of `Cslib.Circuits.Circuit.code`. The circuit is *uniform*: the operation and the wires of
gate `g` are given by a table of constant size, indexed by `g` modulo the size of a block, and by
a few additions and multiplications of `g`, `n` and `T` (`Cslib.Circuits.Boolean.Tableau.gateCode`).
This is the circuit of Ladner's proof that the circuit value problem is `P`-complete under
logarithmic-space reductions [Ladner1975], [Arora and Barak, Section 6.7][AroraBarak09],
[Papadimitriou, Theorem 8.1][Papadimitriou94].

The circuit follows the configuration in the model of `Turing.MultiTapeTM`, without conversion to
a single-tape or oblivious machine. Work-tape cells `-T, …, T` and input positions `0, …, n + 1`
share the `2 T + 1` *columns* `c`: column `c` holds the input head at position `c`, and the work
heads and work cells at `c - T`. After two constant gates (`false` at wire `n`, `true` at wire
`n + 1`), the circuit has one block of gates for each time `t ≤ T`. Block `0` consists of
constants describing the initial configuration. Block `t + 1` reads block `t` and has four
regions:

* the *scan*, column by column: the symbols under the heads, as disjunctions accumulated across
  the columns (`Cslib.Circuits.Boolean.Tableau.ScanLoc`), and the negated head positions;
* the *global* gates: each situation (`Turing.MultiTapeTM.Situation`) as a conjunction of the
  state and the symbols read, and each attribute of the action
  (`Cslib.Circuits.Boolean.Tableau.Attr`) as a disjunction over the situations with that
  attribute;
* the *global features*: the state and the view of the output (`Turing.OutView`);
* the *column features*: the input head, the work heads and the work cells of each column.

Every feature at time `t + 1` is a disjunction of at most eight conjunctions of two wires
(`Cslib.Circuits.Boolean.Tableau.gfTerms`, `Cslib.Circuits.Boolean.Tableau.colTerms`), computed
by sixteen gates. A gate refers to wires symbolically (`Cslib.Circuits.Boolean.Tableau.Ref`),
relative to its block and column, and a reference is resolved to a wire number by arithmetic
(`Cslib.Circuits.Boolean.Tableau.Ref.resolve`).

The circuit is well formed (`Cslib.Circuits.Boolean.Tableau.isCodeFrom_gates`): every gate reads
only inputs and earlier gates. Its correctness is proved in `Tableau/Correct.lean`.

## Main definitions

* `Cslib.Circuits.Boolean.Tableau.Loc`: the position of a gate within its block.
* `Cslib.Circuits.Boolean.Tableau.Ref`: references to wires, relative to a block and a column.
* `Cslib.Circuits.Boolean.Tableau.table`: the gate at each position of a block.
* `Cslib.Circuits.Boolean.Tableau.wire`: the wire number of a position.
* `Cslib.Circuits.Boolean.Tableau.gateCode`: the gate with a given number.
* `Cslib.Circuits.Boolean.Tableau.gates`, `Cslib.Circuits.Boolean.Tableau.outWire`: the gate list
  and the output wire.
* `Cslib.Circuits.Boolean.Tableau.circuit`: the tableau as a De Morgan circuit.

## Main results

* `Cslib.Circuits.Boolean.Tableau.isCodeFrom_gates`: the gate list is the code of a program.
* `Cslib.Circuits.Boolean.Tableau.code_circuit`: the code of the circuit is the gate list with
  the output wire.

## References

* [R. E. Ladner, *The circuit value problem is log space complete for P*][Ladner1975]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Sections 6.1 and 6.7][AroraBarak09]
* [C. H. Papadimitriou, *Computational Complexity*, Theorem 8.1][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Circuits.Program

universe v

/-- A list of gates is the code of a program when every entry has the arity of its operation and
reads only the inputs and the gates before it. -/
private theorem isCodeFrom_of_getElem {σ : Signature.{v}} {n k : ℕ} {gates : List (σ.Op × List ℕ)}
    (h : ∀ j (hj : j < gates.length), gates[j].2.length = σ.Arity gates[j].1 ∧
      ∀ i ∈ gates[j].2, i < n + k + j) :
    IsCodeFrom σ n k gates := by
  induction gates generalizing k with
  | nil => trivial
  | cons g gates ih =>
    have h₀ := h 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h₀
    refine ⟨h₀, ih fun j hj => ?_⟩
    obtain ⟨h₁, h₂⟩ := h (j + 1) (by simpa using hj)
    simp only [List.getElem_cons_succ] at h₁ h₂
    exact ⟨h₁, fun i hi => by have := h₂ i hi; omega⟩

end Cslib.Circuits.Program

namespace Cslib.Circuits.Boolean.Tableau

open Turing MultiTapeTM

/-! ### Positions within a block -/

/-- One aspect of an action: the next state, the move of the input head, what is written on a work
tape, the move of a work head, and the output symbol. -/
inductive Attr (k : ℕ) (State : Type) where
  /-- The next state is `q` (`none` to halt). -/
  | state (q : Option State)
  /-- The input head moves by `m`. -/
  | inMove (m : SignType)
  /-- Work tape `i` is written `w` (`none` to leave the cell). -/
  | write (i : Fin k) (w : Option (Option Bool))
  /-- Work head `i` moves by `m`. -/
  | move (i : Fin k) (m : SignType)
  /-- The output symbol is `e`. -/
  | out (e : Option Bool)
  deriving DecidableEq, Fintype

/-- The features held in each column: the input head, a work head and a work cell. -/
inductive ColFeat (k : ℕ) where
  /-- The input head is at the position of the column. -/
  | inPos
  /-- Work head `i` is at the cell of the column. -/
  | head (i : Fin k)
  /-- The cell of the column on work tape `i` holds `s`. -/
  | cell (i : Fin k) (s : Option Bool)
  deriving DecidableEq, Fintype

/-- The global features: the state and the view of the output. -/
inductive GFeat (State : Type) where
  /-- The state is `q` (`none` once halted). -/
  | state (q : Option State)
  /-- The output written so far has the view `o`. -/
  | out (o : OutView)
  deriving DecidableEq, Fintype

/-- The quantities accumulated by the scan across the columns: the symbol under the input head and
the symbols under the work heads. -/
inductive ScanQ (k : ℕ) where
  /-- The input head reads `s`. -/
  | inRead (s : Option Bool)
  /-- Work head `i` reads `s`. -/
  | read (i : Fin k) (s : Option Bool)
  deriving DecidableEq, Fintype

/-- The gates of a column of the scan. -/
inductive ScanLoc (k : ℕ) where
  /-- Work head `i` is not at the cell of the column. -/
  | nh (i : Fin k)
  /-- The negated input bit of the column. -/
  | nx
  /-- The contribution of the column to a scanned quantity. -/
  | term (q : ScanQ k)
  /-- The disjunction of the contributions of the columns so far. -/
  | acc (q : ScanQ k)
  deriving DecidableEq, Fintype

/-- The number of situations of a machine. -/
abbrev numSit (k : ℕ) (State : Type) [Fintype State] : ℕ := Fintype.card (Situation k State)

/-- The global gates: the situations, as chains of conjunctions, and the attributes, as chains of
disjunctions over the situations. -/
inductive GlobLoc (k : ℕ) (State : Type) [Fintype State] where
  /-- The conjunction of the first `i + 1` conditions of situation number `j`. -/
  | sit (j : Fin (numSit k State)) (i : Fin (k + 1))
  /-- The disjunction of the first `j` situations having the attribute `v`. -/
  | attr (v : Attr k State) (j : Fin (numSit k State + 1))
  deriving DecidableEq, Fintype

/-- The position of a gate within its block: a gate of the scan, a global gate, or one of the
sixteen gates computing a feature from its terms (the conjunction `false` and the running
disjunction `true` of term `j`). -/
inductive Loc (k : ℕ) (State : Type) [Fintype State] where
  /-- A gate of the scan. -/
  | scan (l : ScanLoc k)
  /-- A global gate. -/
  | glob (l : GlobLoc k State)
  /-- A gate computing a global feature. -/
  | gf (f : GFeat State) (b : Bool) (j : Fin 8)
  /-- A gate computing a column feature. -/
  | col (f : ColFeat k) (b : Bool) (j : Fin 8)
  deriving DecidableEq, Fintype

/-! ### References to wires -/

/-- The column of a reference, relative to the column `c` of the gate: `c`, `c - 1`, `c + 1`, or
the last column. -/
inductive ColSel where
  /-- The column `c`. -/
  | same
  /-- The column `c - 1`. -/
  | prev
  /-- The column `c + 1`. -/
  | next
  /-- The last column. -/
  | last
  deriving DecidableEq

instance : Fintype ColSel where
  elems := {.same, .prev, .next, .last}
  complete x := by cases x <;> simp

/-- A condition on the column `c` of a gate, under which a reference is used; otherwise it reads
`false`. -/
inductive Guard where
  /-- Always. -/
  | always
  /-- `1 ≤ c`. -/
  | pos
  /-- `c` is not the last column. -/
  | ltLast
  /-- `1 ≤ c ≤ n`: the column holds an input bit. -/
  | inRange
  /-- The column holds no input bit. -/
  | outRange
  /-- `c = 0`. -/
  | isZero
  /-- `c = n + 1`. -/
  | isEnd
  /-- `1 ≤ c ≤ n + 1`. -/
  | leEnd
  deriving DecidableEq

instance : Fintype Guard where
  elems := {.always, .pos, .ltLast, .inRange, .outRange, .isZero, .isEnd, .leEnd}
  complete x := by cases x <;> simp

/-- A reference to a wire, relative to the block and the column of the gate: the constant wires,
the input bit of the column, or a position of the current or the previous block. -/
inductive Ref (k : ℕ) (State : Type) [Fintype State] where
  /-- The constant `false`. -/
  | fls
  /-- The constant `true`. -/
  | tru
  /-- The input bit of the column, if it holds one. -/
  | inp
  /-- The position `l` of the previous block (`prev = true`) or the current one, in the column
  selected by `cs`, under the guard `g`. -/
  | node (prev : Bool) (l : Loc k State) (cs : ColSel) (g : Guard)
  deriving DecidableEq

variable {k : ℕ} {State : Type} [Fintype State]

/-- References as data. -/
def Ref.toData : Ref k State → Option (Option (Option (Bool × Loc k State × ColSel × Guard)))
  | .fls => none
  | .tru => some none
  | .inp => some (some none)
  | .node p l cs g => some (some (some (p, l, cs, g)))

instance : Finite (Ref k State) :=
  Finite.of_injective Ref.toData fun a b h => by cases a <;> cases b <;> simp_all [Ref.toData]

/-- A column feature of the previous block, in the column selected by `cs`, under the guard `g`. -/
def colF (f : ColFeat k) (cs : ColSel) (g : Guard) : Ref k State := .node true (.col f true 7) cs g

/-- A global feature of the previous block. -/
def gfF (f : GFeat State) : Ref k State := .node true (.gf f true 7) .same .always

/-- The attribute `v` of the action of the current step. -/
def act (v : Attr k State) : Ref k State :=
  .node false (.glob (.attr v (Fin.last _))) .same .always

/-- The previous configuration has halted. -/
abbrev halted : Ref k State := gfF (.state none)

/-- A gate of the scan of the current block. -/
def scanAt (l : ScanLoc k) (cs : ColSel) (g : Guard) : Ref k State := .node false (.scan l) cs g

/-! ### The layout -/

/-- The number of a cell symbol: blank, `false`, `true`. -/
def symIdx : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

/-- The number of a scanned quantity. -/
def ScanQ.idx : ScanQ k → ℕ
  | .inRead s => symIdx s
  | .read i s => 3 + 3 * i + symIdx s

/-- The position of a gate within a column of the scan. -/
def ScanLoc.idx : ScanLoc k → ℕ
  | .nh i => i
  | .nx => k
  | .term q => k + 1 + 2 * q.idx
  | .acc q => k + 2 + 2 * q.idx

/-- The number of gates of a column of the scan. -/
def scanWidth (k : ℕ) : ℕ := 7 + 7 * k

/-- The number of an attribute. -/
noncomputable def attrIdx (v : Attr k State) : ℕ := Fintype.equivFin (Attr k State) v

/-- The position of a global gate. -/
noncomputable def GlobLoc.idx : GlobLoc k State → ℕ
  | .sit j i => j * (k + 1) + i
  | .attr v j => numSit k State * (k + 1) + attrIdx v * (numSit k State + 1) + j

/-- The number of global gates. -/
noncomputable def globWidth (k : ℕ) (State : Type) [Fintype State] : ℕ :=
  numSit k State * (k + 1) + Fintype.card (Attr k State) * (numSit k State + 1)

/-- The number of a global feature. -/
noncomputable def GFeat.idx : GFeat State → ℕ
  | .state q => Fintype.equivFin (Option State) q
  | .out o => Fintype.card (Option State) + o.index

/-- The number of a column feature. -/
def ColFeat.idx : ColFeat k → ℕ
  | .inPos => 0
  | .head i => 1 + i
  | .cell i s => 1 + k + 3 * i + symIdx s

/-- The position of gate `j` of kind `b` within the sixteen gates computing feature number `fi`. -/
def gadgetIdx (fi : ℕ) (b : Bool) (j : Fin 8) : ℕ := 16 * fi + 8 * b.toNat + j

/-- The number of gates computing the global features. -/
def gfWidth (State : Type) [Fintype State] : ℕ := 16 * (Fintype.card (Option State) + 4)

/-- The number of gates computing the features of a column. -/
def colWidth (k : ℕ) : ℕ := 16 * (1 + 4 * k)

/-- The number of columns: the work cells `-T, …, T`. -/
def numCols (T : ℕ) : ℕ := 2 * T + 1

/-- The start of the global gates within a block. -/
def globStart (k T : ℕ) : ℕ := numCols T * scanWidth k

/-- The start of the global features within a block. -/
noncomputable def gfStart (k : ℕ) (State : Type) [Fintype State] (T : ℕ) : ℕ :=
  globStart k T + globWidth k State

/-- The start of the column features within a block. -/
noncomputable def colStart (k : ℕ) (State : Type) [Fintype State] (T : ℕ) : ℕ :=
  gfStart k State T + gfWidth State

/-- The number of gates of a block. -/
noncomputable def blockSize (k : ℕ) (State : Type) [Fintype State] (T : ℕ) : ℕ :=
  colStart k State T + numCols T * colWidth k

/-- The offset of a position in column `c` from the start of its block. -/
noncomputable def Loc.offset (T c : ℕ) : Loc k State → ℕ
  | .scan l => c * scanWidth k + l.idx
  | .glob l => globStart k T + l.idx
  | .gf f b j => gfStart k State T + gadgetIdx f.idx b j
  | .col f b j => colStart k State T + c * colWidth k + gadgetIdx f.idx b j

/-- **The wire of a position** `l` of block `t`, in column `c`: the inputs come first, then the
two constants, then the blocks. -/
noncomputable def wire (n T t : ℕ) (l : Loc k State) (c : ℕ) : ℕ :=
  n + 2 + t * blockSize k State T + l.offset T c

/-- Whether a guard holds in column `c`. -/
def Guard.test (n T c : ℕ) : Guard → Bool
  | .always => true
  | .pos => decide (1 ≤ c)
  | .ltLast => decide (c + 1 < numCols T)
  | .inRange => decide (1 ≤ c ∧ c ≤ n)
  | .outRange => !decide (1 ≤ c ∧ c ≤ n)
  | .isZero => decide (c = 0)
  | .isEnd => decide (c = n + 1)
  | .leEnd => decide (1 ≤ c ∧ c ≤ n + 1)

/-- The column selected relative to column `c`. -/
def ColSel.apply (T c : ℕ) : ColSel → ℕ
  | .same => c
  | .prev => c - 1
  | .next => c + 1
  | .last => 2 * T

/-- **The wire of a reference** from block `t` and column `c`. -/
noncomputable def Ref.resolve (n T t c : ℕ) : Ref k State → ℕ
  | .fls => n
  | .tru => n + 1
  | .inp => if 1 ≤ c ∧ c ≤ n then c - 1 else n
  | .node p l cs g => if g.test n T c then wire n T (if p then t - 1 else t) l (cs.apply T c) else n

/-- The arguments of a gate with operation `op`, from its two candidate wires. -/
def argsOf (op : Op) (a b : ℕ) : List ℕ :=
  match op with
  | .const _ => []
  | .not => [a]
  | .and => [a, b]
  | .or => [a, b]

/-! ### Decoding positions -/

/-- The cell symbol with a number. -/
def symOf (m : ℕ) : Option Bool := if m = 0 then none else if m = 1 then some false else some true

/-- The scanned quantity with a number. -/
def ScanQ.ofIdx (m : ℕ) : ScanQ k :=
  if m < 3 then .inRead (symOf m)
  else if h : (m - 3) / 3 < k then .read ⟨(m - 3) / 3, h⟩ (symOf ((m - 3) % 3)) else .inRead none

/-- The gate of the scan at a position within a column. -/
def ScanLoc.ofIdx (m : ℕ) : ScanLoc k :=
  if h : m < k then .nh ⟨m, h⟩
  else if m = k then .nx
  else if (m - (k + 1)) % 2 = 0 then .term (ScanQ.ofIdx ((m - (k + 1)) / 2))
  else .acc (ScanQ.ofIdx ((m - (k + 1)) / 2))

/-- The global gate at a position. -/
noncomputable def GlobLoc.ofIdx (m : ℕ) : GlobLoc k State :=
  if h : m < numSit k State * (k + 1) then
    .sit ⟨m / (k + 1), Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h)⟩
      ⟨m % (k + 1), Nat.mod_lt _ (Nat.succ_pos k)⟩
  else if h' : (m - numSit k State * (k + 1)) / (numSit k State + 1) <
      Fintype.card (Attr k State) then
    .attr ((Fintype.equivFin (Attr k State)).symm
        ⟨(m - numSit k State * (k + 1)) / (numSit k State + 1), h'⟩)
      ⟨(m - numSit k State * (k + 1)) % (numSit k State + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  else .attr (.inMove 0) 0

/-- The output view with a number. -/
def outViewOf (m : ℕ) : OutView :=
  if m = 0 then .empty else if m = 1 then .one false else if m = 2 then .one true else .many

/-- The global feature with a number. -/
noncomputable def GFeat.ofIdx (m : ℕ) : GFeat State :=
  if h : m < Fintype.card (Option State) then
    .state ((Fintype.equivFin (Option State)).symm ⟨m, h⟩)
  else .out (outViewOf (m - Fintype.card (Option State)))

/-- The column feature with a number. -/
def ColFeat.ofIdx (m : ℕ) : ColFeat k :=
  if m = 0 then .inPos
  else if h : m - 1 < k then .head ⟨m - 1, h⟩
  else if h' : (m - 1 - k) / 3 < k then .cell ⟨(m - 1 - k) / 3, h'⟩ (symOf ((m - 1 - k) % 3))
  else .inPos

/-- The kind of the gate at a position within the gates of a feature. -/
def gadgetB (m : ℕ) : Bool := decide (8 ≤ m % 16)

/-- The term of the gate at a position within the gates of a feature. -/
def gadgetJ (m : ℕ) : Fin 8 := ⟨m % 8, Nat.mod_lt _ (by norm_num)⟩

/-! ### Decoding inverts the layout -/

private theorem symOf_symIdx (s : Option Bool) : symOf (symIdx s) = s := by
  rcases s with _ | _ | _ <;> rfl

private theorem symIdx_lt (s : Option Bool) : symIdx s < 3 := by
  rcases s with _ | _ | _ <;> simp [symIdx]

private theorem ScanQ.ofIdx_idx (q : ScanQ k) : ScanQ.ofIdx q.idx = q := by
  rcases q with s | ⟨i, s⟩
  · simp [ScanQ.idx, ScanQ.ofIdx, symIdx_lt, symOf_symIdx]
  · have hs := symIdx_lt s
    have h₁ : (3 + 3 * (i : ℕ) + symIdx s - 3) / 3 = i := by omega
    have h₂ : (3 + 3 * (i : ℕ) + symIdx s - 3) % 3 = symIdx s := by omega
    simp only [ScanQ.idx, ScanQ.ofIdx, show ¬3 + 3 * (i : ℕ) + symIdx s < 3 by omega,
      ↓reduceIte, h₁, i.isLt, ↓reduceDIte, h₂, symOf_symIdx]

private theorem ScanQ.idx_lt (q : ScanQ k) : q.idx < 3 + 3 * k := by
  rcases q with s | ⟨i, s⟩ <;> simp only [ScanQ.idx] <;> have := symIdx_lt s
  · omega
  · have := i.isLt; omega

private theorem ScanLoc.ofIdx_idx (l : ScanLoc k) : ScanLoc.ofIdx l.idx = l := by
  rcases l with i | _ | q | q
  · simp [ScanLoc.idx, ScanLoc.ofIdx]
  · simp [ScanLoc.idx, ScanLoc.ofIdx]
  · simp only [ScanLoc.idx, ScanLoc.ofIdx, show ¬k + 1 + 2 * q.idx < k by omega,
      show k + 1 + 2 * q.idx ≠ k by omega, ↓reduceDIte, ↓reduceIte,
      show (k + 1 + 2 * q.idx - (k + 1)) % 2 = 0 by omega,
      show (k + 1 + 2 * q.idx - (k + 1)) / 2 = q.idx by omega, ScanQ.ofIdx_idx]
  · simp only [ScanLoc.idx, ScanLoc.ofIdx, show ¬k + 2 + 2 * q.idx < k by omega,
      show k + 2 + 2 * q.idx ≠ k by omega, ↓reduceDIte, ↓reduceIte,
      show (k + 2 + 2 * q.idx - (k + 1)) % 2 = 1 by omega,
      show (k + 2 + 2 * q.idx - (k + 1)) / 2 = q.idx by omega, ScanQ.ofIdx_idx]
    rfl

private theorem ScanLoc.idx_lt (l : ScanLoc k) : l.idx < scanWidth k := by
  rcases l with i | _ | q | q <;> simp only [ScanLoc.idx, scanWidth]
  · have := i.isLt; omega
  · omega
  · have := q.idx_lt; omega
  · have := q.idx_lt; omega

private theorem attrIdx_lt (v : Attr k State) : attrIdx v < Fintype.card (Attr k State) :=
  (Fintype.equivFin (Attr k State) v).isLt

private theorem GlobLoc.idx_lt (l : GlobLoc k State) : l.idx < globWidth k State := by
  rcases l with ⟨j, i⟩ | ⟨v, j⟩ <;> simp only [GlobLoc.idx, globWidth]
  · have := j.isLt
    have := i.isLt
    have : (j : ℕ) * (k + 1) + i < (j + 1) * (k + 1) := by rw [Nat.succ_mul]; omega
    have : ((j : ℕ) + 1) * (k + 1) ≤ numSit k State * (k + 1) := Nat.mul_le_mul_right _ ‹_›
    omega
  · have h₁ := j.isLt
    have h₂ := attrIdx_lt v
    have : attrIdx v * (numSit k State + 1) + j < (attrIdx v + 1) * (numSit k State + 1) := by
      rw [Nat.succ_mul]; omega
    have : (attrIdx v + 1) * (numSit k State + 1) ≤
        Fintype.card (Attr k State) * (numSit k State + 1) := Nat.mul_le_mul_right _ h₂
    omega

private theorem GlobLoc.ofIdx_idx (l : GlobLoc k State) : GlobLoc.ofIdx l.idx = l := by
  rcases l with ⟨j, i⟩ | ⟨v, j⟩
  · have hlt : (j : ℕ) * (k + 1) + i < numSit k State * (k + 1) := by
      have := (GlobLoc.sit (State := State) j i).idx_lt
      have : (j : ℕ) * (k + 1) + i < (j + 1) * (k + 1) := by rw [Nat.succ_mul]; omega
      have : ((j : ℕ) + 1) * (k + 1) ≤ numSit k State * (k + 1) :=
        Nat.mul_le_mul_right _ j.isLt
      omega
    simp only [GlobLoc.idx, GlobLoc.ofIdx, hlt, ↓reduceDIte, GlobLoc.sit.injEq]
    constructor <;> ext
    · simp [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos k), Nat.div_eq_of_lt i.isLt]
    · simp [Nat.add_comm, Nat.mod_eq_of_lt i.isLt]
  · have hm : ¬ numSit k State * (k + 1) + attrIdx v * (numSit k State + 1) + j <
        numSit k State * (k + 1) := by omega
    have h₁ : (numSit k State * (k + 1) + attrIdx v * (numSit k State + 1) + j -
        numSit k State * (k + 1)) / (numSit k State + 1) = attrIdx v := by
      rw [show numSit k State * (k + 1) + attrIdx v * (numSit k State + 1) + j -
        numSit k State * (k + 1) = j + attrIdx v * (numSit k State + 1) by omega,
        Nat.add_mul_div_right _ _ (Nat.succ_pos _), Nat.div_eq_of_lt j.isLt, Nat.zero_add]
    have h₂ : (numSit k State * (k + 1) + attrIdx v * (numSit k State + 1) + j -
        numSit k State * (k + 1)) % (numSit k State + 1) = j := by
      rw [show numSit k State * (k + 1) + attrIdx v * (numSit k State + 1) + j -
        numSit k State * (k + 1) = j + attrIdx v * (numSit k State + 1) by omega,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
    simp only [GlobLoc.idx, GlobLoc.ofIdx, hm, ↓reduceDIte, h₁, attrIdx_lt v, h₂]
    congr
    exact (Fintype.equivFin (Attr k State)).symm_apply_apply v

private theorem GFeat.idx_lt (f : GFeat State) : f.idx < Fintype.card (Option State) + 4 := by
  rcases f with q | o
  · have := (Fintype.equivFin (Option State) q).isLt
    simp only [GFeat.idx]
    omega
  · rcases o with _ | (_ | _) | _ <;> simp [GFeat.idx, OutView.index]

private theorem GFeat.ofIdx_idx (f : GFeat State) : GFeat.ofIdx f.idx = f := by
  rcases f with q | o
  · simp only [GFeat.idx, GFeat.ofIdx, Fin.is_lt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]
  · rw [GFeat.ofIdx]
    split_ifs with h
    · exact absurd h (by simp only [GFeat.idx]; omega)
    · rcases o with _ | (_ | _) | _ <;> simp [GFeat.idx, OutView.index, outViewOf]

private theorem ColFeat.idx_lt (f : ColFeat k) : f.idx < 1 + 4 * k := by
  rcases f with _ | i | ⟨i, s⟩ <;> simp only [ColFeat.idx]
  · omega
  · have := i.isLt; omega
  · have := i.isLt; have := symIdx_lt s; omega

private theorem ColFeat.ofIdx_idx (f : ColFeat k) : ColFeat.ofIdx f.idx = f := by
  rcases f with _ | i | ⟨i, s⟩
  · rfl
  · simp [ColFeat.idx, ColFeat.ofIdx]
  · have hs := symIdx_lt s
    have h₁ : (1 + k + 3 * (i : ℕ) + symIdx s - 1 - k) / 3 = i := by omega
    have h₂ : (1 + k + 3 * (i : ℕ) + symIdx s - 1 - k) % 3 = symIdx s := by omega
    simp only [ColFeat.idx, ColFeat.ofIdx, show 1 + k + 3 * (i : ℕ) + symIdx s ≠ 0 by omega,
      show ¬1 + k + 3 * (i : ℕ) + symIdx s - 1 < k by omega, ↓reduceIte, ↓reduceDIte, h₁,
      i.isLt, h₂, symOf_symIdx]

private theorem gadgetIdx_lt (fi : ℕ) (b : Bool) (j : Fin 8) : gadgetIdx fi b j < 16 * (fi + 1) :=
    by
  have := j.isLt
  cases b <;>
    simp only [gadgetIdx, Bool.toNat_false, Bool.toNat_true, mul_zero, mul_one, add_zero,
      gt_iff_lt] <;> omega

private theorem gadgetIdx_div (fi : ℕ) (b : Bool) (j : Fin 8) : gadgetIdx fi b j / 16 = fi := by
  have := j.isLt
  cases b <;>
    simp only [gadgetIdx, Bool.toNat_false, Bool.toNat_true, mul_zero, mul_one, add_zero] <;> omega

private theorem gadgetB_gadgetIdx (fi : ℕ) (b : Bool) (j : Fin 8) : gadgetB (gadgetIdx fi b j) = b
    := by
  have := j.isLt
  cases b <;>
    simp only [gadgetB, gadgetIdx, Bool.toNat_false, Bool.toNat_true, mul_zero, mul_one, add_zero,
      Nat.mul_add_mod_self_left, decide_eq_false_iff_not, decide_eq_true_eq, not_le, ge_iff_le,
      gt_iff_lt] <;> omega

private theorem gadgetJ_gadgetIdx (fi : ℕ) (b : Bool) (j : Fin 8) : gadgetJ (gadgetIdx fi b j) = j
    := by
  have := j.isLt
  ext
  cases b <;>
    simp only [gadgetJ, gadgetIdx, Bool.toNat_false, Bool.toNat_true, mul_zero, mul_one,
      add_zero] <;> omega

/-! ### The gates -/

variable [DecidableEq State]

/-- Whether an action has an attribute. -/
def Attr.test (a : Action k Bool State) : Attr k State → Bool
  | .state q => decide (a.state = q)
  | .inMove m => decide (a.inputTape = m)
  | .write i w => decide ((a.workTapes i).1 = w)
  | .move i m => decide ((a.workTapes i).2 = m)
  | .out e => decide (a.output = e)

/-- The situation with number `j`. -/
noncomputable def sitOf (j : Fin (numSit k State)) : Situation k State :=
  (Fintype.equivFin (Situation k State)).symm j

/-- The two wires of the contribution of a column to a scanned quantity. -/
def scanTerm : ScanQ k → Ref k State × Ref k State
  | .inRead none => (colF .inPos .same .outRange, .tru)
  | .inRead (some true) => (colF .inPos .same .always, .inp)
  | .inRead (some false) => (colF .inPos .same .inRange, scanAt .nx .same .always)
  | .read i s => (colF (.head i) .same .always, colF (.cell i s) .same .always)

/-- The terms of a global feature at the next time: the feature holds after the step exactly when
both wires of one term are true. -/
def gfTerms : GFeat State → List (Ref k State × Ref k State)
  | .state none => [(halted, .tru), (act (.state none), .tru)]
  | .state (some q) => [(act (.state (some q)), .tru)]
  | .out .empty => [(halted, gfF (.out .empty)), (act (.out none), gfF (.out .empty))]
  | .out (.one b) => [(halted, gfF (.out (.one b))), (act (.out none), gfF (.out (.one b))),
      (act (.out (some b)), gfF (.out .empty))]
  | .out .many => [(halted, gfF (.out .many)), (act (.out none), gfF (.out .many)),
      (act (.out (some false)), gfF (.out (.one false))),
      (act (.out (some false)), gfF (.out (.one true))),
      (act (.out (some false)), gfF (.out .many)),
      (act (.out (some true)), gfF (.out (.one false))),
      (act (.out (some true)), gfF (.out (.one true))),
      (act (.out (some true)), gfF (.out .many))]

/-- The terms of a column feature at the next time. -/
def colTerms : ColFeat k → List (Ref k State × Ref k State)
  | .inPos => [(halted, colF .inPos .same .always),
      (act (.inMove 0), colF .inPos .same .always),
      (act (.inMove 1), colF .inPos .prev .leEnd),
      (act (.inMove (-1)), colF .inPos .next .ltLast),
      (act (.inMove (-1)), colF .inPos .same .isZero),
      (act (.inMove 1), colF .inPos .same .isEnd)]
  | .head i => [(halted, colF (.head i) .same .always),
      (act (.move i 0), colF (.head i) .same .always),
      (act (.move i 1), colF (.head i) .prev .pos),
      (act (.move i (-1)), colF (.head i) .next .ltLast)]
  | .cell i s => [(halted, colF (.cell i s) .same .always),
      (act (.write i none), colF (.cell i s) .same .always),
      (scanAt (.nh i) .same .always, colF (.cell i s) .same .always),
      (colF (.head i) .same .always, act (.write i (some s)))]

variable (tm : MultiTapeTM k Bool State)

/-- **The gate at each position of a block** after the first, with symbolic references to its
wires. -/
noncomputable def table : Loc k State → Op × Ref k State × Ref k State
  | .scan (.nh i) => (.not, colF (.head i) .same .always, .fls)
  | .scan .nx => (.not, .inp, .fls)
  | .scan (.term q) => (.and, scanTerm q)
  | .scan (.acc q) => (.or, scanAt (.acc q) .prev .pos, scanAt (.term q) .same .always)
  | .glob (.sit j i) =>
    (.and, Fin.cases (motive := fun _ => Ref k State) (gfF (.state (some (sitOf j).1)))
        (fun i' => .node false (.glob (.sit j i'.castSucc)) .same .always) i,
      Fin.cases (motive := fun _ => Ref k State)
        (scanAt (.acc (.inRead (sitOf j).2.1)) .last .always)
        (fun i' => scanAt (.acc (.read i' ((sitOf j).2.2 i'))) .last .always) i)
  | .glob (.attr v j) =>
    (.or, Fin.cases (motive := fun _ => Ref k State) .fls
        (fun j' => .node false (.glob (.attr v j'.castSucc)) .same .always) j,
      Fin.cases (motive := fun _ => Ref k State) .fls
        (fun j' => if v.test (tm.actionOf (sitOf j')) then
          .node false (.glob (.sit j' (Fin.last k))) .same .always else .fls) j)
  | .gf f false j => (.and, (gfTerms f).getD j (.fls, .fls))
  | .gf f true j =>
    (.or, Fin.cases (motive := fun _ => Ref k State) .fls
        (fun j' => .node false (.gf f true j'.castSucc) .same .always) j,
      .node false (.gf f false j) .same .always)
  | .col f false j => (.and, (colTerms f).getD j (.fls, .fls))
  | .col f true j =>
    (.or, Fin.cases (motive := fun _ => Ref k State) .fls
        (fun j' => .node false (.col f true j'.castSucc) .same .always) j,
      .node false (.col f false j) .same .always)

/-- The value of a global feature in the initial configuration. -/
def gfInit : GFeat State → Bool
  | .state q => decide (q = some tm.q₀)
  | .out o => decide (o = .empty)

/-- The value of a column feature in the initial configuration, for the column `c` of `2 T + 1`:
the input head on the first input cell, the work heads on cell `0`, the work cells blank. -/
def colInit (T c : ℕ) : ColFeat k → Bool
  | .inPos => decide (c = 1)
  | .head _ => decide (c = T)
  | .cell _ s => decide (s = none)

/-- The constant at each position of the first block: the initial value of a feature at the last
gate of its gadget, `false` elsewhere. -/
def initBit (T c : ℕ) : Loc k State → Bool
  | .gf f true j => decide (j = 7) && gfInit tm f
  | .col f true j => decide (j = 7) && colInit T c f
  | _ => false

/-- The gate at the position `l` of block `t`, in column `c`. -/
noncomputable def gateAt (n T t c : ℕ) (l : Loc k State) : Op × List ℕ :=
  if t = 0 then (.const (initBit tm T c l), [])
  else ((table tm l).1, argsOf (table tm l).1 ((table tm l).2.1.resolve n T t c)
    ((table tm l).2.2.resolve n T t c))

/-- **The gate with number `g`** of the tableau of `tm` for `T` steps on inputs of length `n`:
gates `0` and `1` are the constants `false` and `true`, and gate `2 + t * B + r` is the gate at
offset `r` of block `t`, for blocks of `B` gates. -/
noncomputable def gateCode (n T g : ℕ) : Op × List ℕ :=
  if g < 2 then (.const (decide (g = 1)), [])
  else
    let t := (g - 2) / blockSize k State T
    let r := (g - 2) % blockSize k State T
    if r < globStart k T then
      gateAt tm n T t (r / scanWidth k) (.scan (ScanLoc.ofIdx (r % scanWidth k)))
    else if r < gfStart k State T then
      gateAt tm n T t 0 (.glob (GlobLoc.ofIdx (r - globStart k T)))
    else if r < colStart k State T then
      gateAt tm n T t 0 (.gf (GFeat.ofIdx ((r - gfStart k State T) / 16))
        (gadgetB (r - gfStart k State T)) (gadgetJ (r - gfStart k State T)))
    else
      gateAt tm n T t ((r - colStart k State T) / colWidth k)
        (.col (ColFeat.ofIdx ((r - colStart k State T) % colWidth k / 16))
          (gadgetB ((r - colStart k State T) % colWidth k))
          (gadgetJ ((r - colStart k State T) % colWidth k)))

/-- The number of gates of the tableau: the two constants and `T + 1` blocks. -/
noncomputable def numGates (k : ℕ) (State : Type) [Fintype State] (T : ℕ) : ℕ :=
  2 + (T + 1) * blockSize k State T

/-- **The gate list of the tableau** of `tm` for `T` steps on inputs of length `n`. -/
noncomputable def gates (n T : ℕ) : List (Op × List ℕ) :=
  (List.range (numGates k State T)).map (gateCode tm n T)

/-- **The output wire of the tableau**: the output has the view `[true]` at time `T`. -/
noncomputable def outWire (k : ℕ) (State : Type) [Fintype State] (n T : ℕ) : ℕ :=
  wire (k := k) (State := State) n T T (.gf (.out (.one true)) true 7) 0

/-! ### Gates at their wires -/

variable {T : ℕ}

/-- The column `c` is admissible for the position `l`: a column of the window for a gate of the
scan or a column feature, and `0` for a global gate. -/
def Loc.ColOK (T c : ℕ) : Loc k State → Prop
  | .scan _ => c < numCols T
  | .col _ _ _ => c < numCols T
  | .glob _ => c = 0
  | .gf _ _ _ => c = 0

private theorem mul_add_lt_mul {c w W i : ℕ} (hc : c < W) (hi : i < w) : c * w + i < W * w :=
  calc c * w + i < (c + 1) * w := by rw [Nat.succ_mul]; omega
    _ ≤ W * w := Nat.mul_le_mul_right _ hc

omit [DecidableEq State] in
private theorem gfStart_add_gadgetIdx_lt (f : GFeat State) (b : Bool) (j : Fin 8) :
    gfStart k State T + gadgetIdx f.idx b j < colStart k State T := by
  have h₁ := gadgetIdx_lt f.idx b j
  have h₂ := f.idx_lt
  simp only [colStart, gfWidth]
  omega

omit [DecidableEq State] in
private theorem colStart_add_lt {c : ℕ} (hc : c < numCols T) (f : ColFeat k) (b : Bool) (j : Fin 8)
    :
    colStart k State T + c * colWidth k + gadgetIdx f.idx b j < blockSize k State T := by
  have h₁ := gadgetIdx_lt f.idx b j
  have h₂ := f.idx_lt
  have : gadgetIdx f.idx b j < colWidth k := by simp only [colWidth]; omega
  have := mul_add_lt_mul hc this
  simp only [blockSize]
  omega

omit [DecidableEq State] in
/-- A position lies within its block. -/
theorem Loc.offset_lt {l : Loc k State} {c : ℕ} (hl : l.ColOK T c) :
    l.offset T c < blockSize k State T := by
  have hgs : globStart k T ≤ gfStart k State T := Nat.le_add_right _ _
  have hgc : gfStart k State T ≤ colStart k State T := Nat.le_add_right _ _
  have hcb : colStart k State T ≤ blockSize k State T := Nat.le_add_right _ _
  rcases l with l | l | ⟨f, b, j⟩ | ⟨f, b, j⟩ <;> simp only [Loc.offset] <;>
    simp only [Loc.ColOK] at hl
  · have := mul_add_lt_mul hl l.idx_lt
    simp only [globStart] at hgs
    omega
  · have := l.idx_lt
    simp only [gfStart] at hgc
    omega
  · have := gfStart_add_gadgetIdx_lt (k := k) (T := T) f b j
    omega
  · exact colStart_add_lt hl f b j

omit [DecidableEq State] in
theorem wire_sub (n T t : ℕ) (l : Loc k State) (c : ℕ) :
    wire n T t l c - n = 2 + t * blockSize k State T + l.offset T c := by
  simp only [wire]
  omega

omit [DecidableEq State] in
private theorem div_mod_wire {n T t : ℕ} {l : Loc k State} {c : ℕ} (hl : l.ColOK T c) :
    (wire n T t l c - n - 2) / blockSize k State T = t ∧
      (wire n T t l c - n - 2) % blockSize k State T = l.offset T c := by
  have h := Loc.offset_lt hl
  rw [wire_sub, show 2 + t * blockSize k State T + l.offset T c - 2 =
    l.offset T c + t * blockSize k State T by omega]
  exact ⟨by rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h, Nat.zero_add],
    by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]⟩

/-- **The gate at a wire** is the gate of its position. -/
theorem gateCode_wire {n T t : ℕ} {l : Loc k State} {c : ℕ} (hl : l.ColOK T c) :
    gateCode tm n T (wire n T t l c - n) = gateAt tm n T t c l := by
  obtain ⟨hdiv, hmod⟩ := div_mod_wire (n := n) (t := t) hl
  have h2 : ¬ wire n T t l c - n < 2 := by rw [wire_sub]; omega
  rw [gateCode, ite_eq_right h2]
  simp only [hdiv, hmod]
  have hgs : globStart k T ≤ gfStart k State T := Nat.le_add_right _ _
  have hgc : gfStart k State T ≤ colStart k State T := Nat.le_add_right _ _
  rcases l with l | l | ⟨f, b, j⟩ | ⟨f, b, j⟩ <;> simp only [Loc.ColOK] at hl <;>
    simp only [Loc.offset]
  · have hi := l.idx_lt
    have hlt := mul_add_lt_mul hl hi
    have hw : 0 < scanWidth k := by simp only [scanWidth]; omega
    have h₁ : c * scanWidth k + l.idx < globStart k T := by simpa only [globStart] using hlt
    have h₂ : (c * scanWidth k + l.idx) / scanWidth k = c := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hi, Nat.zero_add]
    have h₃ : (c * scanWidth k + l.idx) % scanWidth k = l.idx := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
    simp only [h₁, ↓reduceIte, h₂, h₃, ScanLoc.ofIdx_idx]
  · have hi := l.idx_lt
    subst hl
    have h₁ : ¬ globStart k T + l.idx < globStart k T := by omega
    have h₂ : globStart k T + l.idx < gfStart k State T := by simp only [gfStart]; omega
    simp only [h₁, h₂, ↓reduceIte, Nat.add_sub_cancel_left, GlobLoc.ofIdx_idx]
  · subst hl
    have := gfStart_add_gadgetIdx_lt (k := k) (T := T) f b j
    have h₁ : ¬ gfStart k State T + gadgetIdx f.idx b j < globStart k T := by omega
    have h₂ : ¬ gfStart k State T + gadgetIdx f.idx b j < gfStart k State T := by omega
    simp only [h₁, h₂, this, ↓reduceIte, Nat.add_sub_cancel_left, gadgetIdx_div,
      GFeat.ofIdx_idx, gadgetB_gadgetIdx, gadgetJ_gadgetIdx]
  · have h₁ := gadgetIdx_lt f.idx b j
    have h₂ := f.idx_lt
    have hw : gadgetIdx f.idx b j < colWidth k := by simp only [colWidth]; omega
    have hw0 : 0 < colWidth k := by simp only [colWidth]; omega
    have h₃ : ¬ colStart k State T + c * colWidth k + gadgetIdx f.idx b j < globStart k T := by
      omega
    have h₄ : ¬ colStart k State T + c * colWidth k + gadgetIdx f.idx b j < gfStart k State T := by
      omega
    have h₅ : ¬ colStart k State T + c * colWidth k + gadgetIdx f.idx b j <
        colStart k State T := by omega
    have h₆ : colStart k State T + c * colWidth k + gadgetIdx f.idx b j - colStart k State T =
        gadgetIdx f.idx b j + c * colWidth k := by omega
    have h₇ : (gadgetIdx f.idx b j + c * colWidth k) / colWidth k = c := by
      rw [Nat.add_mul_div_right _ _ hw0, Nat.div_eq_of_lt hw, Nat.zero_add]
    have h₈ : (gadgetIdx f.idx b j + c * colWidth k) % colWidth k = gadgetIdx f.idx b j := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hw]
    simp only [h₃, h₄, h₅, ↓reduceIte, h₆, h₇, h₈, gadgetIdx_div, ColFeat.ofIdx_idx,
      gadgetB_gadgetIdx, gadgetJ_gadgetIdx]

/-! ### Well-formedness -/

omit [DecidableEq State] in
/-- Every position lies within its block, for a column of the window. -/
private theorem Loc.offset_lt_of_lt {l : Loc k State} {c : ℕ} (hc : c < numCols T) :
    l.offset T c < blockSize k State T := by
  rcases l with l | l | ⟨f, b, j⟩ | ⟨f, b, j⟩
  · exact Loc.offset_lt (l := .scan l) hc
  · exact Loc.offset_lt (l := .glob l) (c := 0) rfl
  · exact Loc.offset_lt (l := .gf f b j) (c := 0) rfl
  · exact Loc.offset_lt (l := .col f b j) hc

omit [DecidableEq State] in
private theorem Loc.ColOK.lt {l : Loc k State} {c : ℕ} (hl : l.ColOK T c) : c < numCols T := by
  rcases l with l | l | ⟨f, b, j⟩ | ⟨f, b, j⟩ <;> simp only [Loc.ColOK] at hl <;>
    first | exact hl | (subst hl; simp [numCols])

section Earlier

variable {n T t c : ℕ} {l : Loc k State}

omit [DecidableEq State] in
private theorem resolve_fls_lt : (Ref.fls : Ref k State).resolve n T t c < wire n T t l c := by
  simp only [Ref.resolve, wire]; omega

omit [DecidableEq State] in
private theorem resolve_tru_lt : (Ref.tru : Ref k State).resolve n T t c < wire n T t l c := by
  simp only [Ref.resolve, wire]; omega

omit [DecidableEq State] in
private theorem resolve_inp_lt : (Ref.inp : Ref k State).resolve n T t c < wire n T t l c := by
  simp only [Ref.resolve, wire]; split_ifs <;> omega

omit [DecidableEq State] in
/-- A reference to the previous block reads an earlier wire. -/
private theorem resolve_prev_lt (ht : 1 ≤ t) {l' : Loc k State} {cs : ColSel} {g : Guard}
    (h : g.test n T c = true → cs.apply T c < numCols T) :
    (Ref.node true l' cs g).resolve n T t c < wire n T t l c := by
  simp only [Ref.resolve, ↓reduceIte]
  split_ifs with hg
  · have := Loc.offset_lt_of_lt (l := l') (h hg)
    simp only [wire]
    have : (t - 1) * blockSize k State T + blockSize k State T = t * blockSize k State T := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel ht]
    omega
  · simp only [wire]; omega

omit [DecidableEq State] in
/-- A reference to an earlier position of the current block reads an earlier wire. -/
private theorem resolve_cur_lt {l' : Loc k State} {cs : ColSel} {g : Guard}
    (h : g.test n T c = true → l'.offset T (cs.apply T c) < l.offset T c) :
    (Ref.node false l' cs g).resolve n T t c < wire n T t l c := by
  simp only [Ref.resolve, Bool.false_eq_true, ↓reduceIte]
  split_ifs with hg
  · have := h hg
    simp only [wire]
    omega
  · simp only [wire]; omega

end Earlier

omit [DecidableEq State] in
theorem scanWidth_pos : 0 < scanWidth k := by simp only [scanWidth]; omega

omit [DecidableEq State] in
private theorem scan_offset_lt_globStart {c : ℕ} (hc : c < numCols T) (l : ScanLoc k) :
    c * scanWidth k + l.idx < globStart k T := mul_add_lt_mul hc l.idx_lt

omit [DecidableEq State] in
private theorem globStart_le_gfStart : globStart k T ≤ gfStart k State T := Nat.le_add_right _ _

omit [DecidableEq State] in
private theorem gfStart_le_colStart : gfStart k State T ≤ colStart k State T := Nat.le_add_right _ _

omit [DecidableEq State] in
private theorem attr_offset_lt (v : Attr k State) (j : Fin (numSit k State + 1)) :
    globStart k T + (GlobLoc.attr v j).idx < gfStart k State T := by
  have := (GlobLoc.attr v j).idx_lt
  simp only [gfStart]
  omega

omit [DecidableEq State] in
/-- The references of a term of a global feature read earlier wires than the gates of the
feature. -/
private theorem gfTerms_lt {n T t : ℕ} (ht : 1 ≤ t) {f : GFeat State} {b : Bool} {j : Fin 8}
    {f' : GFeat State} {p : Ref k State × Ref k State} (hp : p ∈ gfTerms f' ∨ p = (.fls, .fls)) :
    p.1.resolve n T t 0 < wire (k := k) n T t (.gf f b j) 0 ∧
      p.2.resolve n T t 0 < wire (k := k) n T t (.gf f b j) 0 := by
  have hok {r : Ref k State} (hr : r = .tru ∨ r = .fls ∨ (∃ g, gfF g = r) ∨ ∃ v, act v = r) :
      r.resolve n T t 0 < wire (k := k) n T t (.gf f b j) 0 := by
    rcases hr with rfl | rfl | ⟨g, rfl⟩ | ⟨v, rfl⟩
    · exact resolve_tru_lt
    · exact resolve_fls_lt
    · exact resolve_prev_lt ht fun _ => by simp [ColSel.apply, numCols]
    · refine resolve_cur_lt fun _ => ?_
      have := attr_offset_lt (T := T) v (Fin.last _)
      simp only [Loc.offset]
      omega
  rcases hp with hp | rfl
  · rcases f' with (_ | q) | ((_ | _) | _) | _ <;> simp only [gfTerms, List.mem_cons,
      List.not_mem_nil, or_false] at hp <;>
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨hok (by simp), hok (by simp)⟩
  · exact ⟨resolve_fls_lt, resolve_fls_lt⟩

omit [DecidableEq State] in
/-- The references of a term of a column feature read earlier wires than the gates of the
feature. -/
private theorem colTerms_lt {n T t c : ℕ} (ht : 1 ≤ t) (hc : c < numCols T) {f : ColFeat k} {b :
    Bool}
    {j : Fin 8} {f' : ColFeat k} {p : Ref k State × Ref k State}
    (hp : p ∈ colTerms f' ∨ p = (.fls, .fls)) :
    p.1.resolve n T t c < wire (State := State) n T t (.col f b j) c ∧
      p.2.resolve n T t c < wire (State := State) n T t (.col f b j) c := by
  have hcol (g : ColFeat k) (cs : ColSel) (gd : Guard)
      (h : gd.test n T c = true → cs.apply T c < numCols T) :
      (colF g cs gd : Ref k State).resolve n T t c < wire (State := State) n T t (.col f b j) c :=
    resolve_prev_lt ht h
  have hok {r : Ref k State} (hr : r = .tru ∨ r = .fls ∨ (∃ g, gfF g = r) ∨ (∃ v, act v = r) ∨
      (∃ g, colF g .same .always = r) ∨ (∃ g, colF g .prev .pos = r) ∨
      (∃ g, colF g .prev .leEnd = r) ∨ (∃ g, colF g .next .ltLast = r) ∨
      (∃ g, colF g .same .isZero = r) ∨ (∃ g, colF g .same .isEnd = r) ∨
      (∃ i, scanAt (.nh i) .same .always = r)) :
      r.resolve n T t c < wire (State := State) n T t (.col f b j) c := by
    rcases hr with rfl | rfl | ⟨g, rfl⟩ | ⟨v, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ |
      ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨i, rfl⟩
    · exact resolve_tru_lt
    · exact resolve_fls_lt
    · exact resolve_prev_lt ht fun _ => hc
    · refine resolve_cur_lt fun _ => ?_
      have := attr_offset_lt (T := T) v (Fin.last _)
      have := gfStart_le_colStart (k := k) (State := State) (T := T)
      simp only [Loc.offset]
      omega
    · exact hcol g _ _ fun _ => hc
    · exact hcol g _ _ fun _ => by simp only [ColSel.apply]; omega
    · exact hcol g _ _ fun _ => by simp only [ColSel.apply]; omega
    · exact hcol g _ _ fun hg => by
        simpa only [ColSel.apply, Guard.test, decide_eq_true_eq] using hg
    · exact hcol g _ _ fun _ => hc
    · exact hcol g _ _ fun _ => hc
    · refine resolve_cur_lt fun _ => ?_
      have := scan_offset_lt_globStart hc (.nh i)
      have := globStart_le_gfStart (k := k) (State := State) (T := T)
      have := gfStart_le_colStart (k := k) (State := State) (T := T)
      simp only [Loc.offset, ColSel.apply]
      omega
  rcases hp with hp | rfl
  · rcases f' with _ | i | ⟨i, s⟩ <;> simp only [colTerms, List.mem_cons,
      List.not_mem_nil, or_false] at hp <;>
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨hok (by simp), hok (by simp)⟩
  · exact ⟨resolve_fls_lt, resolve_fls_lt⟩

theorem getD_mem_or {α : Type*} (l : List α) (j : ℕ) (d : α) : l.getD j d ∈ l ∨ l.getD j d = d := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : l[j]? with _ | a
  · exact Or.inr rfl
  · exact Or.inl (List.mem_of_getElem? h)

/-- **The references of a gate read earlier wires.** -/
private theorem resolve_table_lt {n T t c : ℕ} (ht : 1 ≤ t) {l : Loc k State} (hl : l.ColOK T c) :
    (table tm l).2.1.resolve n T t c < wire n T t l c ∧
      (table tm l).2.2.resolve n T t c < wire n T t l c := by
  have hc := hl.lt
  have hprevS (g : ColFeat k) :
      (colF g .same .always : Ref k State).resolve n T t c < wire n T t l c :=
    resolve_prev_lt ht fun _ => hc
  have hgs := globStart_le_gfStart (k := k) (State := State) (T := T)
  have hgc := gfStart_le_colStart (k := k) (State := State) (T := T)
  rcases l with l | l | ⟨f, b, j⟩ | ⟨f, b, j⟩
  · rcases l with i | _ | q | q
    · exact ⟨hprevS _, resolve_fls_lt⟩
    · exact ⟨resolve_inp_lt, resolve_fls_lt⟩
    · rcases q with (_ | (_ | _)) | ⟨i, s⟩
      · exact ⟨resolve_prev_lt ht fun _ => hc, resolve_tru_lt⟩
      · refine ⟨resolve_prev_lt ht fun _ => hc, resolve_cur_lt fun _ => ?_⟩
        simp only [Loc.offset, ColSel.apply, ScanLoc.idx, ScanQ.idx, symIdx]
        omega
      · exact ⟨resolve_prev_lt ht fun _ => hc, resolve_inp_lt⟩
      · exact ⟨hprevS _, hprevS _⟩
    · refine ⟨resolve_cur_lt fun hg => ?_, resolve_cur_lt fun _ => ?_⟩
      · simp only [Guard.test, decide_eq_true_eq] at hg
        simp only [Loc.offset, ColSel.apply]
        have : (c - 1) * scanWidth k + scanWidth k = c * scanWidth k := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hg]
        have := scanWidth_pos (k := k)
        omega
      · simp only [Loc.offset, ColSel.apply, ScanLoc.idx]
        omega
  · simp only [Loc.ColOK] at hl
    subst hl
    have hlast (l' : ScanLoc k) (g : GlobLoc k State) :
        (scanAt l' .last .always : Ref k State).resolve n T t 0 < wire n T t (.glob g) 0 :=
      resolve_cur_lt fun _ => by
        have := scan_offset_lt_globStart (k := k) (T := T) (c := 2 * T)
          (by simp [numCols]) l'
        simp only [Loc.offset, ColSel.apply]
        omega
    rcases l with ⟨j, i⟩ | ⟨v, j⟩
    · cases i using Fin.cases with
      | zero =>
        simp only [table, Fin.cases_zero]
        exact ⟨resolve_prev_lt ht fun _ => by simp [ColSel.apply, numCols], hlast _ _⟩
      | succ i =>
        simp only [table, Fin.cases_succ]
        refine ⟨resolve_cur_lt fun _ => ?_, hlast _ _⟩
        simp only [Loc.offset, GlobLoc.idx, Fin.val_castSucc, Fin.val_succ]
        omega
    · cases j using Fin.cases with
      | zero =>
        simp only [table, Fin.cases_zero]
        exact ⟨resolve_fls_lt, resolve_fls_lt⟩
      | succ j =>
        simp only [table, Fin.cases_succ]
        refine ⟨resolve_cur_lt fun _ => ?_, ?_⟩
        · simp only [Loc.offset, GlobLoc.idx, Fin.val_castSucc, Fin.val_succ]
          omega
        · split_ifs
          · refine resolve_cur_lt fun _ => ?_
            have := (GlobLoc.sit (State := State) j (Fin.last k)).idx_lt
            have h₁ : (GlobLoc.sit (State := State) j (Fin.last k)).idx <
                numSit k State * (k + 1) := by
              simp only [GlobLoc.idx, Fin.val_last]
              have : ((j : ℕ) + 1) * (k + 1) ≤ numSit k State * (k + 1) :=
                Nat.mul_le_mul_right _ j.isLt
              rw [Nat.succ_mul] at this
              omega
            simp only [Loc.offset, GlobLoc.idx] at h₁ ⊢
            omega
          · exact resolve_fls_lt
  · simp only [Loc.ColOK] at hl
    subst hl
    rcases b with _ | _
    · exact gfTerms_lt ht (getD_mem_or _ _ _)
    · cases j using Fin.cases with
      | zero =>
        simp only [table, Fin.cases_zero]
        refine ⟨resolve_fls_lt, resolve_cur_lt fun _ => ?_⟩
        simp only [Loc.offset, gadgetIdx, Bool.toNat_false, Bool.toNat_true]
        omega
      | succ j =>
        simp only [table, Fin.cases_succ]
        refine ⟨resolve_cur_lt fun _ => ?_, resolve_cur_lt fun _ => ?_⟩ <;>
          simp only [Loc.offset, gadgetIdx, Bool.toNat_false, Bool.toNat_true,
            Fin.val_castSucc, Fin.val_succ] <;> omega
  · rcases b with _ | _
    · exact colTerms_lt ht hc (getD_mem_or _ _ _)
    · cases j using Fin.cases with
      | zero =>
        simp only [table, Fin.cases_zero]
        refine ⟨resolve_fls_lt, resolve_cur_lt fun _ => ?_⟩
        simp only [Loc.offset, gadgetIdx, Bool.toNat_false, Bool.toNat_true, ColSel.apply]
        omega
      | succ j =>
        simp only [table, Fin.cases_succ]
        refine ⟨resolve_cur_lt fun _ => ?_, resolve_cur_lt fun _ => ?_⟩ <;>
          simp only [Loc.offset, gadgetIdx, Bool.toNat_false, Bool.toNat_true,
            Fin.val_castSucc, Fin.val_succ, ColSel.apply] <;> omega

/-! ### Every gate sits at a position -/

omit [DecidableEq State] in
private theorem symIdx_symOf {m : ℕ} (hm : m < 3) : symIdx (symOf m) = m := by
  rcases m with _ | _ | _ | m
  · rfl
  · rfl
  · rfl
  · omega

omit [DecidableEq State] in
private theorem ScanQ.idx_ofIdx {m : ℕ} (hm : m < 3 + 3 * k) : (ScanQ.ofIdx m : ScanQ k).idx = m :=
    by
  rw [ScanQ.ofIdx]
  split_ifs with h₁ h₂
  · exact symIdx_symOf h₁
  · simp only [ScanQ.idx]
    rw [symIdx_symOf (Nat.mod_lt _ (by norm_num))]
    omega
  · exact absurd (by omega) h₂

omit [DecidableEq State] in
private theorem ScanLoc.idx_ofIdx {m : ℕ} (hm : m < scanWidth k) :
    (ScanLoc.ofIdx m : ScanLoc k).idx = m := by
  simp only [scanWidth] at hm
  rw [ScanLoc.ofIdx]
  split_ifs with h₁ h₂ h₃
  · rfl
  · simp only [ScanLoc.idx]; omega
  · simp only [ScanLoc.idx]
    rw [ScanQ.idx_ofIdx (by omega)]
    omega
  · simp only [ScanLoc.idx]
    rw [ScanQ.idx_ofIdx (by omega)]
    omega

omit [DecidableEq State] in
private theorem GlobLoc.idx_ofIdx {m : ℕ} (hm : m < globWidth k State) :
    (GlobLoc.ofIdx m : GlobLoc k State).idx = m := by
  simp only [globWidth] at hm
  rw [GlobLoc.ofIdx]
  split_ifs with h₁ h₂
  · simp only [GlobLoc.idx]
    exact Nat.div_add_mod' m (k + 1)
  · simp only [GlobLoc.idx, attrIdx, Equiv.apply_symm_apply]
    have := Nat.div_add_mod' (m - numSit k State * (k + 1)) (numSit k State + 1)
    omega
  · have : m - numSit k State * (k + 1) <
        Fintype.card (Attr k State) * (numSit k State + 1) := by omega
    exact absurd ((Nat.div_lt_iff_lt_mul (by omega)).2 this) h₂

omit [DecidableEq State] in
private theorem GFeat.idx_ofIdx {m : ℕ} (hm : m < Fintype.card (Option State) + 4) :
    (GFeat.ofIdx m : GFeat State).idx = m := by
  rw [GFeat.ofIdx]
  split_ifs with h
  · simp [GFeat.idx]
  · simp only [GFeat.idx, outViewOf]
    split_ifs <;> simp only [OutView.index] <;> omega

omit [DecidableEq State] in
private theorem ColFeat.idx_ofIdx {m : ℕ} (hm : m < 1 + 4 * k) : (ColFeat.ofIdx m : ColFeat k).idx =
    m := by
  rw [ColFeat.ofIdx]
  split_ifs with h₁ h₂ h₃
  · simp only [ColFeat.idx]; omega
  · simp only [ColFeat.idx]; omega
  · simp only [ColFeat.idx]
    rw [symIdx_symOf (Nat.mod_lt _ (by norm_num))]
    omega
  · exact absurd (by omega) h₃

omit [DecidableEq State] in
private theorem gadgetIdx_decode (m : ℕ) : gadgetIdx (m / 16) (gadgetB m) (gadgetJ m) = m := by
  simp only [gadgetIdx, gadgetB, gadgetJ]
  by_cases h : 8 ≤ m % 16 <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false, mul_one, mul_zero,
    add_zero] <;> omega

omit [DecidableEq State] in
/-- **Every gate after the constants sits at a position** of a block. -/
private theorem exists_wire_eq {n T g : ℕ} (hg₂ : 2 ≤ g) (hg : g < numGates k State T) :
    ∃ t ≤ T, ∃ (l : Loc k State) (c : ℕ), l.ColOK T c ∧ wire n T t l c - n = g := by
  have hB : 0 < blockSize k State T := by
    have := Loc.offset_lt_of_lt (k := k) (State := State) (l := .scan .nx) (T := T) (c := 0)
      (by simp [numCols])
    omega
  have hdm := Nat.div_add_mod' (g - 2) (blockSize k State T)
  set t := (g - 2) / blockSize k State T
  set r := (g - 2) % blockSize k State T
  have hr : r < blockSize k State T := Nat.mod_lt _ hB
  have hgr : g = 2 + t * blockSize k State T + r := by omega
  have ht : t ≤ T := by
    have h₁ : g - 2 < (T + 1) * blockSize k State T := by
      simp only [numGates] at hg
      omega
    have : (g - 2) / blockSize k State T < T + 1 := (Nat.div_lt_iff_lt_mul hB).2 h₁
    omega
  refine ⟨t, ht, ?_⟩
  have hsw := scanWidth_pos (k := k)
  have hcw : 0 < colWidth k := by simp only [colWidth]; omega
  have hwire (l : Loc k State) (c : ℕ) (h : l.offset T c = r) : wire n T t l c - n = g := by
    rw [wire_sub, h, hgr]
  by_cases h₁ : r < globStart k T
  · refine ⟨.scan (ScanLoc.ofIdx (r % scanWidth k)), r / scanWidth k, ?_, hwire _ _ ?_⟩
    · simp only [Loc.ColOK, globStart] at h₁ ⊢
      rwa [Nat.div_lt_iff_lt_mul hsw]
    · simp only [Loc.offset]
      rw [ScanLoc.idx_ofIdx (Nat.mod_lt _ hsw), Nat.mul_comm]
      exact Nat.div_add_mod r _
  by_cases h₂ : r < gfStart k State T
  · refine ⟨.glob (GlobLoc.ofIdx (r - globStart k T)), 0, rfl, hwire _ _ ?_⟩
    simp only [Loc.offset]
    rw [GlobLoc.idx_ofIdx (by simp only [gfStart] at h₂; omega)]
    omega
  by_cases h₃ : r < colStart k State T
  · set m := r - gfStart k State T
    refine ⟨.gf (GFeat.ofIdx (m / 16)) (gadgetB m) (gadgetJ m), 0, rfl, hwire _ _ ?_⟩
    simp only [Loc.offset]
    rw [GFeat.idx_ofIdx (by simp only [colStart, gfWidth] at h₃; omega), gadgetIdx_decode]
    omega
  · set m := r - colStart k State T
    have hm : m < numCols T * colWidth k := by simp only [blockSize] at hr; omega
    refine ⟨.col (ColFeat.ofIdx (m % colWidth k / 16)) (gadgetB (m % colWidth k))
      (gadgetJ (m % colWidth k)), m / colWidth k, ?_, hwire _ _ ?_⟩
    · simp only [Loc.ColOK]
      rwa [Nat.div_lt_iff_lt_mul hcw]
    · simp only [Loc.offset]
      have hmod := Nat.mod_lt m hcw
      rw [ColFeat.idx_ofIdx (by simp only [colWidth] at hmod ⊢; omega), gadgetIdx_decode]
      have := Nat.div_add_mod' m (colWidth k)
      omega

/-! ### The gate list is the code of a circuit -/

omit [DecidableEq State] in
private theorem length_argsOf (op : Op) (a b : ℕ) : (argsOf op a b).length = signature.Arity op :=
    by
  cases op <;> rfl

omit [DecidableEq State] in
private theorem mem_argsOf {op : Op} {a b i : ℕ} (h : i ∈ argsOf op a b) : i = a ∨ i = b := by
  cases op <;> simp_all [argsOf]

private theorem length_gateAt (n T t c : ℕ) (l : Loc k State) :
    (gateAt tm n T t c l).2.length = signature.Arity (gateAt tm n T t c l).1 := by
  unfold gateAt
  split_ifs
  · rfl
  · exact length_argsOf _ _ _

/-- A gate at a position reads earlier wires. -/
private theorem lt_of_mem_gateAt {n T t c : ℕ} {l : Loc k State} (hl : l.ColOK T c) {i : ℕ}
    (hi : i ∈ (gateAt tm n T t c l).2) : i < wire n T t l c := by
  unfold gateAt at hi
  split_ifs at hi with ht
  · simp at hi
  · have h := resolve_table_lt tm (n := n) (Nat.one_le_iff_ne_zero.mpr ht) hl
    rcases mem_argsOf hi with rfl | rfl
    exacts [h.1, h.2]

/-- **The tableau is well formed**: its gate list is the code of a program on `n` inputs. -/
theorem isCodeFrom_gates (n T : ℕ) : Program.IsCodeFrom signature n 0 (gates tm n T) := by
  refine Program.isCodeFrom_of_getElem fun g hg => ?_
  simp only [gates, List.length_map, List.length_range] at hg
  simp only [gates, List.getElem_map, List.getElem_range, Nat.add_zero]
  by_cases h₂ : g < 2
  · simp only [gateCode, h₂, ↓reduceIte]
    exact ⟨rfl, by simp⟩
  · obtain ⟨t, -, l, c, hl, hw⟩ := exists_wire_eq (k := k) (State := State) (n := n)
      (Nat.le_of_not_lt h₂) hg
    rw [← hw, gateCode_wire tm hl]
    refine ⟨length_gateAt tm _ _ _ _ _, fun i hi => ?_⟩
    have := lt_of_mem_gateAt tm hl hi
    rw [wire_sub] at hw ⊢
    simp only [wire] at this
    omega

omit [DecidableEq State] in
theorem outWire_lt (n T : ℕ) : outWire k State n T < n + numGates k State T := by
  have := Loc.offset_lt (k := k) (State := State) (T := T)
    (l := .gf (.out (.one true)) true 7) (c := 0) rfl
  simp only [outWire, wire, numGates]
  rw [Nat.succ_mul]
  omega

theorem isSome_ofCode (n T : ℕ) :
    (Circuit.ofCode n 1 (gates tm n T, [outWire k State n T]) :
      Option (Circuit signature n 1)).isSome := by
  rw [Circuit.isSome_ofCode_iff]
  refine ⟨isCodeFrom_gates tm n T, rfl, fun i hi => ?_⟩
  simp only [List.mem_singleton] at hi
  subst hi
  simpa [gates] using outWire_lt (k := k) (State := State) n T

/-- **The tableau circuit** of `tm` for `T` steps on inputs of length `n`. -/
noncomputable def circuit (n T : ℕ) : Circuit signature n 1 :=
  (Circuit.ofCode n 1 (gates tm n T, [outWire k State n T])).get (isSome_ofCode tm n T)

/-- The code of the tableau circuit is its gate list with the output wire. -/
theorem code_circuit (n T : ℕ) :
    (circuit tm n T).code = (gates tm n T, [outWire k State n T]) :=
  Circuit.code_of_ofCode_eq_some (Option.some_get _).symm

end Cslib.Circuits.Boolean.Tableau
