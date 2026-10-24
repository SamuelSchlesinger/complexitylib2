/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Size
import Complexity.Foundations.Data.List.Basic

/-!
# Undirected s–t connectivity

An instance of undirected `s`–`t` connectivity (`Cslib.Complexity.USTCONInstance`) is a simple
graph on `Fin n`, given by its adjacency matrix, symmetric and with zero diagonal, together with
two vertices `s` and `t`; it belongs to `Cslib.Complexity.USTCON` when `t` is reachable from `s`
[Arora and Barak, Section 21.4][AroraBarak09] [Reingold, Section 4][Reingold2008].

Instances are encoded (`Cslib.Complexity.encUSTCON`) by the unary header `1^n 0 1^s 0 1^t 0`
followed by the adjacency matrix, row by row: the bit at `n + s + t + 3 + a * n + b` is the entry
of the row `a` and the column `b`. The matrix has `n ^ 2` bits, so the header is no longer than the
matrix plus three bits and every number a machine reads from it has logarithmically many binary
digits; this is the adjacency matrix representation of Reingold's algorithm, with a header that a
machine reading its input by address can parse by counting.

## Main definitions

* `Cslib.Complexity.USTCONInstance`: instances of undirected `s`–`t` connectivity.
* `Cslib.Complexity.USTCONInstance.graph`: the simple graph of an instance.
* `Cslib.Complexity.USTCONInstance.edgeTwo`, `Cslib.Complexity.USTCONInstance.emptyTwo`,
  `Cslib.Complexity.USTCONInstance.ofBool`: canonical two-vertex connected and disconnected
  instances.
* `Cslib.Complexity.encUSTCON`: the encoding of instances.
* `Cslib.Complexity.USTCON`: the instances in which `t` is reachable from `s`.

## Main results

* `Cslib.Complexity.USTCONInstance.getD_encode_n`, `.getD_encode_s`, `.getD_encode_t`,
  `.getD_encode_matrix`: the bits of the header and of the matrix in the encoding.
* `Cslib.Complexity.USTCONInstance.encode_injective`: the encoding is injective.
* `Cslib.Complexity.USTCONInstance.size_n_le_log2`: the number of vertices has logarithmically many
  binary digits in the length of the encoding.
* `Cslib.Complexity.USTCONInstance.edgeTwo_mem_USTCON`,
  `Cslib.Complexity.USTCONInstance.emptyTwo_notMem_USTCON`,
  `Cslib.Complexity.USTCONInstance.ofBool_mem_USTCON`: membership of the canonical two-vertex
  instances in `USTCON`.

## References

* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

/-- An instance of **undirected `s`–`t` connectivity**: a simple graph on `Fin n`, given by its
adjacency matrix, symmetric and with zero diagonal, and two vertices `s` and `t`. -/
structure USTCONInstance where
  /-- The number of vertices. -/
  n : ℕ
  /-- The adjacency matrix. -/
  adj : Fin n → Fin n → Bool
  /-- The adjacency matrix is symmetric. -/
  symm : ∀ a b, adj a b = adj b a
  /-- No vertex is adjacent to itself. -/
  loopless : ∀ a, adj a a = false
  /-- The source. -/
  s : Fin n
  /-- The target. -/
  t : Fin n

namespace USTCONInstance

variable (I : USTCONInstance)

/-- An instance has a vertex, its source. -/
theorem n_pos : 0 < I.n :=
  Fin.pos I.s

/-- The simple graph of an instance: `a` and `b` are adjacent when the entry of the row `a` and the
column `b` of the adjacency matrix is set. -/
def graph : SimpleGraph (Fin I.n) where
  Adj a b := I.adj a b = true
  symm.symm a b h := (I.symm b a).trans h
  loopless.irrefl a h := by simp [I.loopless] at h

/-- Adjacency in the graph of an instance is decidable. -/
instance : DecidableRel I.graph.Adj :=
  fun a b ↦ inferInstanceAs (Decidable (I.adj a b = true))

/-- Adjacency in the graph of an instance is the entry of the adjacency matrix. -/
@[simp]
theorem graph_adj {a b : Fin I.n} : I.graph.Adj a b ↔ I.adj a b = true :=
  Iff.rfl

/-- The column of an index below `n * n` is below `n`. -/
theorem mod_lt_of_lt_mul {i n : ℕ} (h : i < n * n) : i % n < n :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at h)

/-- The adjacency matrix, row by row: its bit at `i` is the entry of the row `i / n` and the
column `i % n`. -/
def matrix : List Bool :=
  List.ofFn fun i : Fin (I.n * I.n) ↦
    I.adj ⟨i / I.n, Nat.div_lt_of_lt_mul i.isLt⟩ ⟨i % I.n, mod_lt_of_lt_mul i.isLt⟩

/-- The adjacency matrix has `n ^ 2` entries. -/
@[simp]
theorem length_matrix : I.matrix.length = I.n * I.n := by
  simp [matrix]

/-- The entry of the row `a` and the column `b` is the bit at `a * n + b` of the matrix. -/
private theorem getD_matrix (a b : Fin I.n) : I.matrix.getD (a * I.n + b) false = I.adj a b := by
  have hlt : (a : ℕ) * I.n + b < I.n * I.n := by
    have := Nat.mul_le_mul_right I.n (Nat.succ_le_of_lt a.isLt)
    rw [Nat.succ_mul] at this
    omega
  unfold matrix
  rw [List.getD_eq_getElem (hn := by simpa using hlt), List.getElem_ofFn]
  have hpos : 0 < I.n := Fin.pos a
  congr 1
  · ext
    simp only
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt b.isLt, Nat.zero_add]
  · ext
    simp only
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.isLt]

/-- The encoding of an instance: the unary header `1^n 0 1^s 0 1^t 0`, then the adjacency matrix
row by row. -/
def encode : List Bool :=
  List.replicate I.n true ++ false :: (List.replicate I.s true ++ false ::
    (List.replicate I.t true ++ false :: I.matrix))

/-- The number of vertices is at most the length of the encoding. -/
private theorem n_le_length_encode : I.n ≤ I.encode.length := by
  simp [encode]

/-- The number of binary digits of `n` is logarithmic in the length of the encoding. -/
theorem size_n_le_log2 : Nat.size I.n ≤ Nat.log2 I.encode.length + 1 :=
  Nat.size_le.2 (I.n_le_length_encode.trans_lt Nat.lt_log2_self)

/-- Within a unary block followed by `false`, the bits are set before the end of the block. -/
private theorem getD_replicate_append_false_of_le {m i : ℕ} (l : List Bool) (h : i ≤ m) :
    (List.replicate m true ++ false :: l).getD i false = decide (i < m) := by
  rcases h.lt_or_eq with h | rfl
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [h]
  · rw [List.getD_append_right _ _ _ _ (by simp)]
    simp

/-- After a unary block of length `m` followed by `false`, the bits are those of the rest. -/
private theorem getD_replicate_append_false_add (m i : ℕ) (l : List Bool) :
    (List.replicate m true ++ false :: l).getD (m + 1 + i) false = l.getD i false := by
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega)]
  simp only [List.length_replicate, show m + 1 + i - m = i + 1 by omega, List.getD_cons_succ]

/-- The header of the number of vertices: the bit at `i ≤ n` is set exactly when `i < n`. -/
theorem getD_encode_n {i : ℕ} (h : i ≤ I.n) : I.encode.getD i false = decide (i < I.n) :=
  getD_replicate_append_false_of_le _ h

/-- The header of the source: the bit at `n + 1 + i`, for `i ≤ s`, is set exactly when `i < s`. -/
theorem getD_encode_s {i : ℕ} (h : i ≤ I.s) :
    I.encode.getD (I.n + 1 + i) false = decide (i < I.s) := by
  rw [encode, getD_replicate_append_false_add]
  exact getD_replicate_append_false_of_le _ h

/-- The header of the target: the bit at `n + 1 + s + 1 + i`, for `i ≤ t`, is set exactly when
`i < t`. -/
theorem getD_encode_t {i : ℕ} (h : i ≤ I.t) :
    I.encode.getD (I.n + 1 + I.s + 1 + i) false = decide (i < I.t) := by
  rw [encode, show I.n + 1 + I.s + 1 + i = I.n + 1 + (I.s + 1 + i) by omega,
    getD_replicate_append_false_add, getD_replicate_append_false_add]
  exact getD_replicate_append_false_of_le _ h

/-- **The bits of the matrix**: the bit at `n + s + t + 3 + a * n + b` of the encoding is the entry
of the row `a` and the column `b`. -/
theorem getD_encode_matrix (a b : Fin I.n) :
    I.encode.getD (I.n + I.s + I.t + 3 + (a * I.n + b)) false = I.adj a b := by
  rw [encode, show I.n + I.s + I.t + 3 + (a * I.n + b) =
      I.n + 1 + (I.s + 1 + (I.t + 1 + (a * I.n + b))) by omega,
    getD_replicate_append_false_add, getD_replicate_append_false_add,
    getD_replicate_append_false_add, getD_matrix]

/-- **The encoding is injective.** -/
theorem encode_injective : Function.Injective encode := by
  rintro ⟨n, adj, symm, loopless, s, t⟩ ⟨n', adj', symm', loopless', s', t'⟩ h
  obtain ⟨rfl, h⟩ := List.replicate_true_append_false_inj h
  obtain ⟨hs, h⟩ := List.replicate_true_append_false_inj h
  obtain ⟨ht, h⟩ := List.replicate_true_append_false_inj h
  have hadj : adj = adj' := by
    funext a b
    have := congrArg (fun l ↦ l.getD (a * n + b) false) h
    exact (getD_matrix ⟨n, adj, symm, loopless, s, t⟩ a b).symm.trans
      (this.trans (getD_matrix ⟨n, adj', symm', loopless', s', t'⟩ a b))
  subst hadj
  have hs' : s = s' := Fin.ext hs
  have ht' : t = t' := Fin.ext ht
  subst hs' ht'
  rfl

end USTCONInstance

/-- The encoding of instances of undirected `s`–`t` connectivity: the unary header
`1^n 0 1^s 0 1^t 0`, then the adjacency matrix row by row. -/
def encUSTCON : USTCONInstance ↪ List Bool :=
  ⟨USTCONInstance.encode, USTCONInstance.encode_injective⟩

/-- **Undirected `s`–`t` connectivity**: the instances in which `t` is reachable from `s`
[Arora and Barak, Section 21.4][AroraBarak09], [Reingold][Reingold2008]. -/
def USTCON : Set USTCONInstance :=
  {I | I.graph.Reachable I.s I.t}

namespace USTCONInstance

/-- The single edge on two vertices `0` and `1`, with source `0` and target `1`. -/
def edgeTwo : USTCONInstance where
  n := 2
  adj a b := decide (a ≠ b)
  symm a b := by simp [ne_comm]
  loopless a := by simp
  s := 0
  t := 1

/-- The edgeless graph on two vertices `0` and `1`, with source `0` and target `1`. -/
def emptyTwo : USTCONInstance where
  n := 2
  adj _ _ := false
  symm _ _ := rfl
  loopless _ := rfl
  s := 0
  t := 1

/-- Canonical two-vertex `USTCON` instance encoding a Boolean truth value: `edgeTwo` for `true`
and `emptyTwo` for `false`. -/
def ofBool (b : Bool) : USTCONInstance :=
  if b then edgeTwo else emptyTwo

/-- The single edge on two vertices belongs to `USTCON`. -/
theorem edgeTwo_mem_USTCON : edgeTwo ∈ USTCON :=
  SimpleGraph.Adj.reachable (by decide)

/-- The edgeless graph on two vertices does not belong to `USTCON`. -/
theorem emptyTwo_notMem_USTCON : emptyTwo ∉ USTCON := by
  rintro ⟨p⟩
  cases p with
  | cons hadj _ => exact absurd hadj (by simp [emptyTwo, graph])

/-- `USTCONInstance.ofBool b` belongs to `USTCON` if and only if `b = true`. -/
@[simp]
theorem ofBool_mem_USTCON {b : Bool} : ofBool b ∈ USTCON ↔ b = true := by
  cases b
  · simp [ofBool, emptyTwo_notMem_USTCON]
  · simp [ofBool, edgeTwo_mem_USTCON]

end USTCONInstance

end Cslib.Complexity
