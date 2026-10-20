/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Output
public import Complexity.Logics.FirstOrder.Interpretation.Rank
import Complexity.Foundations.Data.List.Basic

/-!
# First-order reductions are logarithmic-space reductions

For finite relational vocabularies, an order-free first-order interpretation induces a
logarithmic-space transducer on structure encodings. It checks the input shape, counts domain
tuples to emit the unary output cardinality, and emits each relation table by repeatedly
reconstructing the tuples of the requested ranks. Each loop counter is polynomially bounded in
the input length; the existing counter-program simulation therefore supplies a total
`ComputableInLogSpace` machine. Neither the output structure nor its tables are stored.

Malformed inputs map to a fixed malformed target encoding. Empty structures, empty domains,
nullary relations, and zero-dimensional interpretations are included. Isomorphism closure of
the target query makes the choice of numbering immaterial.

These are order-free interpretations, without built-in order or `BIT`. The standard ordered
notion of first-order reduction in [Immerman1999] is a separate specialization.

## Main definitions

* `Cslib.Logic.FO.Interpretation.encodedMap`: the encoded interpreted structure, with malformed
  inputs sent to a malformed target encoding.

## Main results

* `Cslib.Logic.FO.Interpretation.computableInLogSpace_encodedMap`: the encoded map has a total
  logarithmic-space transducer.
* `Cslib.Logic.FO.Reduces.logSpaceReducible`: order-free interpretation reductions induce
  logspace many-one reductions between query languages.
* `Cslib.Logic.FO.Reduces.queryLanguage_mem_L` and
  `Cslib.Logic.FO.Reduces.queryLanguage_mem_P`: closure of encoded queries in `L` and `P`.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.5][Sipser2013]
-/

@[expose] public section

universe u v u' v'

open FirstOrder Language Structure CategoryTheory Turing Turing.CounterProgram

namespace Cslib.Logic.FO.Interpretation

open Vocabulary.ModelChecker Expr

namespace Transducer

/-! ### Registers and code -/

/-- The register of the coordinate `i` of the tuple in block `m`, for tuples of `d` coordinates. -/
private def blk (d m i : ℕ) : ℕ := 8 + d * m + i

/-- The code writing the coordinates of the tuple whose index is in register `4` into block `m`,
placed at the label `b`; it continues at `b + d`. -/
private def coordsCode (d m b : ℕ) : List Instr :=
  List.ofFn fun i : Fin d =>
    .assign (blk d m i) (mod (div (reg 4) (pow (reg 0) i)) (reg 0)) (b + i + 1)

private theorem length_coordsCode (d m b : ℕ) : (coordsCode d m b).length = d := by
  simp [coordsCode]

variable {P : CounterProgram} {w : List Bool} {B : ℕ}

/-- **Writing the coordinates of a tuple**: from the code at `b`, with the index `u < n ^ d` of a
tuple in register `4` and `n` in register `0`, the program writes the coordinates `u / n ^ i % n`
of the tuple into block `m`, changing no other register. -/
private theorem reaches_coordsCode {d m b n u : ℕ} (hP : P.CodeAt b (coordsCode d m b))
    (hu : u < n ^ d) (hnB : n ≤ B) (regs : List ℕ) (h0 : regs.getD 0 0 = n)
    (h4 : regs.getD 4 0 = u) (hlen : blk d m d ≤ regs.length) (hB : ∀ r ∈ regs, r ≤ B) :
    ∃ regs', P.Reaches w (P.Running B) (b, regs) (b + d, regs') ∧
      regs'.length = regs.length ∧ (∀ i < d, regs'.getD (blk d m i) 0 = u / n ^ i % n) ∧
      (∀ r, (∀ i < d, r ≠ blk d m i) → regs'.getD r 0 = regs.getD r 0) ∧
      ∀ r ∈ regs', r ≤ B := by
  have key : ∀ k ≤ d, ∃ regs', P.Reaches w (P.Running B) (b, regs) (b + k, regs') ∧
      regs'.length = regs.length ∧ (∀ i < k, regs'.getD (blk d m i) 0 = u / n ^ i % n) ∧
      (∀ r, (∀ i < k, r ≠ blk d m i) → regs'.getD r 0 = regs.getD r 0) ∧
      ∀ r ∈ regs', r ≤ B := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨regs, Reaches.refl _, rfl, fun _ h => absurd h (by omega),
        fun _ _ => rfl, hB⟩
    | succ k ih =>
      intro hk
      obtain ⟨regs₁, hreach, hlen₁, hset, hkeep, hB₁⟩ := ih (by omega)
      have hc : P.instr (b + k) =
          .assign (blk d m k) (mod (div (reg 4) (pow (reg 0) k)) (reg 0)) (b + k + 1) := by
        rw [hP k (by rw [length_coordsCode]; omega)]
        simp [coordsCode]
      have h0₁ : regs₁.getD 0 0 = n := by rw [hkeep 0 (fun i _ => by unfold blk; omega), h0]
      have h4₁ : regs₁.getD 4 0 = u := by rw [hkeep 4 (fun i _ => by unfold blk; omega), h4]
      have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with rfl | h
        · rw [zero_pow (by omega)] at hu
          omega
        · exact h
      refine ⟨regs₁.set (blk d m k) (u / n ^ k % n), hreach.trans (Reaches.assign hc hB₁ ?_),
        by rw [List.length_set, hlen₁], fun i hi => ?_, fun r hr => ?_,
        List.forall_mem_set_of_forall_mem hB₁ ((Nat.mod_lt _ hn).le.trans hnB)⟩
      · simp only [eval_mod, eval_div, eval_pow, eval_reg, h4₁, h0₁]
        exact Reaches.refl _
      · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hi | rfl
        · rw [List.getD_set_ne (by unfold blk; omega), hset i hi]
        · exact List.getD_set_self (by rw [hlen₁]; simp only [blk] at hlen ⊢; omega)
      · rw [List.getD_set_ne (Ne.symm (hr k (by omega))), hkeep r fun i hi => hr i (by omega)]
  exact key d le_rfl

/-! ### Frames of counted bits -/

open scoped Classical in
/-- Emitting `true, true` for every number below `N` passing a test, then `false`, frames as many
copies of `true`. -/
private theorem flatMap_pair_append_false (p : ℕ → Prop) (N : ℕ) :
    ((List.range N).flatMap fun k => if p k then [true, true] else []) ++ [false] =
      MultiTapeTM.frame (List.replicate ((Finset.range N).filter p).card true) := by
  rw [MultiTapeTM.frame]
  congr 1
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases hp : p N
    · rw [ite_eq_left hp, Finset.card_insert_of_notMem (by simp), List.replicate_succ',
        List.flatMap_append]
      simp [hp]
    · simp [hp]

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L.IsRelational] [L'.IsRelational]
  (v : Vocabulary L) (v' : Vocabulary L') {ι : Type} {d : ℕ} (e : ι ≃ Fin d)
  (I : Interpretation L L' ι)

/-- The largest arity of a symbol of the vocabulary `v'`. -/
private def maxArity : ℕ := Finset.univ.sup v'.arity

/-- The first register of the bound variables of the compiled formulas: after the blocks `0` to
`maxArity v'` of `d` coordinates. -/
private def base (d : ℕ) : ℕ := 8 + d * (maxArity v' + 1)

/-- The code of the domain formula, on the tuple in block `m`. -/
private noncomputable def domCode (m b T F : ℕ) : List Instr :=
  formulaCode v (fun i => blk d m (e i)) (base v' d) I.domain b T F

/-- The code counting and framing the elements of the interpreted structure, placed at the label
`b`: register `4` runs over the indices of the tuples, register `3` counts those of the domain, and
`true, true` is emitted for each of them; then `false` ends the frame. It continues at
`b + d + codeLength I.domain + 8`. -/
private noncomputable def scanCode (b : ℕ) : List Instr :=
  [.assign 3 (const 0) (b + 1)] ++
  forCode (b + 1) 4 (pow (reg 0) d) (b + 4) (b + d + codeLength I.domain + 7) ++
  coordsCode d 0 (b + 4) ++
  domCode v v' e I 0 (b + 4 + d) (b + 4 + d + codeLength I.domain) (b + 3) ++
  [.emit true (b + 4 + d + codeLength I.domain + 1),
   .emit true (b + 4 + d + codeLength I.domain + 2),
   .assign 3 (add (reg 3) (const 1)) (b + 3),
   .emit false (b + d + codeLength I.domain + 8)]

omit [L'.IsRelational] in
private theorem length_domCode (m b T F : ℕ) :
    (domCode v v' e I m b T F).length = codeLength I.domain :=
  length_formulaCode v _ _ _ _ _ _

omit [L'.IsRelational] in
private theorem blk_lt_base {m i : ℕ} (hm : m ≤ maxArity v') (hi : i < d) :
    blk d m i < base v' d := by
  unfold blk base
  have : d * m + d ≤ d * (maxArity v' + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left d hm) d
  omega

omit [L'.IsRelational] in
private theorem le_base : 8 ≤ base v' d := Nat.le_add_right _ _

variable {v v' e I} {P : CounterProgram} {a : EncodedStructure} {B : ℕ}

omit [L.IsRelational] [L'.IsRelational] in
/-- The domain formula holds of the tuple with index `k < n ^ d` exactly when `k` is an index of
the domain. -/
private theorem inDomain_iff {n k : ℕ} [L.Structure (Fin n)] (hk : k < n ^ d) :
    I.InDomain e n k ↔ I.domain.Realize (tupleAt e ⟨k, hk⟩) :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨hk, h⟩⟩

omit [L'.IsRelational] in
/-- **Counting and framing the elements of the interpreted structure**: from the scan code, with
the cardinality of a well-formed input in register `0`, the program emits the frame of as many
copies of `true` as the interpreted structure has elements, and puts that number in register
`3`. -/
private theorem reachesOut_scanCode (ha : v.WellFormed a) {b : ℕ}
    (hP : P.CodeAt b (scanCode v v' e I b))
    (hnB : a.1 ≤ B) (hNB : a.1 ^ d ≤ B) (regs : List ℕ) (h0 : regs.getD 0 0 = a.1)
    (hlen : base v' d + boundDepth I.domain ≤ regs.length) (hB : ∀ r ∈ regs, r ≤ B) :
    ∃ regs', P.ReachesOut (encStructure a) (P.Active B) (b, regs)
      (b + d + codeLength I.domain + 8, regs')
      (MultiTapeTM.frame (List.replicate (letI := v.decode a; modelCard I e a.1) true)) ∧
      regs'.length = regs.length ∧ regs'.getD 0 0 = a.1 ∧
      regs'.getD 3 0 = (letI := v.decode a; modelCard I e a.1) ∧ ∀ r ∈ regs', r ≤ B := by
  classical
  let _ := v.decode a
  rw [scanCode] at hP
  generalize hcs : codeLength I.domain = cs at hP ⊢
  have hl1 : ([Instr.assign 3 (const 0) (b + 1)] ++
      forCode (b + 1) 4 (pow (reg 0) d) (b + 4) (b + d + cs + 7)).length = 4 := rfl
  have hl2 : ([Instr.assign 3 (const 0) (b + 1)] ++
      forCode (b + 1) 4 (pow (reg 0) d) (b + 4) (b + d + cs + 7) ++
      coordsCode d 0 (b + 4)).length = 4 + d := by
    rw [List.length_append, hl1, length_coordsCode]
  have hl3 : ([Instr.assign 3 (const 0) (b + 1)] ++
      forCode (b + 1) 4 (pow (reg 0) d) (b + 4) (b + d + cs + 7) ++
      coordsCode d 0 (b + 4) ++
      domCode v v' e I 0 (b + 4 + d) (b + 4 + d + cs) (b + 3)).length = 4 + d + cs := by
    rw [List.length_append, hl2, length_domCode, hcs]
  rw [codeAt_append, codeAt_append, codeAt_append, codeAt_append] at hP
  obtain ⟨⟨⟨⟨h₀, hfor⟩, hcoords⟩, hdom⟩, htail⟩ := hP
  rw [hl3] at htail
  rw [hl2] at hdom
  rw [hl1] at hcoords
  rw [List.length_singleton] at hfor
  rw [codeAt_cons] at h₀
  replace h₀ := h₀.1
  simp only [codeAt_cons] at htail
  obtain ⟨hy₀, hy₁, hy₂, hx, -⟩ := htail
  replace hy₀ : P.instr (b + 4 + d + cs) = .emit true (b + 4 + d + cs + 1) := by
    convert hy₀ using 2; omega
  replace hy₁ : P.instr (b + 4 + d + cs + 1) = .emit true (b + 4 + d + cs + 2) := by
    convert hy₁ using 2; omega
  replace hy₂ : P.instr (b + 4 + d + cs + 2) = .assign 3 (add (reg 3) (const 1)) (b + 3) := by
    convert hy₂ using 2; omega
  replace hx : P.instr (b + d + cs + 7) = .emit false (b + d + cs + 8) := by
    convert hx using 2; omega
  rw [show b + (4 + d) = b + 4 + d by omega] at hdom
  have hbase := le_base v' (d := d)
  have hblk0 : blk d 0 d ≤ base v' d := by
    unfold blk base
    simp only [Nat.mul_zero, Nat.add_zero]
    nlinarith
  -- the invariant of the loop over the indices
  let Inv : ℕ → List ℕ → Prop := fun k r => r.getD 4 0 = k ∧ r.getD 0 0 = a.1 ∧
    r.getD 3 0 = I.domainRank e a.1 k ∧ r.length = regs.length ∧ ∀ x ∈ r, x ≤ B
  let o : ℕ → List Bool := fun k => if I.InDomain e a.1 k then [true, true] else []
  have hrank (k : ℕ) (hk : k < a.1 ^ d) : I.domainRank e a.1 (k + 1) ≤ B :=
    (domainRank_mono (I := I) (e := e) (n := a.1) (show k + 1 ≤ a.1 ^ d by omega)).trans
      ((Finset.card_filter_le _ _).trans (by simp; omega))
  have hB₀ : ∀ r ∈ regs.set 3 0, r ≤ B := List.forall_mem_set_of_forall_mem hB (Nat.zero_le _)
  obtain ⟨regsN, hloop, hinvN⟩ := reachesOut_forCode (B := B) (w := encStructure a) hfor Inv o hNB
    (fun k r ⟨h4, h0', _, hl, hB'⟩ => ⟨h4, by simp only [eval_pow, eval_reg, h0'],
      by rw [hl]; omega, hB'⟩)
    (fun k hk r ⟨h4, h0', h3, hl, hB'⟩ => by
      obtain ⟨regs₁, hreach₁, hlen₁, hset₁, hkeep₁, hB₁⟩ :=
        reaches_coordsCode (w := encStructure a) hcoords hk hnB r h0' h4 (by rw [hl]; omega) hB'
      have hreg (x : ℕ) (hx : x < 8) : regs₁.getD x 0 = r.getD x 0 :=
        hkeep₁ x fun i _ => by unfold blk; omega
      obtain ⟨res, regs₂, hres, hreach₂, hlen₂, hkeep₂, hB₂⟩ :=
        reaches_formulaCode ha hnB (fun i => blk d 0 (e i)) (base v' d) (by omega)
          (fun i => blk_lt_base v' (Nat.zero_le _) (e i).2) (tupleAt e ⟨k, hk⟩) I.domain
          (b + 4 + d) (b + 4 + d + cs) (b + 3) regs₁ default hdom
          (by rw [hlen₁, hl]; exact hlen)
          (by rw [hreg 0 (by omega), h0']) hB₁
          (fun i => by rw [hset₁ _ (e i).2, tupleAt_val]) (fun i => i.elim0)
      have hk₂ (x : ℕ) (hx : x < 8) : regs₂.getD x 0 = r.getD x 0 := by
        rw [hkeep₂ x (by omega), hreg x hx]
      have hdomk : (res = true) ↔ I.InDomain e a.1 k := by
        rw [hres, inDomain_iff hk]
        rfl
      have hlen₂' : regs₂.length = regs.length := by rw [hlen₂, hlen₁, hl]
      cases res with
      | true =>
        have hin : I.InDomain e a.1 k := hdomk.mp rfl
        refine ⟨regs₂.set 3 (I.domainRank e a.1 k + 1), ?_, ?_, ?_, ?_⟩
        · have hreach := hreach₁.reachesOut.trans (hreach₂.reachesOut.trans
            (ReachesOut.emit hy₀ hB₂ (ReachesOut.emit hy₁ hB₂ (ReachesOut.assign hy₂ hB₂
              (ReachesOut.refl _)))))
          simp only [eval_add, eval_reg, eval_const, hk₂ 3 (by omega), h3,
            List.nil_append] at hreach
          simpa only [o, hin, ↓reduceIte] using hreach
        · rw [List.getD_set_ne (by omega), hk₂ 4 (by omega), h4]
        · refine List.forall_mem_set_of_forall_mem hB₂ ?_
          have := hrank k hk
          rw [domainRank_succ, ite_eq_left hin] at this
          exact this
        · refine ⟨List.getD_set_self (by simp only [List.length_set]; omega), ?_, ?_,
            by simp only [List.length_set, hlen₂'], List.forall_mem_set_of_forall_mem
              (List.forall_mem_set_of_forall_mem hB₂ ?_) (by omega)⟩
          · rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega), hk₂ 0 (by omega), h0']
          · rw [List.getD_set_ne (by omega), List.getD_set_self (by omega), domainRank_succ,
              ite_eq_left hin]
          · have := hrank k hk
            rw [domainRank_succ, ite_eq_left hin] at this
            exact this
      | false =>
        have hnot : ¬ I.InDomain e a.1 k := fun h => Bool.false_ne_true (hdomk.mpr h)
        refine ⟨regs₂, ?_, by rw [hk₂ 4 (by omega), h4], hB₂, ?_⟩
        · have hreach := hreach₁.reachesOut.trans hreach₂.reachesOut
          simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append] at hreach
          simpa only [o, hnot, ↓reduceIte] using hreach
        · refine ⟨List.getD_set_self (by omega), ?_, ?_, by simp only [List.length_set, hlen₂'],
            List.forall_mem_set_of_forall_mem hB₂ (by omega)⟩
          · rw [List.getD_set_ne (by omega), hk₂ 0 (by omega), h0']
          · rw [List.getD_set_ne (by omega), hk₂ 3 (by omega), h3, domainRank_succ,
              ite_eq_right hnot]
            rfl)
    (regs.set 3 0) hB₀
    ⟨List.getD_set_self (by simp only [List.length_set]; omega),
      by rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega), h0],
      by rw [List.getD_set_ne (by omega), List.getD_set_self (by omega), domainRank_zero],
      by simp only [List.length_set],
      List.forall_mem_set_of_forall_mem hB₀ (Nat.zero_le _)⟩
  obtain ⟨-, h0N, h3N, hlN, hBN⟩ := hinvN
  refine ⟨regsN, ?_, hlN, h0N, h3N, hBN⟩
  have hreach := ReachesOut.assign h₀ hB (hloop.trans (ReachesOut.emit hx hBN (ReachesOut.refl _)))
  rw [modelCard, domainRank, ← flatMap_pair_append_false]
  simpa only [eval_const] using hreach

variable (v v' e I) in
/-- The code finding, by counting, the element of rank `t / n' ^ m % n'` of the interpreted
structure, for `t` in register `6` and its number `n'` of elements in register `3`, and writing its
coordinates into block `m`; placed at `A`, it continues at `A + d + codeLength I.domain + 6`.
Register `7` holds the rank sought, register `4` runs over the indices of the tuples and register
`5` counts those of the domain. -/
private noncomputable def unrankCode (m A : ℕ) : List Instr :=
  [.assign 7 (mod (div (reg 6) (pow (reg 3) m)) (reg 3)) (A + 1),
   .assign 4 (const 0) (A + 2),
   .assign 5 (const 0) (A + 3)] ++
  coordsCode d m (A + 3) ++
  domCode v v' e I m (A + 3 + d) (A + 3 + d + codeLength I.domain)
    (A + 3 + d + codeLength I.domain + 2) ++
  [.lt (reg 5) (reg 7) (A + 3 + d + codeLength I.domain + 1)
     (A + 3 + d + codeLength I.domain + 3),
   .assign 5 (add (reg 5) (const 1)) (A + 3 + d + codeLength I.domain + 2),
   .assign 4 (add (reg 4) (const 1)) (A + 3)]

omit [L'.IsRelational] in
private theorem length_unrankCode (m A : ℕ) :
    (unrankCode v v' e I m A).length = d + codeLength I.domain + 6 := by
  simp only [unrankCode, List.length_append, length_coordsCode, length_domCode, List.length_cons,
    List.length_nil]
  omega

omit [L'.IsRelational] in
/-- **Finding the element of a given rank**: from the unranking code for block `m`, with the
cardinality of a well-formed input in register `0`, the number `n' > 0` of elements of the
interpreted structure in register `3` and `t` in register `6`, the program writes into block `m`
the coordinates of the element of rank `t / n' ^ m % n'`, and changes no register below the base
other than `4`, `5`, `7` and those of block `m`. -/
private theorem reaches_unrankCode (ha : v.WellFormed a) {m A t : ℕ} (hm : m ≤ maxArity v')
    (hP : P.CodeAt A (unrankCode v v' e I m A)) (hnB : a.1 ≤ B) (hNB : a.1 ^ d ≤ B)
    (regs : List ℕ) (h0 : regs.getD 0 0 = a.1)
    (h3 : regs.getD 3 0 = (letI := v.decode a; modelCard I e a.1)) (h6 : regs.getD 6 0 = t)
    (hpos : 0 < (letI := v.decode a; modelCard I e a.1))
    (hlen : base v' d + boundDepth I.domain ≤ regs.length) (hB : ∀ r ∈ regs, r ≤ B) :
    ∃ regs', P.Reaches (encStructure a) (P.Running B) (A, regs)
      (A + d + codeLength I.domain + 6, regs') ∧ regs'.length = regs.length ∧
      (∀ i : ι, regs'.getD (blk d m (e i)) 0 =
        ((letI := v.decode a; ((rankEquiv I e a.1).symm
          ⟨t / modelCard I e a.1 ^ m % modelCard I e a.1, Nat.mod_lt _ hpos⟩).1 i : Fin a.1) :
          ℕ)) ∧
      (∀ x < base v' d, x ≠ 4 → x ≠ 5 → x ≠ 7 → (∀ i < d, x ≠ blk d m i) →
        regs'.getD x 0 = regs.getD x 0) ∧ ∀ r ∈ regs', r ≤ B := by
  classical
  let _ := v.decode a
  rw [unrankCode] at hP
  generalize hcs : codeLength I.domain = cs at hP ⊢
  set n' := modelCard I e a.1 with hn'
  set r := t / n' ^ m % n' with hr
  have hrn : r < n' := Nat.mod_lt _ hpos
  have hn'N : n' ≤ a.1 ^ d := modelCard_le_pow (I := I) (e := e) (n := a.1)
  have hl2 : ([Instr.assign 7 (mod (div (reg 6) (pow (reg 3) m)) (reg 3)) (A + 1),
      .assign 4 (const 0) (A + 2), .assign 5 (const 0) (A + 3)] ++
      coordsCode d m (A + 3)).length = 3 + d := by
    rw [List.length_append, length_coordsCode]
    rfl
  have hl3 : ([Instr.assign 7 (mod (div (reg 6) (pow (reg 3) m)) (reg 3)) (A + 1),
      .assign 4 (const 0) (A + 2), .assign 5 (const 0) (A + 3)] ++
      coordsCode d m (A + 3) ++
      domCode v v' e I m (A + 3 + d) (A + 3 + d + cs) (A + 3 + d + cs + 2)).length =
      3 + d + cs := by
    rw [List.length_append, hl2, length_domCode, hcs]
  rw [codeAt_append, codeAt_append, codeAt_append] at hP
  obtain ⟨⟨⟨hinit, hcoords⟩, hdom⟩, htail⟩ := hP
  rw [hl3] at htail
  rw [hl2] at hdom
  rw [show A + (3 + d) = A + 3 + d by omega] at hdom
  rw [show ([Instr.assign 7 (mod (div (reg 6) (pow (reg 3) m)) (reg 3)) (A + 1),
      .assign 4 (const 0) (A + 2), .assign 5 (const 0) (A + 3)] : List Instr).length = 3 from rfl]
    at hcoords
  simp only [codeAt_cons] at hinit htail
  obtain ⟨hi₀, hi₁, hi₂, -⟩ := hinit
  obtain ⟨hc₀, hc₁, hc₂, -⟩ := htail
  replace hi₂ : P.instr (A + 2) = .assign 5 (const 0) (A + 3) := by convert hi₂ using 2
  replace hc₀ : P.instr (A + 3 + d + cs) = .lt (reg 5) (reg 7) (A + 3 + d + cs + 1)
      (A + 3 + d + cs + 3) := by convert hc₀ using 2; omega
  replace hc₁ : P.instr (A + 3 + d + cs + 1) = .assign 5 (add (reg 5) (const 1))
      (A + 3 + d + cs + 2) := by convert hc₁ using 2; omega
  replace hc₂ : P.instr (A + 3 + d + cs + 2) = .assign 4 (add (reg 4) (const 1)) (A + 3) := by
    convert hc₂ using 2; omega
  have hbase := le_base v' (d := d)
  have hblkm : blk d m d ≤ base v' d := by
    unfold blk base
    have : d * m + d ≤ d * (maxArity v' + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left d hm) d
    omega
  -- the target
  obtain ⟨u₀, hu₀, hru₀⟩ := exists_inDomain_of_lt (I := I) (e := e) (n := a.1) hrn
  have hu₀N : u₀ < a.1 ^ d := hu₀.1
  -- the search
  have search : ∀ e' u (rs : List ℕ), u₀ - u = e' → u ≤ u₀ → rs.getD 4 0 = u →
      rs.getD 5 0 = I.domainRank e a.1 u → rs.getD 7 0 = r → rs.length = regs.length →
      (∀ x < base v' d, x ≠ 4 → x ≠ 5 → x ≠ 7 → (∀ i < d, x ≠ blk d m i) →
        rs.getD x 0 = regs.getD x 0) → (∀ x ∈ rs, x ≤ B) →
      ∃ regs', P.Reaches (encStructure a) (P.Running B) (A + 3, rs) (A + 3 + d + cs + 3, regs') ∧
        regs'.length = regs.length ∧
        (∀ i : ι, regs'.getD (blk d m (e i)) 0 = (tupleAt e ⟨u₀, hu₀N⟩ i : ℕ)) ∧
        (∀ x < base v' d, x ≠ 4 → x ≠ 5 → x ≠ 7 → (∀ i < d, x ≠ blk d m i) →
          regs'.getD x 0 = regs.getD x 0) ∧ ∀ x ∈ regs', x ≤ B := by
    intro e'
    induction e' using Nat.strong_induction_on with
    | _ e' ih =>
      intro u rs he hu h4 h5 h7 hl hkeep hB'
      have huN : u < a.1 ^ d := by omega
      have h0s : rs.getD 0 0 = a.1 := by
        rw [hkeep 0 (by omega) (by omega) (by omega) (by omega) (fun i _ => by unfold blk; omega),
          h0]
      have h3s : rs.getD 3 0 = n' := by
        rw [hkeep 3 (by omega) (by omega) (by omega) (by omega) (fun i _ => by unfold blk; omega),
          h3]
      obtain ⟨regs₁, hreach₁, hlen₁, hset₁, hkeep₁, hB₁⟩ :=
        reaches_coordsCode (w := encStructure a) hcoords huN hnB rs h0s h4 (by omega) hB'
      obtain ⟨res, regs₂, hres, hreach₂, hlen₂, hkeep₂, hB₂⟩ :=
        reaches_formulaCode ha hnB (fun i => blk d m (e i)) (base v' d) (by omega)
          (fun i => blk_lt_base v' hm (e i).2) (tupleAt e ⟨u, huN⟩) I.domain
          (A + 3 + d) (A + 3 + d + cs) (A + 3 + d + cs + 2) regs₁ default hdom
          (by rw [hlen₁, hl]; exact hlen)
          (by rw [hkeep₁ 0 (fun i _ => by unfold blk; omega), h0s]) hB₁
          (fun i => by rw [hset₁ _ (e i).2, tupleAt_val]) (fun i => i.elim0)
      have hk₂ (x : ℕ) (hx : x < base v' d) (hxm : ∀ i < d, x ≠ blk d m i) :
          regs₂.getD x 0 = rs.getD x 0 := by
        rw [hkeep₂ x (by omega), hkeep₁ x hxm]
      have hres' : res = true ↔ I.InDomain e a.1 u := by
        rw [hres, inDomain_iff huN]
        rfl
      have hlen₂' : regs₂.length = regs.length := by rw [hlen₂, hlen₁, hl]
      have h4₂ : regs₂.getD 4 0 = u := by
        rw [hk₂ 4 (by omega) (fun i _ => by unfold blk; omega), h4]
      have h5₂ : regs₂.getD 5 0 = I.domainRank e a.1 u := by
        rw [hk₂ 5 (by omega) (fun i _ => by unfold blk; omega), h5]
      have h7₂ : regs₂.getD 7 0 = r := by
        rw [hk₂ 7 (by omega) (fun i _ => by unfold blk; omega), h7]
      have hkeepr (rs' : List ℕ) (hrs' : ∀ x < base v' d, (∀ i < d, x ≠ blk d m i) →
          x ≠ 4 → x ≠ 5 → rs'.getD x 0 = regs₂.getD x 0) :
          ∀ x < base v' d, x ≠ 4 → x ≠ 5 → x ≠ 7 → (∀ i < d, x ≠ blk d m i) →
            rs'.getD x 0 = regs.getD x 0 := fun x hx h4' h5' h7' hxm => by
        rw [hrs' x hx hxm h4' h5', hk₂ x hx hxm, hkeep x hx h4' h5' h7' hxm]
      have hle : I.domainRank e a.1 u ≤ r := hru₀ ▸ domainRank_mono hu
      cases res with
      | false =>
        have hnot : ¬ I.InDomain e a.1 u := fun h => Bool.false_ne_true (hres'.mpr h)
        have hne : u ≠ u₀ := fun h => hnot (h ▸ hu₀)
        obtain ⟨regs', hreach', hlen', hset', hkeep', hB''⟩ :=
          ih (u₀ - (u + 1)) (by omega) (u + 1) (regs₂.set 4 (u + 1)) rfl (by omega)
            (List.getD_set_self (by omega))
            (by rw [List.getD_set_ne (by omega), h5₂, domainRank_succ, ite_eq_right hnot]; rfl)
            (by rw [List.getD_set_ne (by omega), h7₂]) (by rw [List.length_set, hlen₂'])
            (hkeepr _ fun x _ _ h4' _ => List.getD_set_ne (Ne.symm h4'))
            (List.forall_mem_set_of_forall_mem hB₂ (by omega))
        refine ⟨regs', ?_, hlen', hset', hkeep', hB''⟩
        refine hreach₁.trans (hreach₂.trans ?_)
        refine Reaches.assign hc₂ hB₂ ?_
        simpa only [eval_add, eval_reg, eval_const, h4₂] using hreach'
      | true =>
        have hin : I.InDomain e a.1 u := hres'.mp rfl
        by_cases hlt : I.domainRank e a.1 u < r
        · have hne : u ≠ u₀ := fun h => by rw [h, hru₀] at hlt; exact lt_irrefl _ hlt
          have hB₃ : ∀ x ∈ regs₂.set 5 (I.domainRank e a.1 u + 1), x ≤ B :=
            List.forall_mem_set_of_forall_mem hB₂ (by omega)
          obtain ⟨regs', hreach', hlen', hset', hkeep', hB''⟩ :=
            ih (u₀ - (u + 1)) (by omega) (u + 1)
              ((regs₂.set 5 (I.domainRank e a.1 u + 1)).set 4 (u + 1)) rfl (by omega)
              (List.getD_set_self (by simp only [List.length_set]; omega))
              (by rw [List.getD_set_ne (by omega), List.getD_set_self (by omega), domainRank_succ,
                ite_eq_left hin])
              (by rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega), h7₂])
              (by simp only [List.length_set, hlen₂'])
              (hkeepr _ fun x _ _ h4' h5' => by
                rw [List.getD_set_ne (Ne.symm h4'), List.getD_set_ne (Ne.symm h5')])
              (List.forall_mem_set_of_forall_mem hB₃ (by omega))
          refine ⟨regs', ?_, hlen', hset', hkeep', hB''⟩
          refine hreach₁.trans (hreach₂.trans ?_)
          refine Reaches.lt hc₀ hB₂ ?_
          simp only [eval_reg, h5₂, h7₂, hlt, ↓reduceIte]
          refine Reaches.assign hc₁ hB₂ ?_
          simp only [eval_add, eval_reg, eval_const, h5₂]
          refine Reaches.assign hc₂ hB₃ ?_
          simpa only [eval_add, eval_reg, eval_const, List.getD_set_ne (show 5 ≠ 4 by omega),
            h4₂] using hreach'
        · have hrank : I.domainRank e a.1 u = r := by omega
          have heq : u = u₀ := by
            by_contra hne
            have := domainRank_lt_of_inDomain hin (show u < u₀ by omega)
            omega
          subst heq
          refine ⟨regs₂, ?_, hlen₂', fun i => by rw [hkeep₂ _ (blk_lt_base v' hm (e i).2),
            hset₁ _ (e i).2, tupleAt_val], hkeepr _ fun _ _ _ _ _ => rfl, hB₂⟩
          refine hreach₁.trans (hreach₂.trans ?_)
          refine Reaches.lt hc₀ hB₂ ?_
          simp only [eval_reg, h5₂, h7₂, hlt, ↓reduceIte]
          exact Reaches.refl _
  -- the initialization
  have hrB : r ≤ B := by omega
  have hB₇ : ∀ x ∈ regs.set 7 r, x ≤ B := List.forall_mem_set_of_forall_mem hB hrB
  have hB₄ : ∀ x ∈ (regs.set 7 r).set 4 0, x ≤ B :=
    List.forall_mem_set_of_forall_mem hB₇ (Nat.zero_le _)
  have hB₅ : ∀ x ∈ ((regs.set 7 r).set 4 0).set 5 0, x ≤ B :=
    List.forall_mem_set_of_forall_mem hB₄ (Nat.zero_le _)
  have hl₄ : 4 < (regs.set 7 r).length := by simp only [List.length_set]; omega
  have hl₅ : 5 < ((regs.set 7 r).set 4 0).length := by simp only [List.length_set]; omega
  obtain ⟨regs', hreach', hlen', hset', hkeep', hB''⟩ :=
    search (u₀ - 0) 0 (((regs.set 7 r).set 4 0).set 5 0) rfl (Nat.zero_le _)
      (by rw [List.getD_set_ne (by omega), List.getD_set_self hl₄])
      (by rw [List.getD_set_self hl₅, domainRank_zero])
      (by rw [List.getD_set_ne (by omega), List.getD_set_ne (by omega),
        List.getD_set_self (by omega)])
      (by simp only [List.length_set])
      (fun x _ h4' h5' h7' _ => by
        rw [List.getD_set_ne (Ne.symm h5'), List.getD_set_ne (Ne.symm h4'),
          List.getD_set_ne (Ne.symm h7')])
      hB₅
  refine ⟨regs', ?_, hlen', fun i => ?_, hkeep', hB''⟩
  · refine Reaches.assign hi₀ hB ?_
    simp only [eval_mod, eval_div, eval_pow, eval_reg, h6, h3]
    refine Reaches.assign hi₁ hB₇ ?_
    simp only [eval_const]
    refine Reaches.assign hi₂ hB₄ ?_
    rw [show A + d + cs + 6 = A + 3 + d + cs + 3 by omega]
    simpa only [eval_const] using hreach'
  · rw [hset' i, rankEquiv_symm_val (r := ⟨r, hrn⟩) hu₀ hru₀]

/-- Emitting `true` and a bit for every number below `N`, then `false`, frames the bits. -/
private theorem flatMap_range_pair_append_false (N : ℕ) (f : Fin N → Bool) :
    ((List.range N).flatMap fun t => [true, if h : t < N then f ⟨t, h⟩ else false]) ++ [false] =
      MultiTapeTM.frame (List.ofFn f) := by
  rw [MultiTapeTM.frame, ← List.map_coe_finRange_eq_range, List.flatMap_map, List.ofFn_eq_map,
    List.flatMap_map]
  congr 1
  refine List.flatMap_congr fun i _ => ?_
  simp [i.2]

variable (v' I) in
/-- The number of instructions of the code of the defining formula of the symbol `j`. -/
private noncomputable def relLength (j : Fin v'.count) : ℕ := codeLength (I.rel (v'.symbol j).2)

variable (v' I d) in
/-- The number of instructions of the code of the table of the symbol `j`. -/
private noncomputable def tableLength (j : Fin v'.count) : ℕ :=
  3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j + 5

variable (v v' e I) in
/-- The code emitting the framed truth table of the symbol `j` of the interpreted structure,
placed at `b`: register `6` runs over the indices `t` of the tuples of elements, the elements of
the tuple are found by their ranks (`Cslib.Logic.FO.Interpretation.Transducer.unrankCode`), and
`true` followed by the truth value of the defining formula is emitted for each; then `false` ends
the frame. It continues at `b + tableLength v' d I j`. -/
private noncomputable def tableCode (j : Fin v'.count) (b : ℕ) : List Instr :=
  forCode b 6 (pow (reg 3) (v'.symbol j).1) (b + 3)
    (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j + 4) ++
  (List.range (v'.symbol j).1).flatMap
    (fun m => unrankCode v v' e I m (b + 3 + (d + codeLength I.domain + 6) * m)) ++
  formulaCode v (fun p : Fin (v'.symbol j).1 × ι => blk d p.1 (e p.2)) (base v' d)
    (I.rel (v'.symbol j).2) (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1)
    (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j)
    (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j + 2) ++
  [.emit true (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j + 1),
   .emit true (b + 2),
   .emit true (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j + 3),
   .emit false (b + 2),
   .emit false (b + 3 + (d + codeLength I.domain + 6) * (v'.symbol j).1 + relLength v' I j + 5)]

private theorem blk_ne {m m' i i' : ℕ} (h : m ≠ m') (hi : i < d) (hi' : i' < d) :
    blk d m i ≠ blk d m' i' := by
  unfold blk
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have : d * (m + 1) ≤ d * m' := Nat.mul_le_mul_left d hlt
    rw [Nat.mul_succ] at this
    omega
  · have : d * (m' + 1) ≤ d * m := Nat.mul_le_mul_left d hgt
    rw [Nat.mul_succ] at this
    omega

omit [L'.IsRelational] in
private theorem arity_le_maxArity (j : Fin v'.count) : (v'.symbol j).1 ≤ maxArity v' :=
  Finset.le_sup (f := v'.arity) (Finset.mem_univ j)

omit [L'.IsRelational] in
private theorem length_unranks (b k : ℕ) :
    ((List.range k).flatMap fun m =>
      unrankCode v v' e I m (b + 3 + (d + codeLength I.domain + 6) * m)).length =
      (d + codeLength I.domain + 6) * k := by
  rw [List.length_flatMap]
  simp only [length_unrankCode, List.map_const', List.length_range, List.sum_replicate,
    smul_eq_mul, Nat.mul_comm]

/-- **Emitting the truth table of a symbol of the interpreted structure**: from the table code
for the symbol `j`, with the cardinality of a well-formed input in register `0` and the number `n'`
of elements of the interpreted structure in register `3`, the program emits the framed truth table
of the symbol in the interpreted structure, numbered by ranks. -/
private theorem reachesOut_tableCode (ha : v.WellFormed a) (j : Fin v'.count) {b : ℕ}
    (hP : P.CodeAt b (tableCode v v' e I j b)) (hnB : a.1 ≤ B) (hNB : a.1 ^ d ≤ B)
    (hTB : (letI := v.decode a; modelCard I e a.1) ^ (v'.symbol j).1 ≤ B)
    (regs : List ℕ) (h0 : regs.getD 0 0 = a.1)
    (h3 : regs.getD 3 0 = (letI := v.decode a; modelCard I e a.1))
    (hlenD : base v' d + boundDepth I.domain ≤ regs.length)
    (hlenR : base v' d + boundDepth (I.rel (v'.symbol j).2) ≤ regs.length)
    (hB : ∀ r ∈ regs, r ≤ B) :
    ∃ regs', P.ReachesOut (encStructure a) (P.Active B) (b, regs)
      (b + tableLength v' d I j, regs')
      (MultiTapeTM.frame (letI := v.decode a;
        Vocabulary.relTable (I.Model (Fin a.1)) (rankEquiv I e a.1) (v'.symbol j))) ∧
      regs'.length = regs.length ∧ regs'.getD 0 0 = a.1 ∧
      regs'.getD 3 0 = (letI := v.decode a; modelCard I e a.1) ∧ ∀ r ∈ regs', r ≤ B := by
  classical
  let _ := v.decode a
  have hkm := arity_le_maxArity (v' := v') j
  have hlu := length_unranks (v := v) (v' := v') (e := e) (I := I) b (v'.symbol j).1
  rw [tableCode] at hP
  rw [tableLength]
  generalize hcs : codeLength I.domain = cs at hP hlu ⊢
  generalize hcr : relLength v' I j = cr at hP ⊢
  set n' := modelCard I e a.1 with hn'
  have hn'N : n' ≤ a.1 ^ d := modelCard_le_pow (I := I) (e := e) (n := a.1)
  rw [codeAt_append, codeAt_append, codeAt_append] at hP
  obtain ⟨⟨⟨hfor, hunr⟩, hrel⟩, htail⟩ := hP
  have hlf : (forCode b 6 (pow (reg 3) (v'.symbol j).1) (b + 3)
      (b + 3 + (d + cs + 6) * (v'.symbol j).1 + cr + 4)).length = 3 := rfl
  rw [List.length_append, hlu, hlf] at hrel
  rw [List.length_append, List.length_append, hlu, hlf, length_formulaCode,
    show codeLength (I.rel (v'.symbol j).2) = cr from hcr] at htail
  rw [hlf] at hunr
  rw [show b + (3 + (d + cs + 6) * (v'.symbol j).1) = b + 3 + (d + cs + 6) * (v'.symbol j).1 by
    omega] at hrel
  simp only [codeAt_cons] at htail
  obtain ⟨hy₀, hy₁, hn₀, hn₁, hx, -⟩ := htail
  set Rl := b + 3 + (d + cs + 6) * (v'.symbol j).1 with hRl
  replace hy₀ : P.instr (Rl + cr) = .emit true (Rl + cr + 1) := by convert hy₀ using 2; omega
  replace hy₁ : P.instr (Rl + cr + 1) = .emit true (b + 2) := by convert hy₁ using 2; omega
  replace hn₀ : P.instr (Rl + cr + 2) = .emit true (Rl + cr + 3) := by convert hn₀ using 2; omega
  replace hn₁ : P.instr (Rl + cr + 3) = .emit false (b + 2) := by convert hn₁ using 2; omega
  replace hx : P.instr (Rl + cr + 4) = .emit false (Rl + cr + 5) := by convert hx using 2; omega
  have hbase := le_base v' (d := d)
  -- the arguments of a tuple, found by their ranks
  have chain : ∀ t (ht : t < n' ^ (v'.symbol j).1) (rs : List ℕ), rs.getD 6 0 = t →
      rs.getD 0 0 = a.1 → rs.getD 3 0 = n' → rs.length = regs.length → (∀ x ∈ rs, x ≤ B) →
      ∀ m (hmk : m ≤ (v'.symbol j).1), ∃ rs', P.Reaches (encStructure a) (P.Running B)
        (b + 3, rs) (b + 3 + (d + cs + 6) * m, rs') ∧ rs'.length = regs.length ∧
        rs'.getD 0 0 = a.1 ∧ rs'.getD 3 0 = n' ∧ rs'.getD 6 0 = t ∧ (∀ x ∈ rs', x ≤ B) ∧
        ∀ m' (hm' : m' < m) (i : ι), rs'.getD (blk d m' (e i)) 0 =
          (((rankEquiv I e a.1).symm
            (finFunctionFinEquiv.symm ⟨t, ht⟩ ⟨m', lt_of_lt_of_le hm' hmk⟩)).1 i : ℕ) := by
    intro t ht rs h6 h0' h3' hl hB' m
    induction m with
    | zero => exact fun _ => ⟨rs, Reaches.refl _, hl, h0', h3', h6, hB',
        fun _ h => absurd h (by omega)⟩
    | succ m ih =>
      intro hm
      obtain ⟨rs₁, hreach₁, hl₁, h0₁, h3₁, h6₁, hB₁, hblk₁⟩ := ih (by omega)
      have hpos : 0 < n' := by
        rcases Nat.eq_zero_or_pos n' with h | h
        · rw [h, zero_pow (by omega)] at ht
          omega
        · exact h
      have hcode := CodeAt.flatMap_range
        (f := fun m => unrankCode v v' e I m (b + 3 + (d + cs + 6) * m))
        (fun i => by rw [length_unrankCode, hcs]) hunr m (by omega)
      obtain ⟨rs₂, hreach₂, hl₂, hblk₂, hkeep₂, hB₂⟩ :=
        reaches_unrankCode (v := v) ha (show m ≤ maxArity v' by omega) hcode hnB hNB rs₁ h0₁ h3₁
          h6₁ hpos (by rw [hl₁]; exact hlenD) hB₁
      refine ⟨rs₂, hreach₁.trans ?_, hl₂.trans hl₁, ?_, ?_, ?_, hB₂, fun m' hm' i => ?_⟩
      · rw [hcs, show b + 3 + (d + cs + 6) * m + d + cs + 6 = b + 3 + (d + cs + 6) * (m + 1) by
          rw [Nat.mul_succ]; omega] at hreach₂
        exact hreach₂
      · rw [hkeep₂ 0 (by omega) (by omega) (by omega) (by omega) (fun i _ => by unfold blk; omega),
          h0₁]
      · rw [hkeep₂ 3 (by omega) (by omega) (by omega) (by omega) (fun i _ => by unfold blk; omega),
          h3₁]
      · rw [hkeep₂ 6 (by omega) (by omega) (by omega) (by omega) (fun i _ => by unfold blk; omega),
          h6₁]
      · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hm') with hlt | rfl
        · rw [hkeep₂ _ (blk_lt_base v' (by omega) (e i).2) (by unfold blk; omega)
            (by unfold blk; omega) (by unfold blk; omega)
            (fun i' hi' => blk_ne (by omega) (e i).2 hi'), hblk₁ m' hlt i]
        · rw [hblk₂ i]
          congr 3
  -- the loop over the tuples of elements
  let bit : ℕ → Bool := fun t => if h : t < n' ^ (v'.symbol j).1 then
    decide (RelMap (v'.symbol j).2 ((rankEquiv I e a.1).symm ∘ finFunctionFinEquiv.symm ⟨t, h⟩))
    else false
  let Inv : ℕ → List ℕ → Prop := fun t rs => rs.getD 6 0 = t ∧ rs.getD 0 0 = a.1 ∧
    rs.getD 3 0 = n' ∧ rs.length = regs.length ∧ ∀ x ∈ rs, x ≤ B
  obtain ⟨regsN, hloop, hinvN⟩ := reachesOut_forCode (B := B) (w := encStructure a) hfor Inv
    (fun t => [true, bit t]) hTB
    (fun t rs ⟨h6, _, h3', hl, hB'⟩ => ⟨h6, by simp only [eval_pow, eval_reg, h3'],
      by rw [hl]; omega, hB'⟩)
    (fun t ht rs ⟨h6, h0', h3', hl, hB'⟩ => by
      obtain ⟨rs₁, hreach₁, hl₁, h0₁, h3₁, h6₁, hB₁, hblk₁⟩ :=
        chain t ht rs h6 h0' h3' hl hB' _ le_rfl
      obtain ⟨res, rs₂, hres, hreach₂, hl₂, hkeep₂, hB₂⟩ :=
        reaches_formulaCode ha hnB (fun p : Fin (v'.symbol j).1 × ι => blk d p.1 (e p.2))
          (base v' d) (by omega)
          (fun p => blk_lt_base v' (show (p.1 : ℕ) ≤ maxArity v' by omega) (e p.2).2)
          (fun p => ((rankEquiv I e a.1).symm (finFunctionFinEquiv.symm ⟨t, ht⟩ p.1)).1 p.2)
          (I.rel (v'.symbol j).2) Rl (Rl + cr) (Rl + cr + 2) rs₁ default hrel
          (by rw [hl₁]; exact hlenR) h0₁ hB₁ (fun p => hblk₁ p.1 p.1.2 p.2) (fun i => i.elim0)
      have hbit : bit t = res := by
        have hiff : RelMap (v'.symbol j).2
            ((rankEquiv I e a.1).symm ∘ finFunctionFinEquiv.symm ⟨t, ht⟩) ↔ res = true :=
          hres.symm
        simp only [bit, ht, ↓reduceDIte]
        cases res
        · simpa using hiff
        · simpa using hiff
      have h6₂ : rs₂.getD 6 0 = t := by rw [hkeep₂ 6 (by omega), h6₁]
      refine ⟨rs₂, ?_, h6₂, hB₂, List.getD_set_self (by rw [hl₂, hl₁]; omega), ?_, ?_,
        by rw [List.length_set, hl₂, hl₁], List.forall_mem_set_of_forall_mem hB₂ (by omega)⟩
      · refine hreach₁.reachesOut.trans (hreach₂.reachesOut.trans ?_)
        rw [hbit]
        cases res
        · exact ReachesOut.emit hn₀ hB₂ (ReachesOut.emit hn₁ hB₂ (ReachesOut.refl _))
        · exact ReachesOut.emit hy₀ hB₂ (ReachesOut.emit hy₁ hB₂ (ReachesOut.refl _))
      · rw [List.getD_set_ne (by omega), hkeep₂ 0 (by omega), h0₁]
      · rw [List.getD_set_ne (by omega), hkeep₂ 3 (by omega), h3₁])
    regs hB ⟨List.getD_set_self (by omega), by rw [List.getD_set_ne (by omega), h0],
      by rw [List.getD_set_ne (by omega), h3], by rw [List.length_set],
      List.forall_mem_set_of_forall_mem hB (Nat.zero_le _)⟩
  obtain ⟨-, h0N, h3N, hlN, hBN⟩ := hinvN
  refine ⟨regsN, ?_, hlN, h0N, h3N, hBN⟩
  have hreach := hloop.trans (ReachesOut.emit hx hBN (ReachesOut.refl _))
  rw [show b + (3 + (d + cs + 6) * (v'.symbol j).1 + cr + 5) = Rl + cr + 5 by omega,
    Vocabulary.relTable, ← flatMap_range_pair_append_false]
  exact hreach

variable (v v' e I) in
/-- The codes of the tables of some symbols, one after the other from the label `b`. -/
private noncomputable def tablesCode : ℕ → List (Fin v'.count) → List Instr
  | _, [] => []
  | b, j :: js => tableCode v v' e I j b ++ tablesCode (b + tableLength v' d I j) js

omit [L'.IsRelational] in
private theorem length_tablesCode : ∀ (b : ℕ) (js : List (Fin v'.count)),
    (tablesCode v v' e I b js).length = (js.map (tableLength v' d I)).sum
  | _, [] => rfl
  | b, j :: js => by
    rw [tablesCode, List.length_append, length_tablesCode, List.map_cons, List.sum_cons,
      tableCode]
    simp only [List.length_append, length_unranks, length_formulaCode, List.length_cons,
      List.length_nil, tableLength, relLength]
    rfl

/-- **Emitting the truth tables of some symbols**, one after the other. -/
private theorem reachesOut_tablesCode (ha : v.WellFormed a) (hnB : a.1 ≤ B) (hNB : a.1 ^ d ≤ B) :
    ∀ (js : List (Fin v'.count)) (b : ℕ) (regs : List ℕ),
      P.CodeAt b (tablesCode v v' e I b js) →
      (∀ j ∈ js, (letI := v.decode a; modelCard I e a.1) ^ (v'.symbol j).1 ≤ B) →
      regs.getD 0 0 = a.1 → regs.getD 3 0 = (letI := v.decode a; modelCard I e a.1) →
      base v' d + boundDepth I.domain ≤ regs.length →
      (∀ j ∈ js, base v' d + boundDepth (I.rel (v'.symbol j).2) ≤ regs.length) →
      (∀ r ∈ regs, r ≤ B) →
      ∃ regs', P.ReachesOut (encStructure a) (P.Active B) (b, regs)
        (b + (js.map (tableLength v' d I)).sum, regs')
        (js.flatMap fun j => MultiTapeTM.frame (letI := v.decode a;
          Vocabulary.relTable (I.Model (Fin a.1)) (rankEquiv I e a.1) (v'.symbol j))) ∧
        regs'.length = regs.length ∧ regs'.getD 0 0 = a.1 ∧
        regs'.getD 3 0 = (letI := v.decode a; modelCard I e a.1) ∧ ∀ r ∈ regs', r ≤ B
  | [], b, regs, _, _, h0, h3, _, _, hB => ⟨regs, by simpa using ReachesOut.refl _, rfl, h0, h3, hB⟩
  | j :: js, b, regs, hP, hTB, h0, h3, hlenD, hlenR, hB => by
    rw [tablesCode, codeAt_append] at hP
    have hl : (tableCode v v' e I j b).length = tableLength v' d I j := by
      have := length_tablesCode (v := v) (v' := v') (e := e) (I := I) b [j]
      simpa [tablesCode] using this
    rw [hl] at hP
    obtain ⟨regs₁, hreach₁, hl₁, h0₁, h3₁, hB₁⟩ :=
      reachesOut_tableCode ha j hP.1 hnB hNB (hTB j List.mem_cons_self) regs h0 h3 hlenD
        (hlenR j List.mem_cons_self) hB
    obtain ⟨regs₂, hreach₂, hl₂, h0₂, h3₂, hB₂⟩ :=
      reachesOut_tablesCode ha hnB hNB js _ regs₁ hP.2
        (fun j' hj' => hTB j' (List.mem_cons_of_mem _ hj')) h0₁ h3₁ (hl₁ ▸ hlenD)
        (fun j' hj' => hl₁ ▸ hlenR j' (List.mem_cons_of_mem _ hj')) hB₁
    refine ⟨regs₂, ?_, hl₂.trans hl₁, h0₂, h3₂, hB₂⟩
    rw [List.map_cons, List.sum_cons, ← Nat.add_assoc, List.flatMap_cons]
    exact hreach₁.trans hreach₂

variable (v') in
/-- The code emitting `encStructure (0, [[], …, []])`, a malformed input with one table too many,
then halting; placed at `b`. -/
private def rejectCode (b : ℕ) : List Instr :=
  List.ofFn (fun i : Fin (v'.count + 2) => .emit false (b + i + 1)) ++ [.halt List.nil]

omit [L'.IsRelational] in
private theorem reachesOut_rejectCode {b : ℕ} (hP : P.CodeAt b (rejectCode v' b)) (regs : List ℕ)
    (hB : ∀ r ∈ regs, r ≤ B) :
    P.ReachesOut (encStructure a) (P.Active B) (b, regs) (b + (v'.count + 2), regs)
      (List.replicate (v'.count + 2) false) ∧ P.instr (b + (v'.count + 2)) = .halt [] := by
  rw [rejectCode, codeAt_append, List.length_ofFn] at hP
  refine ⟨?_, (codeAt_cons.mp hP.2).1⟩
  have key : ∀ k ≤ v'.count + 2, P.ReachesOut (encStructure a) (P.Active B)
      (b + (v'.count + 2 - k), regs) (b + (v'.count + 2), regs) (List.replicate k false) := by
    intro k
    induction k with
    | zero => exact fun _ => by simpa using ReachesOut.refl _
    | succ k ih =>
      intro hk
      have hc : P.instr (b + (v'.count + 2 - (k + 1))) =
          .emit false (b + (v'.count + 2 - (k + 1)) + 1) := by
        rw [hP.1 (v'.count + 2 - (k + 1)) (by rw [List.length_ofFn]; omega)]
        simp only [List.getElem_ofFn]
      refine ReachesOut.emit hc hB ?_
      rw [show b + (v'.count + 2 - (k + 1)) + 1 = b + (v'.count + 2 - k) by omega]
      exact ih (by omega)
  simpa using key (v'.count + 2) le_rfl

omit [L'.IsRelational] in
private theorem encStructure_reject :
    encStructure ((0, List.replicate (v'.count + 1) []) : EncodedStructure) =
      List.replicate (v'.count + 2) false := by
  have h (n : ℕ) : (List.replicate n ([] : List Bool)).flatMap MultiTapeTM.frame =
      List.replicate n false := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [List.replicate_succ, List.flatMap_cons,
        MultiTapeTM.frame, List.flatMap_nil, List.nil_append, List.singleton_append, ih]
  rw [encStructure_eq, h]
  simp only [List.replicate_zero, MultiTapeTM.frame, List.flatMap_nil, List.nil_append,
    List.singleton_append]
  rfl

/-! ### The complete transducer -/

variable (v v' e I d)

/-- The starting label of the domain scan, immediately after the shape check. -/
private def scanStart : ℕ := 4 + 6 * v.count

/-- The starting label of the relation tables, immediately after the domain scan. -/
private def tablesStart : ℕ := scanStart v + d + codeLength I.domain + 8

/-- The accepting halt label, immediately after the relation tables. -/
private noncomputable def haltLabel : ℕ := tablesStart v d I +
  ((List.finRange v'.count).map (tableLength v' d I)).sum

/-- Enough registers for each relation formula and the domain formula. -/
private def registerCount : ℕ := base v' d +
  max (boundDepth I.domain) (Finset.univ.sup fun j => boundDepth (I.rel (v'.symbol j).2))

/-- The counter program checking shape, enumerating the interpreted domain, and emitting its
relation tables. A malformed input produces a fixed malformed output. -/
private noncomputable def program : CounterProgram where
  code := shapeCode v 0 (scanStart v) (haltLabel v v' d I + 1) ++
    scanCode v v' e I (scanStart v) ++
    tablesCode v v' e I (tablesStart v d I) (List.finRange v'.count) ++
    [.halt List.nil] ++ rejectCode v' (haltLabel v v' d I + 1)
  registers := registerCount v' d I

/-- A polynomial exponent bounding every register of the transducer. -/
private def exponent : ℕ := regExponent v + d * (maxArity v' + 1) + 1

end Transducer

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L.IsRelational] [L'.IsRelational]
  {ι : Type} {d : ℕ} (I : Interpretation L L' ι) (v : Vocabulary L) (v' : Vocabulary L')
  (e : ι ≃ Fin d)

/-- Encode the structure interpreted in a well-formed input, numbering its elements by ranks.
Malformed inputs map to a fixed malformed structure encoding. This includes empty structures,
empty interpreted domains, nullary relations, and interpretations of dimension zero. -/
noncomputable def encodedMap (a : EncodedStructure) : EncodedStructure :=
  if v.WellFormed a then
    letI := v.decode a
    v'.encode (I.Model (Fin a.1)) (rankEquiv I e a.1)
  else (0, List.replicate (v'.count + 1) [])

open Transducer in
/-- Computing an order-free first-order interpretation on encoded finite relational structures
uses logarithmic work space. The output is streamed, including its unary cardinality frame;
malformed inputs map to malformed outputs. -/
theorem computableInLogSpace_encodedMap :
    MultiTapeTM.ComputableInLogSpace (I.encodedMap v v' e) encStructure encStructure := by
  classical
  let P := program v v' d e I
  refine P.computableInLogSpace_of_reachesOut (exponent v v' d) fun a => ?_
  let B := ((encStructure a).length + 1) ^ exponent v v' d
  have hpow (k : ℕ) (hk : k ≤ exponent v v' d) :
      a.1 ^ k ≤ B :=
    (Nat.pow_le_pow_left ((card_le_length_encStructure a).trans (Nat.le_succ _)) k).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) hk)
  have hE : regExponent v ≤ exponent v v' d := by unfold exponent; omega
  have hwB : (encStructure a).length ≤ B :=
    (length_le_pow_regExponent v a).trans (Nat.pow_le_pow_right (Nat.succ_pos _) hE)
  have hnB : a.1 ≤ B := (card_le_length_encStructure a).trans hwB
  have hdE : d ≤ exponent v v' d := by
    have := Nat.mul_le_mul_left d (show 1 ≤ maxArity v' + 1 by omega)
    simp only [Nat.mul_one] at this
    unfold exponent
    omega
  have hNB : a.1 ^ d ≤ B := hpow d hdE
  have hcode : P.CodeAt 0 P.code := by
    exact codeAt_of_code_eq (pre := []) (post := []) (by simp)
  change P.CodeAt 0 (_ ++ _ ++ _ ++ _ ++ _) at hcode
  rw [codeAt_append, codeAt_append, codeAt_append, codeAt_append] at hcode
  obtain ⟨⟨⟨⟨hshape, hscan⟩, htables⟩, hhalt⟩, hreject⟩ := hcode
  have hscanLen : (scanCode v v' e I (scanStart v)).length = d + codeLength I.domain + 8 := by
    simp only [scanCode, List.length_append, List.length_cons, List.length_nil,
      length_coordsCode, length_domCode, forCode]
    omega
  simp only [List.length_append, length_shapeCode, hscanLen, length_tablesCode,
    List.length_cons, List.length_nil, Nat.zero_add] at hscan htables hhalt hreject
  change P.CodeAt (scanStart v) _ at hscan
  have htabStart : 4 + 6 * v.count + (d + codeLength I.domain + 8) = tablesStart v d I := by
    unfold tablesStart scanStart
    omega
  rw [htabStart] at htables hhalt hreject
  change P.CodeAt (haltLabel v v' d I) [.halt List.nil] at hhalt
  change P.CodeAt (haltLabel v v' d I + 1) _ at hreject
  have hhalt' := (codeAt_cons.mp hhalt).1
  have hlenD : base v' d + boundDepth I.domain ≤ P.registers := by
    exact Nat.add_le_add_left (le_max_left _ _) _
  have hlenR (j : Fin v'.count) : base v' d + boundDepth (I.rel (v'.symbol j).2) ≤
      P.registers :=
    Nat.add_le_add_left ((Finset.le_sup (f := fun j => boundDepth (I.rel (v'.symbol j).2))
      (Finset.mem_univ j)).trans (le_max_right _ _)) _
  have hbase := le_base v' (d := d)
  obtain ⟨rs, hshapeRun, hlen, h0, hB⟩ := reaches_shapeCode (B := B) (a := a) hshape
    (fun i => (pow_arityAt_le v a i).trans (Nat.pow_le_pow_right (Nat.succ_pos _) hE))
    hwB (List.replicate P.registers 0) (by simp) (by simp only [List.length_replicate]; omega)
    (by simp)
  by_cases ha : v.WellFormed a
  · rw [ite_eq_left ha] at hshapeRun
    obtain ⟨rs₁, hscanRun, hlen₁, h0₁, h3₁, hB₁⟩ := reachesOut_scanCode ha hscan hnB hNB rs
      (h0 ha) (by rw [hlen, List.length_replicate]; exact hlenD) hB
    change P.ReachesOut _ _ _ (tablesStart v d I, rs₁) _ at hscanRun
    have hTB (j : Fin v'.count) :
        (letI := v.decode a; modelCard I e a.1) ^ (v'.symbol j).1 ≤ B := by
      let _ := v.decode a
      calc
        modelCard I e a.1 ^ (v'.symbol j).1 ≤ (a.1 ^ d) ^ (v'.symbol j).1 :=
          Nat.pow_le_pow_left modelCard_le_pow _
        _ = a.1 ^ (d * (v'.symbol j).1) := (pow_mul _ _ _).symm
        _ ≤ B := hpow _ (by
          have hmul : d * (v'.symbol j).1 ≤ d * (maxArity v' + 1) :=
            Nat.mul_le_mul_left d ((arity_le_maxArity j).trans (Nat.le_succ _))
          unfold exponent
          omega)
    obtain ⟨rs₂, htablesRun, _, _, _, hB₂⟩ := reachesOut_tablesCode ha hnB hNB
      (List.finRange v'.count) _ rs₁ htables (fun j _ => hTB j) h0₁ h3₁
      (by rw [hlen₁, hlen, List.length_replicate]; exact hlenD)
      (fun j _ => by rw [hlen₁, hlen, List.length_replicate]; exact hlenR j) hB₁
    refine ⟨(haltLabel v v' d I, rs₂), _, [],
      hshapeRun.reachesOut.trans (hscanRun.trans htablesRun), hhalt', ?_, hB₂⟩
    simp only [List.nil_append, List.append_nil, encodedMap, ha, ↓reduceIte,
      encStructure_eq, Vocabulary.encode]
    congr 1
    rw [List.ofFn_eq_map, List.flatMap_map]
  · rw [ite_eq_right ha] at hshapeRun
    obtain ⟨hrun, hhalt⟩ := reachesOut_rejectCode hreject rs hB
    refine ⟨(_, rs), _, [], hshapeRun.reachesOut.trans hrun, hhalt, ?_, hB⟩
    simp only [List.nil_append, List.append_nil, encodedMap, ha, ↓reduceIte]
    exact encStructure_reject

end Cslib.Logic.FO.Interpretation

namespace Cslib.Logic.FO

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L.IsRelational] [L'.IsRelational]
  (v : Vocabulary L) (v' : Vocabulary L')
  {K : Set (Bundled.{0} L.Structure)} {K' : Set (Bundled.{0} L'.Structure)}

/-- An order-free first-order interpretation reduction induces a logspace many-one reduction
between the query languages, provided the target class is closed under isomorphism. The
transducer rejects malformed instances and includes empty structures and empty domains. -/
theorem Reduces.logSpaceReducible (h : Reduces K K') (hK' : IsoClosed K') :
    Complexity.LogSpaceReducible encStructure encStructure (v.queryLanguage K)
      (v'.queryLanguage K') := by
  classical
  obtain ⟨ι, hι, I, hI⟩ := h
  let _ := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  refine ⟨I.encodedMap v v' e, I.computableInLogSpace_encodedMap v v' e, fun a => ?_⟩
  by_cases ha : v.WellFormed a
  · rw [Interpretation.encodedMap, ite_eq_left ha,
      ha.mem_queryLanguage_iff]
    let _ := v.decode a
    rw [v'.mem_queryLanguage_encode hK']
    have : Finite (v.decoded a) := inferInstanceAs (Finite (Fin a.1))
    exact hI (v.decoded a)
  · have hbad : ¬ v'.WellFormed (0, List.replicate (v'.count + 1) []) := by
      intro hbad
      have := hbad.1
      simp only [List.length_replicate] at this
      omega
    simp only [Interpretation.encodedMap, ha, ↓reduceIte, Vocabulary.mem_queryLanguage,
      hbad, false_and]

/-- Query languages in `L` are closed under order-free first-order interpretation reductions
with an isomorphism-closed target class. -/
theorem Reduces.queryLanguage_mem_L (h : Reduces K K') (hK' : IsoClosed K')
    (hL : v'.queryLanguage K' ∈ Complexity.L encStructure) :
    v.queryLanguage K ∈ Complexity.L encStructure :=
  (h.logSpaceReducible v v' hK').mem_L hL

/-- Query languages in `P` are closed under order-free first-order interpretation reductions
with an isomorphism-closed target class. -/
theorem Reduces.queryLanguage_mem_P (h : Reduces K K') (hK' : IsoClosed K')
    (hP : v'.queryLanguage K' ∈ Complexity.P encStructure) :
    v.queryLanguage K ∈ Complexity.P encStructure :=
  (h.logSpaceReducible v v' hK').polyTimeReducible.mem_P hP

end Cslib.Logic.FO
