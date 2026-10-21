/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered
public import Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder.Output
public import Complexity.Logics.FirstOrder.Ordered.FullTuple.Encoding
import Complexity.Foundations.Data.List.Basic

/-!
# Canonical full-tuple interpretations in logarithmic space

The actual encoded map of a fixed full-tuple interpretation is computed by a native counter
program with streamed output. It checks the source shape and size before emitting output,
then writes the unary target cardinality and each input-relation table. Target elements use
lexicographic rank, while table arguments keep their existing least-significant-first order.
Canonical source numeric atoms use the proved ordered compiler; no numeric tables are supplied.

## Main results

* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.computableInLogSpace_encodedMap`: native output.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.logSpaceReducible_onSentence`: the exact map
  reduces the pulled-back ordered query to the target query.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Theorem 3.1 and Propositions 3.5/3.10.
  This is the full-tuple slice; restricted-domain numeric reconstruction and capture remain open.
* The order-free interpretation writer, shared counter-program simulation and Christian
  Reitwiessner's native arithmetic are reused with their source authorship retained.
-/

@[expose] public section

open FirstOrder Language Structure Turing Turing.CounterProgram

namespace Cslib.Logic.FO.Ordered.FullTupleInterpretation

open Vocabulary.ModelChecker Vocabulary.ModelChecker.Writer Expr

namespace Transducer

variable {L L' : Language}
  (v : Vocabulary L) (v' : Vocabulary L') {k : ℕ} (I : FullTupleInterpretation L L' k)

/-- The largest target input-relation arity. -/
private def maxArity : ℕ := Finset.univ.sup v'.arity

/-- Quantified variables follow all coordinate blocks. -/
private def base (k : ℕ) : ℕ := 8 + k * (maxArity v' + 1)

private theorem tupleReg_le_base {m : ℕ} (hm : m ≤ maxArity v') :
    tupleReg k m k ≤ base v' k := by
  unfold tupleReg base
  have h := Nat.mul_le_mul_left k (Nat.succ_le_succ hm)
  rw [Nat.mul_succ, Nat.mul_succ] at h
  lia

private theorem tupleReg_lt_base {m i : ℕ} (hm : m ≤ maxArity v') (hi : i < k) :
    tupleReg k m i < base v' k := by
  have h := tupleReg_le_base (k := k) v' hm
  unfold tupleReg at h ⊢
  lia

private theorem le_base : 8 ≤ base v' k := Nat.le_add_right _ _

/-- Set the target size, then stream its unary cardinality frame. -/
private def headerCode (k b : ℕ) : List Instr :=
  [.assign 3 (pow (reg 0) k) (b + 1)] ++
  forCode (b + 1) 6 (reg 3) (b + 4) (b + 6) ++
  [.emit true (b + 5), .emit true (b + 3), .emit false (b + 7)]

private theorem length_headerCode (k b : ℕ) : (headerCode k b).length = 7 := rfl

variable {P : CounterProgram} {a : EncodedStructure} {B : ℕ}

private theorem reachesOut_headerCode {b : ℕ} (hP : P.CodeAt b (headerCode k b))
    (hNB : a.1 ^ k ≤ B) (regs : List ℕ) (h0 : regs.getD 0 0 = a.1)
    (hlen : 8 ≤ regs.length) (hB : ∀ r ∈ regs, r ≤ B) :
    ∃ regs', P.ReachesOut (encStructure a) (P.Active B) (b, regs) (b + 7, regs')
      (MultiTapeTM.frame (List.replicate (a.1 ^ k) true)) ∧
      regs'.length = regs.length ∧ regs'.getD 0 0 = a.1 ∧
      regs'.getD 3 0 = a.1 ^ k ∧ ∀ r ∈ regs', r ≤ B := by
  rw [headerCode, codeAt_append, codeAt_append] at hP
  simp only [List.length_append, forCode, List.length_cons, List.length_nil,
    Nat.reduceAdd, codeAt_cons] at hP
  obtain ⟨⟨⟨hset, -⟩, hinit, htest, hinc, -⟩, hout₁, hout₂, hend, -⟩ := hP
  let N := a.1 ^ k
  let Inv : ℕ → List ℕ → Prop := fun t rs => rs.getD 6 0 = t ∧ rs.getD 0 0 = a.1 ∧
    rs.getD 3 0 = N ∧ rs.length = regs.length ∧ ∀ r ∈ rs, r ≤ B
  have hfor : P.CodeAt (b + 1) (forCode (b + 1) 6 (reg 3) (b + 4) (b + 6)) := by
    simpa only [forCode, codeAt_cons, Nat.add_assoc] using ⟨hinit, htest, hinc, codeAt_nil⟩
  have hB' : ∀ r ∈ regs.set 3 N, r ≤ B := List.forall_mem_set_of_forall_mem hB hNB
  obtain ⟨rs, hloop, _, h0', h3', hl', hB''⟩ :=
    reachesOut_forCode (w := encStructure a) (N := N) hfor Inv
    (fun t => [true, if t < N then true else false]) hNB
    (fun t rs ⟨h6, _, h3, hl, hb⟩ => ⟨h6, by simpa only [eval_reg] using h3,
      by rw [hl]; lia, hb⟩)
    (fun t ht rs ⟨h6, h₀, h₃, hl, hb⟩ => by
      refine ⟨rs, ?_, h6, hb, List.getD_set_self (by rw [hl]; lia), ?_, ?_,
        by rw [List.length_set, hl], List.forall_mem_set_of_forall_mem hb (by lia)⟩
      · simpa only [ht, ↓reduceIte, Nat.add_assoc, Nat.reduceAdd] using
          ReachesOut.emit (w := encStructure a) hout₁ hb
            (ReachesOut.emit hout₂ hb (ReachesOut.refl _))
      · rw [List.getD_set_ne (by decide), h₀]
      · rw [List.getD_set_ne (by decide), h₃])
    (regs.set 3 N) hB'
    ⟨List.getD_set_self (by simpa only [List.length_set] using (show 6 < regs.length by lia)),
      by rw [List.getD_set_ne (by decide), List.getD_set_ne (by decide), h0],
      by rw [List.getD_set_ne (by decide), List.getD_set_self (by lia)],
      by simp only [List.length_set], List.forall_mem_set_of_forall_mem hB' (Nat.zero_le _)⟩
  refine ⟨rs, ReachesOut.assign hset hB ?_, hl', h0', h3', hB''⟩
  simp only [eval_pow, eval_reg, h0]
  have hr := hloop.trans (ReachesOut.emit hend hB'' (ReachesOut.refl _))
  simpa only [List.ofFn_const, Nat.add_assoc] using
    hr.of_eq (flatMap_range_pair_append_false N (fun _ => true))

/-- Extract one target argument from the outer table index and write its source digits.
The formula reads this block in reverse, so its logical coordinates have lexicographic rank. -/
private def argumentCode (k m b : ℕ) : List Instr :=
  [.assign 4 (mod (div (reg 6) (pow (reg 3) m)) (reg 3)) (b + 1)] ++
  coordinatesCode k m (b + 1)

private theorem length_argumentCode (k m b : ℕ) : (argumentCode k m b).length = k + 1 := by
  simp [argumentCode, length_coordinatesCode]

private theorem reaches_argumentCode {m b t : ℕ} (hn : 0 < a.1)
    (hP : P.CodeAt b (argumentCode k m b)) (hnB : a.1 ≤ B) (hNB : a.1 ^ k ≤ B)
    (regs : List ℕ) (h0 : regs.getD 0 0 = a.1) (h3 : regs.getD 3 0 = a.1 ^ k)
    (h6 : regs.getD 6 0 = t) (hlen : tupleReg k m k ≤ regs.length)
    (hB : ∀ r ∈ regs, r ≤ B) :
    ∃ regs', P.Reaches (encStructure a) (P.Running B) (b, regs) (b + (k + 1), regs') ∧
      regs'.length = regs.length ∧
      (∀ i : Fin k, regs'.getD (tupleReg k m i.rev) 0 =
        (lexEquiv.symm (⟨t / (a.1 ^ k) ^ m % a.1 ^ k,
          Nat.mod_lt _ (Nat.pow_pos hn)⟩ : Fin (a.1 ^ k)) i).val) ∧
      (∀ r, r ≠ 4 → (∀ i < k, r ≠ tupleReg k m i) →
        regs'.getD r 0 = regs.getD r 0) ∧ ∀ r ∈ regs', r ≤ B := by
  rw [argumentCode, codeAt_append, List.length_singleton, codeAt_cons] at hP
  obtain ⟨⟨hset, -⟩, hcoords⟩ := hP
  let u := t / (a.1 ^ k) ^ m % a.1 ^ k
  have hu : u < a.1 ^ k := Nat.mod_lt _ (Nat.pow_pos hn)
  have hlen₀ : 8 ≤ regs.length := by unfold tupleReg at hlen; lia
  obtain ⟨rs, hr, hl, hv, hkeep, hb⟩ := reaches_coordinatesCode (w := encStructure a) hcoords hu
    hnB (regs.set 4 u) (by rw [List.getD_set_ne (by decide), h0])
    (List.getD_set_self (by lia)) (by rw [List.length_set]; exact hlen)
    (List.forall_mem_set_of_forall_mem hB (hu.le.trans hNB))
  refine ⟨rs, Reaches.assign hset hB ?_, hl.trans (List.length_set ..), fun i => ?_,
    fun r h4 hne => ?_, hb⟩
  · simpa only [eval_mod, eval_div, eval_pow, eval_reg, h3, h6,
      Nat.add_assoc, Nat.add_comm 1 k] using hr
  · rw [hv i.rev i.rev.isLt, lexEquiv_symm_apply_val]
  · rw [hkeep r hne, List.getD_set_ne h4.symm]


private def relLength (j : Fin v'.count) : ℕ := codeLength (I.rel (v'.symbol j).2)

private def tableLength (j : Fin v'.count) : ℕ :=
  3 + (k + 1) * (v'.symbol j).1 + relLength v' I j + 5

variable [L.IsRelational]

/-- Stream one relation table in outer `tupleIndex` order, with lexicographic argument blocks. -/
private def relTableCode (j : Fin v'.count) (b : ℕ) : List Instr :=
  forCode b 6 (pow (reg 3) (v'.symbol j).1) (b + 3)
    (b + 3 + (k + 1) * (v'.symbol j).1 + relLength v' I j + 4) ++
  (List.range (v'.symbol j).1).flatMap
    (fun m => argumentCode k m (b + 3 + (k + 1) * m)) ++
  ModelChecker.formulaCode v (fun p : Fin (v'.symbol j).1 × Fin k => tupleReg k p.1 p.2.rev)
    (base v' k) (I.rel (v'.symbol j).2) (b + 3 + (k + 1) * (v'.symbol j).1)
    (b + 3 + (k + 1) * (v'.symbol j).1 + relLength v' I j)
    (b + 3 + (k + 1) * (v'.symbol j).1 + relLength v' I j + 2) ++
  [.emit true (b + 3 + (k + 1) * (v'.symbol j).1 + relLength v' I j + 1),
   .emit true (b + 2),
   .emit true (b + 3 + (k + 1) * (v'.symbol j).1 + relLength v' I j + 3),
   .emit false (b + 2),
   .emit false (b + 3 + (k + 1) * (v'.symbol j).1 + relLength v' I j + 5)]

private theorem arity_le_maxArity (j : Fin v'.count) : (v'.symbol j).1 ≤ maxArity v' :=
  Finset.le_sup (f := v'.arity) (Finset.mem_univ j)

private theorem length_arguments (b r : ℕ) :
    ((List.range r).flatMap fun m => argumentCode k m (b + 3 + (k + 1) * m)).length =
      (k + 1) * r := by
  rw [List.length_flatMap]
  simp only [length_argumentCode, List.map_const', List.length_range, List.sum_replicate,
    smul_eq_mul, Nat.mul_comm]

variable {v v' I} [L'.IsRelational]

/-- The native writer emits the exact table of the identity-numbered canonical target. -/
private theorem reachesOut_relTableCode (ha : v.WellFormed a) [Fact (2 ≤ a.1)]
    (j : Fin v'.count) {b : ℕ} (hP : P.CodeAt b (relTableCode v v' I j b))
    (hnB : a.1 ≤ B) (hNB : a.1 ^ k ≤ B) (hTB : (a.1 ^ k) ^ (v'.symbol j).1 ≤ B)
    (regs : List ℕ) (h0 : regs.getD 0 0 = a.1) (h3 : regs.getD 3 0 = a.1 ^ k)
    (hlenR : base v' k + boundDepth (I.rel (v'.symbol j).2) ≤ regs.length)
    (hB : ∀ r ∈ regs, r ≤ B) :
    ∃ regs', P.ReachesOut (encStructure a) (P.Active B) (b, regs)
      (b + tableLength v' I j, regs')
      (MultiTapeTM.frame (letI := v.decode a; letI := I.inputStructure (n := a.1);
        Vocabulary.relTable (Fin (a.1 ^ k)) (Equiv.refl _) (v'.symbol j))) ∧
      regs'.length = regs.length ∧ regs'.getD 0 0 = a.1 ∧
      regs'.getD 3 0 = a.1 ^ k ∧ ∀ r ∈ regs', r ≤ B := by
  classical
  let _ := v.decode a
  let _ := I.inputStructure (n := a.1)
  have hn : 0 < a.1 := lt_of_lt_of_le (by decide) (Fact.out : 2 ≤ a.1)
  have hkm := arity_le_maxArity v' j
  have hlu := length_arguments (k := k) b (v'.symbol j).1
  rw [relTableCode] at hP
  rw [tableLength]
  generalize hcr : relLength v' I j = cr at hP ⊢
  let n' := a.1 ^ k
  rw [codeAt_append, codeAt_append, codeAt_append] at hP
  obtain ⟨⟨⟨hfor, hargs⟩, hrel⟩, htail⟩ := hP
  have hlf : (forCode b 6 (pow (reg 3) (v'.symbol j).1) (b + 3)
      (b + 3 + (k + 1) * (v'.symbol j).1 + cr + 4)).length = 3 := rfl
  rw [List.length_append, hlu, hlf] at hrel
  rw [List.length_append, List.length_append, hlu, hlf, ModelChecker.length_formulaCode,
    show codeLength (I.rel (v'.symbol j).2) = cr from hcr] at htail
  rw [hlf] at hargs
  rw [show b + (3 + (k + 1) * (v'.symbol j).1) = b + 3 + (k + 1) * (v'.symbol j).1 by
    lia] at hrel
  simp only [codeAt_cons] at htail
  obtain ⟨hy₀, hy₁, hn₀, hn₁, hx, -⟩ := htail
  set Rl := b + 3 + (k + 1) * (v'.symbol j).1 with hRl
  replace hy₀ : P.instr (Rl + cr) = .emit true (Rl + cr + 1) := by convert hy₀ using 2; lia
  replace hy₁ : P.instr (Rl + cr + 1) = .emit true (b + 2) := by convert hy₁ using 2; lia
  replace hn₀ : P.instr (Rl + cr + 2) = .emit true (Rl + cr + 3) := by convert hn₀ using 2; lia
  replace hn₁ : P.instr (Rl + cr + 3) = .emit false (b + 2) := by convert hn₁ using 2; lia
  replace hx : P.instr (Rl + cr + 4) = .emit false (Rl + cr + 5) := by convert hx using 2; lia
  have hbase := le_base (k := k) v'
  -- Decode outer arguments without changing the table counter or previous blocks.
  have chain : ∀ t (ht : t < n' ^ (v'.symbol j).1) (rs : List ℕ), rs.getD 6 0 = t →
      rs.getD 0 0 = a.1 → rs.getD 3 0 = n' → rs.length = regs.length → (∀ x ∈ rs, x ≤ B) →
      ∀ m (hmk : m ≤ (v'.symbol j).1), ∃ rs', P.Reaches (encStructure a) (P.Running B)
        (b + 3, rs) (b + 3 + (k + 1) * m, rs') ∧ rs'.length = regs.length ∧
        rs'.getD 0 0 = a.1 ∧ rs'.getD 3 0 = n' ∧ rs'.getD 6 0 = t ∧ (∀ x ∈ rs', x ≤ B) ∧
        ∀ m' (hm' : m' < m) (i : Fin k), rs'.getD (tupleReg k m' i.rev) 0 =
          (lexEquiv.symm (finFunctionFinEquiv.symm ⟨t, ht⟩
            ⟨m', lt_of_lt_of_le hm' hmk⟩) i).val := by
    intro t ht rs h6 h0' h3' hl hB' m
    induction m with
    | zero => exact fun _ => ⟨rs, Reaches.refl _, hl, h0', h3', h6, hB',
        fun _ h => absurd h (by lia)⟩
    | succ m ih =>
      intro hm
      obtain ⟨rs₁, hreach₁, hl₁, h0₁, h3₁, h6₁, hB₁, hblk₁⟩ := ih (by lia)
      have hcode := CodeAt.flatMap_range
        (f := fun m => argumentCode k m (b + 3 + (k + 1) * m))
        (fun _ => length_argumentCode ..) hargs m (by lia)
      obtain ⟨rs₂, hreach₂, hl₂, hblk₂, hkeep₂, hB₂⟩ := reaches_argumentCode hn hcode hnB hNB
        rs₁ h0₁ h3₁ h6₁
        ((tupleReg_le_base v' (show m ≤ maxArity v' by lia)).trans
          (by rw [hl₁]; lia)) hB₁
      refine ⟨rs₂, hreach₁.trans ?_, hl₂.trans hl₁, ?_, ?_, ?_, hB₂, fun m' hm' i => ?_⟩
      · rw [show b + 3 + (k + 1) * m + (k + 1) = b + 3 + (k + 1) * (m + 1) by
          rw [Nat.mul_succ]; lia] at hreach₂
        exact hreach₂
      · rw [hkeep₂ 0 (by decide) (fun i _ => by unfold tupleReg; lia), h0₁]
      · rw [hkeep₂ 3 (by decide) (fun i _ => by unfold tupleReg; lia), h3₁]
      · rw [hkeep₂ 6 (by decide) (fun i _ => by unfold tupleReg; lia), h6₁]
      · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hm') with hlt | rfl
        · rw [hkeep₂ _ (by unfold tupleReg; lia)
            (fun i' hi' => tupleReg_ne (by lia) i.rev.isLt hi'), hblk₁ m' hlt i]
        · rw [hblk₂ i, lexEquiv_symm_apply_val, lexEquiv_symm_apply_val,
            finFunctionFinEquiv_symm_apply_val]
  let bit : ℕ → Bool := fun t => if h : t < n' ^ (v'.symbol j).1 then
    decide (RelMap (v'.symbol j).2 (finFunctionFinEquiv.symm ⟨t, h⟩)) else false
  let Inv : ℕ → List ℕ → Prop := fun t rs => rs.getD 6 0 = t ∧ rs.getD 0 0 = a.1 ∧
    rs.getD 3 0 = n' ∧ rs.length = regs.length ∧ ∀ x ∈ rs, x ≤ B
  obtain ⟨regsN, hloop, hinvN⟩ := reachesOut_forCode (B := B) (w := encStructure a)
    (N := n' ^ (v'.symbol j).1) hfor Inv
    (fun t => [true, bit t]) hTB
    (fun t rs ⟨h6, _, h3', hl, hB'⟩ => ⟨h6, by simp only [eval_pow, eval_reg, h3'],
      by rw [hl]; lia, hB'⟩)
    (fun t ht rs ⟨h6, h0', h3', hl, hB'⟩ => by
      obtain ⟨rs₁, hreach₁, hl₁, h0₁, h3₁, h6₁, hB₁, hblk₁⟩ :=
        chain t ht rs h6 h0' h3' hl hB' _ le_rfl
      obtain ⟨res, rs₂, hres, hreach₂, hl₂, hkeep₂, hB₂⟩ :=
        ModelChecker.reaches_formulaCode ha hnB
          (fun p : Fin (v'.symbol j).1 × Fin k => tupleReg k p.1 p.2.rev)
          (base v' k) (by lia)
          (fun p => tupleReg_lt_base v' (show p.1.val ≤ maxArity v' by lia) p.2.rev.isLt)
          (fun p => lexEquiv.symm (finFunctionFinEquiv.symm ⟨t, ht⟩ p.1) p.2)
          (I.rel (v'.symbol j).2) Rl (Rl + cr) (Rl + cr + 2) rs₁ default hrel
          (by rw [hl₁]; exact hlenR) h0₁ hB₁ (fun p => hblk₁ p.1 p.1.2 p.2) (fun i => i.elim0)
      have hbit : bit t = res := by
        have hiff : RelMap (v'.symbol j).2 (finFunctionFinEquiv.symm ⟨t, ht⟩) ↔ res = true :=
          by
            change (I.rel (v'.symbol j).2).Realize
              (fun p => lexEquiv.symm (finFunctionFinEquiv.symm ⟨t, ht⟩ p.1) p.2) ↔ _
            exact hres.symm
        simp only [bit, ht, ↓reduceDIte]
        cases res <;> simpa using hiff
      have h6₂ : rs₂.getD 6 0 = t := by rw [hkeep₂ 6 (by lia), h6₁]
      refine ⟨rs₂, ?_, h6₂, hB₂, List.getD_set_self (by rw [hl₂, hl₁]; lia), ?_, ?_,
        by rw [List.length_set, hl₂, hl₁], List.forall_mem_set_of_forall_mem hB₂ (by lia)⟩
      · refine hreach₁.reachesOut.trans (hreach₂.reachesOut.trans ?_)
        rw [hbit]
        cases res
        · exact ReachesOut.emit hn₀ hB₂ (ReachesOut.emit hn₁ hB₂ (ReachesOut.refl _))
        · exact ReachesOut.emit hy₀ hB₂ (ReachesOut.emit hy₁ hB₂ (ReachesOut.refl _))
      · rw [List.getD_set_ne (by decide), hkeep₂ 0 (by lia), h0₁]
      · rw [List.getD_set_ne (by decide), hkeep₂ 3 (by lia), h3₁])
    regs hB ⟨List.getD_set_self (by lia), by rw [List.getD_set_ne (by decide), h0],
      by rw [List.getD_set_ne (by decide), h3], by rw [List.length_set],
      List.forall_mem_set_of_forall_mem hB (Nat.zero_le _)⟩
  obtain ⟨-, h0N, h3N, hlN, hBN⟩ := hinvN
  refine ⟨regsN, ?_, hlN, h0N, h3N, hBN⟩
  have hreach := hloop.trans (ReachesOut.emit hx hBN (ReachesOut.refl _))
  rw [show b + (3 + (k + 1) * (v'.symbol j).1 + cr + 5) = Rl + cr + 5 by lia,
    Vocabulary.relTable, ← flatMap_range_pair_append_false]
  refine hreach.of_eq ?_
  simp only [bit, n', Equiv.refl_symm, Equiv.coe_refl, Function.id_comp]
  congr 2


variable (v v' I) in
/-- Concatenate the writers for a fixed list of target relation symbols. -/
private def tablesCode : ℕ → List (Fin v'.count) → List Instr
  | _, [] => []
  | b, j :: js => relTableCode v v' I j b ++ tablesCode (b + tableLength v' I j) js

omit [L'.IsRelational] in
private theorem length_tablesCode : ∀ (b : ℕ) (js : List (Fin v'.count)),
    (tablesCode v v' I b js).length = (js.map (tableLength v' I)).sum
  | _, [] => rfl
  | b, j :: js => by
    rw [tablesCode, List.length_append, length_tablesCode, List.map_cons, List.sum_cons,
      relTableCode]
    simp only [List.length_append, length_arguments, ModelChecker.length_formulaCode,
      List.length_cons, List.length_nil, tableLength, relLength]
    rfl

private theorem reachesOut_tablesCode (ha : v.WellFormed a) [Fact (2 ≤ a.1)]
    (hnB : a.1 ≤ B) (hNB : a.1 ^ k ≤ B) :
    ∀ (js : List (Fin v'.count)) (b : ℕ) (regs : List ℕ),
      P.CodeAt b (tablesCode v v' I b js) →
      (∀ j ∈ js, (a.1 ^ k) ^ (v'.symbol j).1 ≤ B) →
      regs.getD 0 0 = a.1 → regs.getD 3 0 = a.1 ^ k →
      (∀ j ∈ js, base v' k + boundDepth (I.rel (v'.symbol j).2) ≤ regs.length) →
      (∀ r ∈ regs, r ≤ B) →
      ∃ regs', P.ReachesOut (encStructure a) (P.Active B) (b, regs)
        (b + (js.map (tableLength v' I)).sum, regs')
        (js.flatMap fun j => MultiTapeTM.frame (letI := v.decode a;
          letI := I.inputStructure (n := a.1);
          Vocabulary.relTable (Fin (a.1 ^ k)) (Equiv.refl _) (v'.symbol j))) ∧
        regs'.length = regs.length ∧ regs'.getD 0 0 = a.1 ∧
        regs'.getD 3 0 = a.1 ^ k ∧ ∀ r ∈ regs', r ≤ B
  | [], b, regs, _, _, h0, h3, _, hB => ⟨regs, by simpa using ReachesOut.refl _, rfl, h0, h3, hB⟩
  | j :: js, b, regs, hP, hTB, h0, h3, hlenR, hB => by
    rw [tablesCode, codeAt_append] at hP
    have hl : (relTableCode v v' I j b).length = tableLength v' I j := by
      have := length_tablesCode (v := v) (v' := v') (I := I) b [j]
      simpa [tablesCode] using this
    rw [hl] at hP
    obtain ⟨regs₁, hreach₁, hl₁, h0₁, h3₁, hB₁⟩ :=
      reachesOut_relTableCode ha j hP.1 hnB hNB (hTB j List.mem_cons_self) regs h0 h3
        (hlenR j List.mem_cons_self) hB
    obtain ⟨regs₂, hreach₂, hl₂, h0₂, h3₂, hB₂⟩ :=
      reachesOut_tablesCode ha hnB hNB js _ regs₁ hP.2
        (fun j' hj' => hTB j' (List.mem_cons_of_mem _ hj')) h0₁ h3₁
        (fun j' hj' => hl₁ ▸ hlenR j' (List.mem_cons_of_mem _ hj')) hB₁
    refine ⟨regs₂, ?_, hl₂.trans hl₁, h0₂, h3₂, hB₂⟩
    rw [List.map_cons, List.sum_cons, ← Nat.add_assoc, List.flatMap_cons]
    exact hreach₁.trans hreach₂

variable (v v' I)

/-- The size guard is immediately after shape checking. -/
private def sizeLabel : ℕ := 4 + 6 * v.count

private def tablesLabel : ℕ := sizeLabel v + 8

private def haltLabel : ℕ := tablesLabel v +
  ((List.finRange v'.count).map (tableLength v' I)).sum

private def registerCount : ℕ := base v' k +
  Finset.univ.sup fun j => boundDepth (I.rel (v'.symbol j).2)

/-- Check both guards before streaming any output, then emit the exact full-tuple structure. -/
private def program : CounterProgram where
  code := shapeCode v 0 (sizeLabel v) (haltLabel v v' I + 1) ++
    [.lt (reg 0) (const 2) (haltLabel v v' I + 1) (sizeLabel v + 1)] ++
    headerCode k (sizeLabel v + 1) ++
    tablesCode v v' I (tablesLabel v) (List.finRange v'.count) ++
    [.halt List.nil] ++ rejectCode v' (haltLabel v v' I + 1)
  registers := registerCount v' I

/-- All counters, including each loop's terminal value, fit this fixed polynomial. -/
private def exponent : ℕ := regExponent v + k * (maxArity v' + 1) + 1

end Transducer


variable {L L' : Language} [L.IsRelational] [L'.IsRelational] {k : ℕ}
  (I : FullTupleInterpretation L L' k) (v : Vocabulary L) (v' : Vocabulary L')

open Transducer in
/-- The actual canonical full-tuple encoded map is computed by a native logspace transducer.
The dimension, formulas and vocabularies are fixed. Space is logarithmic in full encoded input
length; the unary target size and relation tables are streamed through the write-only output. -/
theorem computableInLogSpace_encodedMap :
    MultiTapeTM.ComputableInLogSpace (I.encodedMap v v') encStructure encStructure := by
  classical
  let P := program v v' I
  refine P.computableInLogSpace_of_reachesOut (exponent (k := k) v v') fun a => ?_
  let B := ((encStructure a).length + 1) ^ exponent (k := k) v v'
  have hpow (d : ℕ) (hd : d ≤ exponent (k := k) v v') : a.1 ^ d ≤ B :=
    (Nat.pow_le_pow_left ((card_le_length_encStructure a).trans (Nat.le_succ _)) d).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) hd)
  have hE : regExponent v ≤ exponent (k := k) v v' := by unfold exponent; lia
  have hwB : (encStructure a).length ≤ B :=
    (length_le_pow_regExponent v a).trans (Nat.pow_le_pow_right (Nat.succ_pos _) hE)
  have hnB : a.1 ≤ B := (card_le_length_encStructure a).trans hwB
  have hkE : k ≤ exponent (k := k) v v' := by
    have := Nat.mul_le_mul_left k (show 1 ≤ maxArity v' + 1 by lia)
    simp only [Nat.mul_one] at this
    unfold exponent
    lia
  have hNB : a.1 ^ k ≤ B := hpow k hkE
  have hcode : P.CodeAt 0 P.code := codeAt_of_code_eq (pre := []) (post := []) (by simp)
  change P.CodeAt 0 (_ ++ _ ++ _ ++ _ ++ _ ++ _) at hcode
  rw [codeAt_append, codeAt_append, codeAt_append, codeAt_append, codeAt_append] at hcode
  obtain ⟨⟨⟨⟨⟨hshape, hsize⟩, hheader⟩, htables⟩, hhalt⟩, hreject⟩ := hcode
  simp only [List.length_append, length_shapeCode, length_headerCode, length_tablesCode,
    List.length_cons, List.length_nil, Nat.zero_add] at hsize hheader htables hhalt hreject
  change P.CodeAt (sizeLabel v) [_] at hsize
  change P.CodeAt (sizeLabel v + 1) (headerCode k _) at hheader
  change P.CodeAt (tablesLabel v) _ at htables
  change P.CodeAt (haltLabel v v' I) [.halt List.nil] at hhalt
  change P.CodeAt (haltLabel v v' I + 1) _ at hreject
  have hsize' := (codeAt_cons.mp hsize).1
  have hhalt' := (codeAt_cons.mp hhalt).1
  have hlenR (j : Fin v'.count) : base v' k + boundDepth (I.rel (v'.symbol j).2) ≤ P.registers :=
    Nat.add_le_add_left (Finset.le_sup (f := fun j => boundDepth (I.rel (v'.symbol j).2))
      (Finset.mem_univ j)) _
  have hbase := le_base (k := k) v'
  have hlen₀ : 8 ≤ P.registers := hbase.trans (Nat.le_add_right _ _)
  obtain ⟨rs, hshapeRun, hlen, h0, hB⟩ := reaches_shapeCode (B := B) (a := a) hshape
    (fun i => (pow_arityAt_le v a i).trans (Nat.pow_le_pow_right (Nat.succ_pos _) hE))
    hwB (List.replicate P.registers 0) (by simp)
    (by simp only [List.length_replicate]; lia) (by simp)
  by_cases ha : v.WellFormed a
  · rw [ite_eq_left ha] at hshapeRun
    by_cases hn : 2 ≤ a.1
    · let _ : Fact (2 ≤ a.1) := ⟨hn⟩
      have hcheck : P.Reaches (encStructure a) (P.Running B)
          (sizeLabel v, rs) (sizeLabel v + 1, rs) := by
        refine Reaches.lt hsize' hB ?_
        simp only [eval_reg, eval_const, h0 ha, Nat.not_lt.mpr hn, ↓reduceIte]
        exact Reaches.refl _
      obtain ⟨rs₁, hheaderRun, hlen₁, h0₁, h3₁, hB₁⟩ := reachesOut_headerCode hheader hNB rs
        (h0 ha) (by rw [hlen, List.length_replicate]; exact hlen₀) hB
      change P.ReachesOut _ _ _ (tablesLabel v, rs₁) _ at hheaderRun
      have hTB (j : Fin v'.count) : (a.1 ^ k) ^ (v'.symbol j).1 ≤ B := by
        rw [← pow_mul]
        apply hpow
        have hm := Nat.mul_le_mul_left k ((arity_le_maxArity v' j).trans (Nat.le_succ _))
        unfold exponent
        lia
      obtain ⟨rs₂, htablesRun, _, _, _, hB₂⟩ := reachesOut_tablesCode ha hnB hNB
        (List.finRange v'.count) _ rs₁ htables (fun j _ => hTB j) h0₁ h3₁
        (fun j _ => by rw [hlen₁, hlen, List.length_replicate]; exact hlenR j) hB₁
      refine ⟨(haltLabel v v' I, rs₂), _, [], hshapeRun.reachesOut.trans
        (hcheck.reachesOut.trans (hheaderRun.trans htablesRun)), hhalt', ?_, hB₂⟩
      rw [I.encodedMap_of_admissible v v' ha hn]
      simp only [List.nil_append, List.append_nil, encStructure_eq, Vocabulary.encode]
      congr 1
      rw [List.ofFn_eq_map, List.flatMap_map]
    · obtain ⟨hrun, hhalt⟩ := reachesOut_rejectCode (w := encStructure a) hreject rs hB
      refine ⟨(_, rs), List.replicate (v'.count + 2) false, [],
        hshapeRun.reachesOut.trans (ReachesOut.lt hsize' hB ?_), hhalt, ?_, hB⟩
      · simpa only [eval_reg, eval_const, h0 ha, Nat.lt_of_not_ge hn, ↓reduceIte,
          List.replicate_succ] using hrun
      · rw [I.encodedMap_of_not_admissible v v' (fun h => hn h.2)]
        simpa only [List.nil_append, List.append_nil] using encStructure_reject (v' := v')
  · rw [ite_eq_right ha] at hshapeRun
    obtain ⟨hrun, hhalt⟩ := reachesOut_rejectCode (w := encStructure a) hreject rs hB
    refine ⟨(_, rs), _, [], hshapeRun.reachesOut.trans hrun, hhalt, ?_, hB⟩
    rw [I.encodedMap_of_not_admissible v v' (fun h => ha h.1)]
    simpa only [List.nil_append, List.append_nil] using encStructure_reject (v' := v')

/-- For positive tuple dimension, the encoded map belongs to the target ordered query language if
and only if the source belongs to the pulled-back ordered query language. -/
theorem mem_queryLanguage_encodedMap_iff (hk : 0 < k) (φ : (language L').Sentence)
    {a : EncodedStructure} :
    I.encodedMap v v' a ∈ queryLanguage v' φ ↔ a ∈ queryLanguage v (I.onSentence φ) := by
  by_cases h : v.WellFormed a ∧ 2 ≤ a.1
  · obtain ⟨ha, hn⟩ := h
    let : Fact (2 ≤ a.1) := ⟨hn⟩
    let : Fact (2 ≤ (I.encodedMap v v' a).1) := ⟨I.two_le_card_encodedMap v v' hk ha hn⟩
    rw [mem_queryLanguage, mem_queryLanguage, I.wellFormed_encodedMap_iff]
    refine ⟨fun ⟨_, hφ⟩ => ⟨ha, ?_⟩, fun ⟨_, hφ⟩ => ⟨⟨ha, hn⟩, ?_⟩⟩
    · let _ := v.decode a
      let _ := I.modelStructure hk (n := a.1)
      let _ := I.inputStructure (n := a.1)
      let _ : Fact (2 ≤ a.1 ^ k) := ⟨two_le_pow (n := a.1) hk⟩
      let _ := v'.decode (I.encodedMap v v' a)
      rw [I.realize_onSentence hk φ, ← StrongHomClass.realize_sentence (I.modelEquiv hk) φ,
        StrongHomClass.realize_sentence (I.encodedModelEquiv v v' hk ha) φ]
      exact hφ
    · let _ := v.decode a
      let _ := I.modelStructure hk (n := a.1)
      let _ := I.inputStructure (n := a.1)
      let _ : Fact (2 ≤ a.1 ^ k) := ⟨two_le_pow (n := a.1) hk⟩
      let _ := v'.decode (I.encodedMap v v' a)
      rw [← StrongHomClass.realize_sentence (I.encodedModelEquiv v v' hk ha) φ,
        StrongHomClass.realize_sentence (I.modelEquiv hk) φ, ← I.realize_onSentence hk φ]
      exact hφ
  · refine iff_of_false ?_ ?_
    · intro hm
      exact h ((I.wellFormed_encodedMap_iff v v').mp hm.1)
    · rintro ⟨ha, hn, _⟩
      exact h ⟨ha, hn⟩

/-- For positive tuple dimension, the canonical full-tuple encoded map is a logspace many-one
reduction from the pulled-back ordered query language to the target ordered query language. -/
theorem logSpaceReducible_onSentence (hk : 0 < k) (φ : (language L').Sentence) :
    Complexity.LogSpaceReducible encStructure encStructure
      (queryLanguage v (I.onSentence φ)) (queryLanguage v' φ) :=
  ⟨I.encodedMap v v', I.computableInLogSpace_encodedMap v v',
    fun _ => (I.mem_queryLanguage_encodedMap_iff v v' hk φ).symm⟩

end Cslib.Logic.FO.Ordered.FullTupleInterpretation
