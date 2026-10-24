/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.MCSP.NP
public import Complexity.Computability.MCSP.Partial
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Circuit.Boolean.Hierarchy
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Foundations.Data.BitString.Binary
import Mathlib.Data.List.GetD

/-!
# Partial MCSP (`MCSP*`) is in NP

We define standard string encodings for instances of the Partial Minimum Circuit Size Problem
(`Cslib.PartialMCSP.Instance`) and prove that `PartialMCSP` belongs to `NP` under both encodings:
* `Cslib.PartialMCSP.enc`: encodes the $2^n$-entry truth table over `Option Bool` using
  `encList (encOption encBool)` followed by the threshold in unary (`encUnary`), matching
  [Hirahara2022, Definition 8.4] and Issue #798 comment 3.
* `Cslib.PartialMCSP.encBinary`: encodes the $2^n$-entry truth table over `Option Bool` using
  `encList (encOption encBool)` followed by the threshold in binary (`encNat`), matching
  `Cslib.MCSP.encInstance` and [Ilango2020FOCS, Section 2.2].

A certificate for `PartialMCSP` is a circuit with at most `MCSP.budget n s` gates, in the format
of `Cslib.Circuits.Boolean.readCertificate`, since any partial truth table on `n` variables can be
extended to a total Boolean function `x.completion` of complexity at most $2^n (2 n + 3) + 1$
(`complexity_le_two_pow_mul_add_one`). The verifier evaluates the decoded circuit on every input
$y \in \{0, 1\}^n$ and checks that whenever the partial truth table specifies `some b` at `y`, the
circuit outputs `b`.

We also prove that the embedding `PartialMCSP.Instance.ofTotal : MCSP.Instance →
PartialMCSP.Instance` is computable in polynomial time (`computableInPolyTime_ofTotal_encBinary`),
giving a polynomial-time many-one reduction from `MCSP` to `PartialMCSP`
(`polyTimeReducible_MCSP_PartialMCSP_encBinary`).

## Main definitions

* `Cslib.PartialMCSP.enc`: encoding of `PartialMCSP.Instance` with unary threshold.
* `Cslib.PartialMCSP.encBinary`: encoding of `PartialMCSP.Instance` with binary threshold.
* `Cslib.PartialMCSP.tableEntry`: lookup of an input bitstring in a partial truth-table list.
* `Cslib.PartialMCSP.verifier`, `Cslib.PartialMCSP.tableVerifier`: the NP verifiers.

## Main results

* `Cslib.PartialMCSP.mem_of_verifier_eq_true`, `Cslib.PartialMCSP.exists_verifier_append`:
  soundness and padded completeness of `PartialMCSP.verifier`.
* `Cslib.PartialMCSP.isVerifier`, `Cslib.PartialMCSP.isVerifier_encBinary`: verifier correctness.
* `Cslib.PartialMCSP.computableInPolyTime_verifier`,
  `Cslib.PartialMCSP.computableInPolyTime_verifier_encBinary`: plain polynomial-time certificates
  for the verifiers.
* `Cslib.PartialMCSP.mem_NP`, `Cslib.PartialMCSP.mem_NP_encBinary`: `PartialMCSP ∈ NP`.
* `Cslib.PartialMCSP.computableInPolyTime_ofTotal_encBinary`,
  `Cslib.PartialMCSP.polyTimeReducible_MCSP_PartialMCSP_encBinary`: polynomial-time reduction from
  `MCSP` to `PartialMCSP`.

## References

* [R. Ilango, *Constant Depth Formula and Partial Function Versions of MCSP are
  Hard*][Ilango2020FOCS]
* [S. Hirahara, *NP-Hardness of Learning Programs and Partial MCSP*][Hirahara2022]
-/

@[expose] public section

namespace Cslib.PartialMCSP

open Circuits Circuits.Boolean Turing.MultiTapeTM Complexity

/-- Instances of `PartialMCSP` encoded by the framed list of `Option Bool` truth-table entries
followed by the threshold in unary [Hirahara2022, Definition 8.4]. -/
def enc : Instance ↪ List Bool :=
  ⟨fun x => encPair (encList (encOption encBool)) encUnary (List.ofFn x.table, x.threshold), by
    rintro ⟨n, T, s⟩ ⟨n', T', s'⟩ h
    obtain ⟨hT, hs⟩ := Prod.ext_iff.1
      ((encPair (encList (encOption encBool)) encUnary).injective h)
    obtain rfl : n = n' := Nat.pow_right_injective le_rfl (by simpa using congrArg List.length hT)
    obtain rfl := List.ofFn_injective hT
    obtain rfl : s = s' := hs
    rfl⟩

theorem enc_apply (x : Instance) :
    enc x = encPair (encList (encOption encBool)) encUnary (List.ofFn x.table, x.threshold) :=
  rfl

/-- Instances of `PartialMCSP` encoded by the framed list of `Option Bool` truth-table entries
followed by the threshold in binary [Ilango2020FOCS, Section 2.2]. -/
def encBinary : Instance ↪ List Bool :=
  ⟨fun x => encPair (encList (encOption encBool)) encNat (List.ofFn x.table, x.threshold), by
    rintro ⟨n, T, s⟩ ⟨n', T', s'⟩ h
    obtain ⟨hT, hs⟩ := Prod.ext_iff.1
      ((encPair (encList (encOption encBool)) encNat).injective h)
    obtain rfl : n = n' := Nat.pow_right_injective le_rfl (by simpa using congrArg List.length hT)
    obtain rfl := List.ofFn_injective hT
    obtain rfl : s = s' := hs
    rfl⟩

theorem encBinary_apply (x : Instance) :
    encBinary x = encPair (encList (encOption encBool)) encNat (List.ofFn x.table, x.threshold) :=
  rfl

private theorem two_pow_le_length_encList_table (x : Instance) :
    2 ^ x.arity ≤ (encList (encOption encBool) (List.ofFn x.table)).length := by
  have h := SizedListEncoding.length_le (encA := encOption encBool)
    (encL := encList (encOption encBool)) (List.ofFn x.table)
  simpa using h

private theorem two_pow_le_length_enc (x : Instance) :
    2 ^ x.arity ≤ (enc x).length := by
  have h := two_pow_le_length_encList_table x
  rw [enc_apply, length_encPair]
  dsimp only
  omega

private theorem two_pow_le_length_encBinary (x : Instance) :
    2 ^ x.arity ≤ (encBinary x).length := by
  have h := two_pow_le_length_encList_table x
  rw [encBinary_apply, length_encPair]
  dsimp only
  omega

/-- The entry of a partial truth-table list at the input with bits `y` (`none` if out of bounds). -/
def tableEntry (table : List (Option Bool)) (y : List Bool) : Option Bool :=
  table.getD (BitString.boundedBinaryValue table.length y.reverse) none

/-- The verifier reads the partial function of an instance from its truth table. -/
theorem tableEntry_ofFn (x : Instance) (y : BitString x.arity) :
    tableEntry (List.ofFn x.table) (List.ofFn y) = x.partialFunction y := by
  have hlt := (BitString.equivFin x.arity y).isLt
  rw [tableEntry, BitString.boundedBinaryValue_eq, BitString.binaryValue_reverse_ofFn,
    List.length_ofFn, Nat.min_eq_right hlt.le, List.getD_eq_getElem _ _ (by simp),
    List.getElem_ofFn]
  rfl

/-- An optional truth-table entry `entry` agrees with a circuit output bit `out` iff
`entry.getD out == out` holds. -/
theorem getD_beq_self_eq_true_iff (entry : Option Bool) (out : Bool) :
    (entry.getD out == out) = true ↔ ∀ b, entry = some b → out = b := by
  cases entry with
  | none => simp
  | some b =>
    simp only [Option.getD_some, beq_iff_eq, Option.some.injEq, forall_eq']
    exact eq_comm

/-- The verifier for `PartialMCSP`: the certificate must describe a circuit on `n` inputs with at
most `MCSP.budget n s` gates (`readCertificate`) whose output agrees with the partial truth table on
all defined entries among the `2 ^ n` inputs. -/
def verifier (p : Instance × List Bool) : Bool :=
  let c := readCertificate p.1.arity (MCSP.budget p.1.arity p.1.threshold) p.2
  (codeCheck p.1.arity c.1 && decide (c.2 < p.1.arity + c.1.length)) &&
    (BitString.enumList p.1.arity).all fun y =>
      let out := evalOutput y c.1 c.2
      (tableEntry (List.ofFn p.1.table) y).getD out == out

/-! ### Correctness -/

private theorem certLength_le_enc (x : Instance) :
    certLength x.arity (MCSP.budget x.arity x.threshold) ≤
      MCSP.certPolynomial.eval (enc x).length := by
  set L := (enc x).length
  have hT := two_pow_le_length_enc x
  have hn : x.arity ≤ L := (Nat.lt_two_pow_self).le.trans hT
  have hS : MCSP.budget x.arity x.threshold ≤ L * (2 * L + 3) + 1 :=
    (Nat.min_le_right _ _).trans (Nat.add_le_add_right
      (Nat.mul_le_mul hT (by omega)) 1)
  simp only [MCSP.certPolynomial, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat, certLength]
  nlinarith

private theorem certLength_le_encBinary (x : Instance) :
    certLength x.arity (MCSP.budget x.arity x.threshold) ≤
      MCSP.certPolynomial.eval (encBinary x).length := by
  set L := (encBinary x).length
  have hT := two_pow_le_length_encBinary x
  have hn : x.arity ≤ L := (Nat.lt_two_pow_self).le.trans hT
  have hS : MCSP.budget x.arity x.threshold ≤ L * (2 * L + 3) + 1 :=
    (Nat.min_le_right _ _).trans (Nat.add_le_add_right
      (Nat.mul_le_mul hT (by omega)) 1)
  simp only [MCSP.certPolynomial, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat, certLength]
  nlinarith

/-- **Soundness of the verifier.** An instance with an accepted certificate, of any length, is in
`PartialMCSP`. -/
theorem mem_of_verifier_eq_true {x : Instance} {w : List Bool} (hw : verifier (x, w) = true) :
    x ∈ PartialMCSP := by
  set S := MCSP.budget x.arity x.threshold with hSdef
  set r := readCertificate x.arity S w
  simp only [verifier, ← hSdef, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    codeCheck_eq_true_iff, getD_beq_self_eq_true_iff] at hw
  obtain ⟨⟨hcode, hout⟩, hall⟩ := hw
  have hsome : (Circuit.ofCode x.arity 1 (r.1, [r.2]) : Option (Circuit signature _ 1)).isSome :=
    Circuit.isSome_ofCode_iff.2 ⟨hcode, rfl, by simpa using hout⟩
  set c : Circuit signature x.arity 1 := (Circuit.ofCode x.arity 1 (r.1, [r.2])).get hsome
  have hc : c.code = (r.1, [r.2]) := Circuit.code_of_ofCode_eq_some (Option.some_get _).symm
  have houtput : (c.outputs 0).toNat = r.2 := by
    have := congrArg (fun p => p.2.headD 0) hc
    simpa [Circuit.code] using this
  refine mem_iff_exists_circuit.2 ⟨c, ?_, fun y b hy => ?_⟩
  · calc c.size = r.1.length := by rw [← Circuit.length_code_fst, hc]
      _ ≤ S := length_readCertificate_le _ _ _
      _ ≤ x.threshold := Nat.min_le_left _ _
  · rw [Circuit.eval_eq_evalOutput, houtput, show c.code.1 = r.1 by rw [hc]]
    exact hall (List.ofFn y) (BitString.mem_enumList.2 List.length_ofFn) b
      ((tableEntry_ofFn x y).trans hy)

/-- **Completeness of the verifier.** Every instance in `PartialMCSP` has a certificate of length
`certLength x.arity (MCSP.budget x.arity x.threshold)` that is accepted whatever bits follow it. -/
theorem exists_verifier_append {x : Instance} (hx : x ∈ PartialMCSP) :
    ∃ u : List Bool, u.length = certLength x.arity (MCSP.budget x.arity x.threshold) ∧
      ∀ extra, verifier (x, u ++ extra) = true := by
  set S := MCSP.budget x.arity x.threshold with hSdef
  have hcomp_bound :
      complexityOn interpretation x.definedInputs (single x.completion) ≤
        2 ^ x.arity * (2 * x.arity + 3) + 1 :=
    complexityOn_le_complexity.trans (complexity_le_two_pow_mul_add_one _)
  have hS : complexityOn interpretation x.definedInputs (single x.completion) ≤ S :=
    le_min hx hcomp_bound
  obtain ⟨c, hc, hsize⟩ := complexityOn_le_iff.mp hS
  have hagree : x.AgreesWith fun y => c.eval interpretation y 0 :=
    (Instance.computesOn_definedInputs_iff.mp hc)
  have hcode : Program.IsCodeFrom signature x.arity 0 c.code.1 := by
    rw [← Program.isSome_ofCode_iff, Circuit.code, Program.ofCode_code]
    rfl
  refine ⟨certificate x.arity S c.code.1 (c.outputs 0).toNat, length_certificate_code c hsize,
    fun extra => ?_⟩
  simp only [verifier, ← hSdef, readCertificate_certificate_code_append c hsize,
    Bool.and_eq_true, codeCheck_eq_true_iff.2 hcode, decide_eq_true_eq, List.all_eq_true,
    getD_beq_self_eq_true_iff, true_and]
  refine ⟨by rw [Circuit.length_code_fst]; exact (c.outputs 0).toNat_lt, fun y hy b hb => ?_⟩
  obtain ⟨y', rfl⟩ : ∃ y' : BitString x.arity, List.ofFn y' = y :=
    ⟨fun i => y[i.val]'(by rw [BitString.mem_enumList.1 hy]; exact i.isLt),
      List.ext_getElem (by simp [BitString.mem_enumList.1 hy]) fun _ _ _ => by simp⟩
  rw [← Circuit.eval_eq_evalOutput]
  exact hagree y' b ((tableEntry_ofFn x y').symm.trans hb)

/-- `PartialMCSP.verifier` verifies `PartialMCSP` under `enc` (unary threshold). -/
theorem isVerifier : IsVerifier enc MCSP.certPolynomial verifier PartialMCSP := by
  refine IsVerifier.of_padding (fun x w _ hw => mem_of_verifier_eq_true hw) fun x hx => ?_
  obtain ⟨u, hu, hV⟩ := exists_verifier_append hx
  exact ⟨u, hu ▸ certLength_le_enc x, fun k => hV _⟩

/-- `PartialMCSP.verifier` verifies `PartialMCSP` under `encBinary` (binary threshold). -/
theorem isVerifier_encBinary : IsVerifier encBinary MCSP.certPolynomial verifier PartialMCSP := by
  refine IsVerifier.of_padding (fun x w _ hw => mem_of_verifier_eq_true hw) fun x hx => ?_
  obtain ⟨u, hu, hV⟩ := exists_verifier_append hx
  exact ⟨u, hu ▸ certLength_le_encBinary x, fun k => hV _⟩

/-! ### Polynomial time -/

open ComputableTidilyInPolyTime

/-- The verifier on a raw partial truth-table list, a threshold, and a certificate, with the number
of inputs read from the length of the table. -/
def tableVerifier (r : (List (Option Bool) × ℕ) × List Bool) : Bool :=
  let n := Nat.log 2 r.1.1.length
  let c := readCertificate n (min r.1.2 (r.1.1.length * (2 * n + 3) + 1)) r.2
  (codeCheck n c.1 && decide (c.2 < n + c.1.length)) &&
    (BitString.enumList n).all fun y =>
      let out := evalOutput y c.1 c.2
      (tableEntry r.1.1 y).getD out == out

theorem verifier_eq_tableVerifier (p : Instance × List Bool) :
    verifier p = tableVerifier ((List.ofFn p.1.table, p.1.threshold), p.2) := by
  simp only [tableVerifier, List.length_ofFn, Nat.log_pow Nat.one_lt_two]
  rfl

private theorem computableTidilyInPolyTime_tableVerifier :
    ComputableTidilyInPolyTime tableVerifier
      (encPair (encPair (encList (encOption encBool)) encNat) encBits) encBool := by
  let encT := encList (encOption encBool)
  let encIn := encPair (encPair encT encNat) encBits
  have hlen : ComputableTidilyInPolyTime
      (fun r : (List (Option Bool) × ℕ) × List Bool => r.1.1.length) encIn encUnary :=
    (length_list (encOption encBool)).comp (fst _ _).fst'
  have hn : ComputableTidilyInPolyTime
      (fun r : (List (Option Bool) × ℕ) × List Bool => Nat.log 2 r.1.1.length) encIn encUnary :=
    unary_log_two.comp hlen
  have hB : ComputableTidilyInPolyTime
      (fun r : (List (Option Bool) × ℕ) × List Bool =>
        r.1.1.length * (2 * Nat.log 2 r.1.1.length + 3) + 1)
      encIn encUnary := by
    fun_prop
  have hB' := unary_to_binary.comp hB
  simp only [Function.comp_def] at hB'
  have hS : ComputableTidilyInPolyTime
      (fun r : (List (Option Bool) × ℕ) × List Bool =>
        min r.1.2 (r.1.1.length * (2 * Nat.log 2 r.1.1.length + 3) + 1))
      encIn encUnary := by
    refine binary_to_unary_bounded ?_ hB fun _ => Nat.min_le_right _ _
    simpa only [Nat.min_def] using ite_decide (binary_le' (by fun_prop) hB') (by fun_prop) hB'
  have hc := (computableInPolyTime_readCertificate (.of_tidy hn) (.of_tidy hS)
    (.of_tidy (snd _ _))).tidy
  have henum : ComputableTidilyInPolyTime
      (fun r : (List (Option Bool) × ℕ) × List Bool =>
        BitString.enumList (Nat.log 2 r.1.1.length))
      encIn (encList encBits) := by
    refine bitsEnumList hn (size := fun L => L * (2 * L + 1)) (by fun_prop) fun r => ?_
    set T := r.1.1.length
    have hpow : 2 ^ Nat.log 2 T ≤ T + 1 := by
      rcases Nat.eq_zero_or_pos T with h | h
      · simp [h]
      · exact (Nat.pow_log_le_self 2 h.ne').trans (Nat.le_succ T)
    have hlog : 2 * Nat.log 2 T + 1 ≤ 2 * T + 1 := by
      have := Nat.log_le_self 2 T
      omega
    have h1 := SizedListEncoding.length_le (encA := encOption encBool) (encL := encT) r.1.1
    have hT_enc : 2 * T + 1 ≤ (encIn r).length := by
      simp only [encIn, length_encPair]
      omega
    calc 2 ^ Nat.log 2 T * (2 * Nat.log 2 T + 1) ≤ (T + 1) * (2 * T + 1) :=
          Nat.mul_le_mul hpow hlog
      _ ≤ (encIn r).length * (2 * (encIn r).length + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
  have htest : ComputableTidilyInPolyTime
      (fun p : ((List (Option Bool) × ℕ) × List Bool) × List Bool =>
        let out := evalOutput p.2
          (readCertificate (Nat.log 2 p.1.1.1.length)
            (min p.1.1.2 (p.1.1.1.length * (2 * Nat.log 2 p.1.1.1.length + 3) + 1)) p.1.2).1
          (readCertificate (Nat.log 2 p.1.1.1.length)
            (min p.1.1.2 (p.1.1.1.length * (2 * Nat.log 2 p.1.1.1.length + 3) + 1)) p.1.2).2
        (tableEntry p.1.1.1 p.2).getD out == out)
      (encPair encIn encBits) encBool := by
    have htable : ComputableTidilyInPolyTime
        (fun p : ((List (Option Bool) × ℕ) × List Bool) × List Bool => p.1.1.1)
        (encPair encIn encBits) encT :=
      (fst _ _).fst'.fst'
    have hentry : ComputableTidilyInPolyTime
        (fun p : ((List (Option Bool) × ℕ) × List Bool) × List Bool => tableEntry p.1.1.1 p.2)
        (encPair encIn encBits) (encOption encBool) := by
      unfold tableEntry
      exact (listGetD (encA := encOption encBool) (encL := encT) none).comp
        (htable.prod (bitsBoundedBinaryValueWithInput
          ((length_list (encOption encBool)).comp htable)
          (bitsReverse.comp (snd _ _))))
    have hout : ComputableTidilyInPolyTime
        (fun p : ((List (Option Bool) × ℕ) × List Bool) × List Bool =>
          evalOutput p.2
            (readCertificate (Nat.log 2 p.1.1.1.length)
              (min p.1.1.2 (p.1.1.1.length * (2 * Nat.log 2 p.1.1.1.length + 3) + 1)) p.1.2).1
            (readCertificate (Nat.log 2 p.1.1.1.length)
              (min p.1.1.2 (p.1.1.1.length * (2 * Nat.log 2 p.1.1.1.length + 3) + 1)) p.1.2).2)
        (encPair encIn encBits) encBool :=
      (computableInPolyTime_evalOutput (.of_tidy (snd _ _))
        (.of_tidy (hc.comp (fst _ _)).fst')
        (.of_tidy (hc.comp (fst _ _)).snd')).tidy
    exact beq (optionGetDWithInput hentry hout) hout
  unfold tableVerifier
  exact bool_and'
    (bool_and' (computableInPolyTime_codeCheck (.of_tidy hn) (.of_tidy hc.fst')).tidy
      (binary_lt' hc.snd' (unary_to_binary.comp (unary_add.comp
        (hn.prod ((length_list encGate).comp hc.fst'))))))
    (allWithInput henum htest)

/-- The verifier on raw data is computable in polynomial time. -/
theorem computableInPolyTime_tableVerifier :
    ComputableInPolyTime tableVerifier
      (encPair (encPair (encList (encOption encBool)) encNat) encBits) encBool :=
  .of_tidy computableTidilyInPolyTime_tableVerifier

private theorem computableTidilyInPolyTime_verifier_encBinary :
    ComputableTidilyInPolyTime verifier (encPair encBinary encBits) encBool := by
  have hraw : ComputableTidilyInPolyTime
      (fun p : Instance × List Bool => ((List.ofFn p.1.table, p.1.threshold), p.2))
      (encPair encBinary encBits)
      (encPair (encPair (encList (encOption encBool)) encNat) encBits) :=
    .of_eq fun _ => rfl
  rw [funext verifier_eq_tableVerifier]
  exact computableTidilyInPolyTime_tableVerifier.comp hraw

/-- The `PartialMCSP` verifier is computable in polynomial time under `encBinary`. -/
theorem computableInPolyTime_verifier_encBinary :
    ComputableInPolyTime verifier (encPair encBinary encBits) encBool :=
  .of_tidy computableTidilyInPolyTime_verifier_encBinary

private theorem computableTidilyInPolyTime_verifier :
    ComputableTidilyInPolyTime verifier (encPair enc encBits) encBool := by
  have hraw : ComputableTidilyInPolyTime
      (fun p : Instance × List Bool => ((List.ofFn p.1.table, p.1.threshold), p.2))
      (encPair enc encBits)
      (encPair (encPair (encList (encOption encBool)) encUnary) encBits) :=
    .of_eq fun _ => rfl
  have hconv : ComputableTidilyInPolyTime
      (fun r : (List (Option Bool) × ℕ) × List Bool => ((r.1.1, r.1.2), r.2))
      (encPair (encPair (encList (encOption encBool)) encUnary) encBits)
      (encPair (encPair (encList (encOption encBool)) encNat) encBits) :=
    ((fst _ _).fst'.prod (unary_to_binary.comp (fst _ _).snd')).prod (snd _ _)
  rw [funext verifier_eq_tableVerifier]
  exact (computableTidilyInPolyTime_tableVerifier.comp hconv).comp hraw

/-- The `PartialMCSP` verifier is computable in polynomial time under `enc` (unary threshold). -/
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair enc encBits) encBool :=
  .of_tidy computableTidilyInPolyTime_verifier

/-- **`PartialMCSP` is in `NP`** under `PartialMCSP.enc` (framed `Option Bool` truth table and
unary threshold) [Hirahara2022, Definition 8.4]. -/
theorem mem_NP : PartialMCSP ∈ NP enc :=
  ⟨MCSP.certPolynomial, verifier, computableInPolyTime_verifier, isVerifier⟩

/-- **`PartialMCSP` is in `NP`** under `PartialMCSP.encBinary` (framed `Option Bool` truth table
and binary threshold) [Ilango2020FOCS, Section 2.2]. -/
theorem mem_NP_encBinary : PartialMCSP ∈ NP encBinary :=
  ⟨MCSP.certPolynomial, verifier, computableInPolyTime_verifier_encBinary, isVerifier_encBinary⟩

/-! ### Polynomial-time reduction from `MCSP` to `PartialMCSP` -/

private theorem foldl_cons_some (l : List Bool) (acc : List (Option Bool)) :
    l.foldl (fun acc b => some b :: acc) acc = l.reverse.map some ++ acc := by
  induction l generalizing acc with
  | nil => simp
  | cons b l ih =>
    simp [ih, List.map_append]

private theorem computableTidilyInPolyTime_bitsMapSome :
    ComputableTidilyInPolyTime (List.map some) encBits (encList (encOption encBool)) := by
  have hfold := foldl_of_bounded_growth (encA := encBool) (encL := encBits)
    (encB := encList (encOption encBool))
    (step := fun acc b => some b :: acc) (init := fun _ => [])
    bitsReverse (const [])
    (show ComputableTidilyInPolyTime
      (fun p : List (Option Bool) × Bool => some p.2 :: p.1)
      (encPair (encList (encOption encBool)) encBool) (encList (encOption encBool)) by fun_prop)
    (growth := 5) (fun acc b => by
      rw [encList_cons, List.length_append]
      have hb : (frame (encOption encBool (some b))).length = 5 := by cases b <;> rfl
      omega)
  refine hfold.of_enc_eq fun l => ?_
  rw [foldl_cons_some, List.reverse_reverse, List.append_nil]

/-- Embedding a total `MCSP.Instance` as a `PartialMCSP.Instance` with no `*` entries is computable
in polynomial time. -/
theorem computableInPolyTime_ofTotal_encBinary :
    ComputableInPolyTime Instance.ofTotal MCSP.encInstance encBinary := by
  have hraw : ComputableTidilyInPolyTime
      (fun x : MCSP.Instance => (List.ofFn x.table, x.threshold))
      MCSP.encInstance (encPair encBits encNat) :=
    .of_eq fun _ => rfl
  have hmap : ComputableTidilyInPolyTime
      (fun p : List Bool × ℕ => (p.1.map some, p.2))
      (encPair encBits encNat) (encPair (encList (encOption encBool)) encNat) :=
    (computableTidilyInPolyTime_bitsMapSome.comp (fst encBits encNat)).prod (snd encBits encNat)
  have hout : ComputableTidilyInPolyTime Instance.ofTotal MCSP.encInstance encBinary := by
    refine (hmap.comp hraw).of_enc_eq fun x => ?_
    have hofFn : (List.ofFn x.table).map some = List.ofFn (Instance.ofTotal x).table := by
      ext i b
      simp [Instance.ofTotal]
    simp [encBinary_apply, hofFn, Instance.ofTotal]
  exact .of_tidy hout

/-- `MCSP` reduces to `PartialMCSP` in polynomial time via `Instance.ofTotal`. -/
theorem polyTimeReducible_MCSP_PartialMCSP_encBinary :
    PolyTimeReducible MCSP.encInstance encBinary MCSP PartialMCSP :=
  ⟨Instance.ofTotal, computableInPolyTime_ofTotal_encBinary, fun x => (ofTotal_mem_iff x).symm⟩

end Cslib.PartialMCSP
