/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Encoding.Certificate
public import Complexity.Computability.Circuit.Boolean.PPoly
public import Complexity.Computability.Complexity.Classes.NP.SelfReduction
public import Complexity.Computability.Complexity.Classes.NP.Witness
public import Complexity.Computability.Complexity.Classes.PH.Collapse
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# The Karp–Lipton theorem

If `SAT` has circuits of polynomial size, the polynomial hierarchy collapses to its second level
[Karp and Lipton][KarpLipton1980], [Arora and Barak, Theorem 6.19][AroraBarak09]. The hypothesis is
that some language `L ∈ P/poly` contains exactly the encodings `encCNF φ` of the satisfiable
formulas; it follows from `NP ⊆ P/poly`, for problems with any encoding of their instances.

The proof shows `Π₂ ⊆ Σ₂` (`Cslib.Complexity.PiP_two_subset_SigmaP_two_of_SAT`). Let
`a ∈ A ↔ ∀ u, ∃ v, V (a, u ++ v)`. The pairs `(a, u)` for which some `v` is accepted form a
problem in `NP` by the witness API (`Cslib.Complexity.mem_NP_setOf_exists_append`), which the
Cook–Levin reduction `f` maps to `SAT`. A `Σ₂` verifier guesses circuits for `SAT` on all the
lengths the self-reduction (`Cslib.Complexity.SAT.search`) of a formula `f (a, u)` asks about, then
checks,
for every `u`, that the self-reduction answered by the guessed circuits finds a satisfying
assignment of `f (a, u)`. A satisfying assignment proves `(a, u)` in the problem whatever circuits
were guessed, and correct circuits always find one when there is one. Since `Π₂ ⊆ Σ₂` holds for
every encoding of instances, the hierarchy collapses to `Σ₂`
(`Cslib.Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP`).

The guessed circuits are listed in an advice string (`Cslib.Circuits.Boolean.familyAdvice`): the
circuits `C 0, …, C N`, each in the certificate format of
`Cslib.Circuits.Boolean.readCertificate`, padded to a common length. The circuit for an input `x`
is read from the block at position `x.length` and evaluated on `x`
(`Cslib.Circuits.Boolean.evalAdvice`), in polynomial time.

## Main definitions

* `Cslib.Circuits.Boolean.familyAdvice`: the advice string listing a family of circuits.
* `Cslib.Circuits.Boolean.evalAdvice`: evaluation of the circuit for the length of the input read
  from an advice string.

## Main results

* `Cslib.Circuits.Boolean.evalAdvice_familyAdvice`: evaluation from the advice string of a family
  is evaluation of its circuits.
* `Cslib.Circuits.Boolean.computableTidilyInPolyTime_evalAdvice`: evaluation from advice strings is
  polynomial-time.
* `Cslib.Complexity.PiP_two_subset_SigmaP_two_of_SAT`: if `SAT` has circuits of polynomial size,
  then `Π₂ ⊆ Σ₂`.
* `Cslib.Complexity.PiP_two_eq_SigmaP_two_of_SAT`: under the same hypothesis, `Π₂ = Σ₂`.
* `Cslib.Complexity.PH_eq_SigmaP_two_of_SAT`: **the Karp–Lipton theorem**, if `SAT` has circuits
  of polynomial size, then `PH = Σ₂`.
* `Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_PPoly`: if `NP ⊆ P/poly`, then `PH = Σ₂`.

## References

* [R. M. Karp, R. J. Lipton, *Some connections between nonuniform and uniform complexity
  classes*][KarpLipton1980]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.4][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM

/-! ### Advice strings for circuit families -/

/-- The advice string listing the circuits `C 0, …, C N`, each with at most `s` gates: block `m`
holds the certificate of `C m` (`certificate`), padded with `false` to `certLength N s` bits. -/
def familyAdvice (N s : ℕ) (C : ∀ m, Circuit signature m 1) : List Bool :=
  (List.range (N + 1)).flatMap fun m =>
    certificate m s (C m).code.1 ((C m).outputs 0).toNat ++
      List.replicate (certLength N s - certLength m s) false

/-- The value on `x` of the circuit for inputs of length `x.length`, read with at most `s` gates
from the block at position `x.length` of an advice string `w` whose blocks have `width` bits.
Every advice string gives a value. -/
def evalAdvice (s width : ℕ) (w x : List Bool) : Bool :=
  evalOutput x (readCertificate x.length s (w.drop (x.length * width))).1
    (readCertificate x.length s (w.drop (x.length * width))).2

section Family

variable {N s : ℕ} {C : ∀ m, Circuit signature m 1}

theorem length_familyAdvice_block (hs : ∀ m ≤ N, (C m).size ≤ s) {m : ℕ} (hm : m ≤ N) :
    (certificate m s (C m).code.1 ((C m).outputs 0).toNat ++
      List.replicate (certLength N s - certLength m s) false).length = certLength N s := by
  rw [List.length_append, length_certificate_code _ (hs m hm), List.length_replicate,
    Nat.add_sub_cancel' (certLength_mono_left hm s)]

/-- The advice string of circuits with at most `s` gates has `N + 1` blocks of `certLength N s`
bits. -/
theorem length_familyAdvice (hs : ∀ m ≤ N, (C m).size ≤ s) :
    (familyAdvice N s C).length = (N + 1) * certLength N s := by
  rw [familyAdvice, List.length_flatMap, List.map_congr_left fun m hm =>
    length_familyAdvice_block hs (Nat.lt_succ_iff.1 (List.mem_range.1 hm)), List.map_const',
    List.length_range, List.sum_replicate, smul_eq_mul]

/-- Block `m` of the advice string of a family starts with the certificate of `C m`. -/
theorem drop_familyAdvice (hs : ∀ m ≤ N, (C m).size ≤ s) {m : ℕ} (hm : m ≤ N) :
    ∃ rest, (familyAdvice N s C).drop (m * certLength N s) =
      certificate m s (C m).code.1 ((C m).outputs 0).toNat ++ rest := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hprefix : ((List.range m).flatMap fun j =>
      certificate j s (C j).code.1 ((C j).outputs 0).toNat ++
        List.replicate (certLength (m + k) s - certLength j s) false).length =
      m * certLength (m + k) s := by
    rw [List.length_flatMap, List.map_congr_left fun j hj =>
      length_familyAdvice_block hs (by have := List.mem_range.1 hj; omega), List.map_const',
      List.length_range, List.sum_replicate, smul_eq_mul]
  rw [familyAdvice, show m + k + 1 = m + (k + 1) by omega, List.range_add, List.flatMap_append,
    List.drop_left' hprefix, List.range_succ_eq_map, List.map_cons, List.flatMap_cons,
    Nat.add_zero, List.append_assoc]
  exact ⟨_, rfl⟩

/-- **Evaluation from the advice string of a family** is evaluation of its circuits, on inputs of
length at most `N`. -/
theorem evalAdvice_familyAdvice (hs : ∀ m ≤ N, (C m).size ≤ s) {x : List Bool}
    (hx : x.length ≤ N) :
    evalAdvice s (certLength N s) (familyAdvice N s C) x =
      (C x.length).eval interpretation (fun i => x[i]) 0 := by
  obtain ⟨rest, hrest⟩ := drop_familyAdvice hs hx
  rw [evalAdvice, hrest, readCertificate_certificate_code_append _ (hs _ hx),
    Circuit.eval_eq_evalOutput]
  simp only [Fin.getElem_fin, List.ofFn_getElem]

end Family

open ComputableTidilyInPolyTime

/-- **Evaluation from advice strings is polynomial-time**, for the number of gates and the block
width in unary. -/
@[fun_prop]
theorem computableTidilyInPolyTime_evalAdvice {γ : Type} {encIn : γ ↪ List Bool}
    {s width : γ → ℕ} {w x : γ → List Bool} (hs : ComputableTidilyInPolyTime s encIn encUnary)
    (hwidth : ComputableTidilyInPolyTime width encIn encUnary)
    (hw : ComputableTidilyInPolyTime w encIn encBits)
    (hx : ComputableTidilyInPolyTime x encIn encBits) :
    ComputableTidilyInPolyTime (fun a => evalAdvice (s a) (width a) (w a) (x a)) encIn
      encBool := by
  have hm : ComputableTidilyInPolyTime (fun a => (x a).length) encIn encUnary := length_bits.comp hx
  have hc := computableTidilyInPolyTime_readCertificate hm hs
    (bitsDropWithInput hw (unary_mul.comp (hm.prod hwidth)))
  exact computableTidilyInPolyTime_evalOutput hx hc.fst' hc.snd'

end Cslib.Circuits.Boolean

namespace Cslib.Complexity

open Cslib.Logic.PL Circuits Circuits.Boolean Turing.MultiTapeTM ComputableTidilyInPolyTime

variable {α : Type} {enc : α ↪ List Bool}

/-! ### The Karp–Lipton verifier -/

namespace KarpLipton

/-- The `Σ₂` verifier of Karp and Lipton for the reduction `f` to `SAT`. On `(a, w₁ ++ u)`, where
`w₁` has `P (enc a).length` bits, it runs the self-reduction of `f (a, u)` with the circuits read
from the advice string `w₁` (with at most `S (enc a).length` gates, in blocks of
`W (enc a).length` bits), and checks the assignment it finds. -/
def verifier (enc : α ↪ List Bool) (f : α × List Bool → CNF ℕ) (S W P : Polynomial ℕ)
    (x : α × List Bool) : Bool :=
  SAT.verifier (f (x.1, x.2.drop (P.eval (enc x.1).length)),
    SAT.search (fun ψ => evalAdvice (S.eval (enc x.1).length) (W.eval (enc x.1).length)
      (x.2.take (P.eval (enc x.1).length)) (encCNF ψ))
      (f (x.1, x.2.drop (P.eval (enc x.1).length))))

theorem verifier_append {f : α × List Bool → CNF ℕ} {S W P : Polynomial ℕ} (a : α)
    {w₁ : List Bool} (hw₁ : w₁.length = P.eval (enc a).length) (u : List Bool) :
    verifier enc f S W P (a, w₁ ++ u) = SAT.verifier (f (a, u),
      SAT.search (fun ψ => evalAdvice (S.eval (enc a).length) (W.eval (enc a).length) w₁
        (encCNF ψ)) (f (a, u))) := by
  rw [verifier, ← hw₁, List.drop_left, List.take_left]

theorem computableTidilyInPolyTime_verifier {f : α × List Bool → CNF ℕ}
    (hf : ComputableTidilyInPolyTime f (encPair enc encBits) encCNF) (S W P : Polynomial ℕ) :
    ComputableTidilyInPolyTime (verifier enc f S W P) (encPair enc encBits) encBool := by
  have hn : ComputableTidilyInPolyTime (fun x : α × List Bool => (enc x.1).length)
      (encPair enc encBits) encUnary :=
    (encoding_length enc).comp (fst _ _)
  have hφ : ComputableTidilyInPolyTime (fun x : α × List Bool =>
      f (x.1, x.2.drop (P.eval (enc x.1).length))) (encPair enc encBits) encCNF :=
    hf.comp ((fst _ _).prod (bitsDropWithInput (snd _ _) ((unary_eval P).comp hn)))
  have hD : ComputableTidilyInPolyTime (fun p : (α × List Bool) × CNF ℕ =>
      evalAdvice (S.eval (enc p.1.1).length) (W.eval (enc p.1.1).length)
        (p.1.2.take (P.eval (enc p.1.1).length)) (encCNF p.2))
      (encPair (encPair enc encBits) encCNF) encBool := by
    have hn' := hn.comp (fst (encPair enc encBits) encCNF)
    exact computableTidilyInPolyTime_evalAdvice ((unary_eval S).comp hn')
      ((unary_eval W).comp hn') (bitsTakeWithInput (fst _ _).snd' ((unary_eval P).comp hn'))
      ((encode encCNF).comp (snd _ _))
  exact SAT.computableTidilyInPolyTime_verifier.comp
    (hφ.prod (SAT.computableTidilyInPolyTime_search hD hφ))

end KarpLipton

/-! ### `Π₂ ⊆ Σ₂` -/

/-- **Karp–Lipton, `Π₂ ⊆ Σ₂`.** If some language in `P/poly` contains exactly the encodings of the
satisfiable formulas, then `Π₂ ⊆ Σ₂`, for every encoding of instances. -/
theorem PiP_two_subset_SigmaP_two_of_SAT (hSAT : ∃ L ∈ PPoly, ∀ φ, φ ∈ SAT ↔ encCNF φ ∈ L)
    (enc : α ↪ List Bool) : PiP 2 enc ⊆ SigmaP 2 enc := by
  rintro A ⟨ps, V, hlen, hV, hA⟩
  obtain ⟨p, q, rfl⟩ := List.length_eq_two.1 hlen
  obtain ⟨f, hf, hfB⟩ := CookLevin.SAT_npHard _ _ (mem_NP_setOf_exists_append hV.tidy q)
  obtain ⟨L, hL, hSAT⟩ := hSAT
  obtain ⟨C, s, hs, hC⟩ := mem_PPoly_iff_exists_circuits.1 hL
  obtain ⟨c, d, hcd⟩ := polynomiallyBounded_iff_le.1 hs
  obtain ⟨c', d', hf'⟩ := hf.polyBounded_length.exists_le
  -- a bound on the length of the formulas `f (a, u)`
  let F : Polynomial ℕ := Polynomial.C c' * (2 * Polynomial.X + 2 + p) ^ d'
  -- a bound on the length of the queries
  let N : Polynomial ℕ := F + (F + 1) * (8 * F + 11)
  -- a bound on the size of the circuits for `SAT` up to that length
  let S : Polynomial ℕ := Polynomial.C c * (N + 1) ^ d
  -- the length of a block and of the advice string
  let W : Polynomial ℕ := S + (N + S) + S * (3 + 2 * (N + S))
  let P : Polynomial ℕ := (N + 1) * W
  have hF (a : α) (u : List Bool) (hu : u.length = p.eval (enc a).length) :
      (encCNF (f (a, u))).length ≤ F.eval (enc a).length := by
    refine (hf' (a, u)).trans (le_of_eq ?_)
    simp only [length_encPair, encBits_apply, hu, F, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
    ring
  have hN (n : ℕ) : N.eval n = SAT.queryBound (F.eval n) := by
    simp [N, SAT.queryBound, Polynomial.eval_add, Polynomial.eval_mul]
  have hS (n : ℕ) : S.eval n = c * (N.eval n + 1) ^ d := by simp [S]
  have hW (n : ℕ) : W.eval n = certLength (N.eval n) (S.eval n) := by
    simp [W, certLength]
  have hP (n : ℕ) : P.eval n = (N.eval n + 1) * certLength (N.eval n) (S.eval n) := by
    simp [P, hW]
  have hsize (n : ℕ) : ∀ m ≤ N.eval n, (C m).size ≤ S.eval n := fun m hm =>
    ((hC m).1.trans (hcd m)).trans (by
      rw [hS]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) d))
  refine ⟨[P, p], KarpLipton.verifier enc f S W P, rfl,
    .of_tidy (KarpLipton.computableTidilyInPolyTime_verifier hf S W P), fun a => ?_⟩
  set n := (enc a).length
  -- membership in `A` through `SAT`
  have hA' : a ∈ A ↔ ∀ u : List Bool, u.length = p.eval n → f (a, u) ∈ SAT := by
    rw [hA a]
    simp only [List.map_cons, List.map_nil, alternation_false_cons, alternation_true_cons,
      alternation_nil, List.append_nil]
    exact forall₂_congr fun u _ => hfB (a, u)
  rw [hA']
  simp only [List.map_cons, List.map_nil, alternation_true_cons, alternation_false_cons,
    alternation_nil, List.append_nil]
  constructor
  · intro h
    refine ⟨familyAdvice (N.eval n) (S.eval n) C,
      (length_familyAdvice (hsize n)).trans (hP n).symm, fun u hu => ?_⟩
    rw [KarpLipton.verifier_append a ((length_familyAdvice (hsize n)).trans (hP n).symm), hW]
    refine SAT.verifier_search (fun ψ hψ => ?_) (h u hu)
    have hlen : (encCNF ψ).length ≤ N.eval n := by
      rw [hN]
      exact hψ.trans (SAT.queryBound_mono (hF a u hu))
    rw [evalAdvice_familyAdvice (hsize n) hlen, (hC _).2, single_apply,
      Language.slice_eq_true_iff, hSAT]
    simp only [Fin.getElem_fin, List.ofFn_getElem]
  · rintro ⟨w₁, hw₁, h⟩ u hu
    have := h u hu
    rw [KarpLipton.verifier_append a hw₁] at this
    exact ⟨_, this⟩

/-- **Karp–Lipton, `Π₂ = Σ₂`.** If some language in `P/poly` contains exactly the encodings of the
satisfiable formulas, then `Π₂ = Σ₂`, for every encoding of instances. -/
theorem PiP_two_eq_SigmaP_two_of_SAT (hSAT : ∃ L ∈ PPoly, ∀ φ, φ ∈ SAT ↔ encCNF φ ∈ L)
    (enc : α ↪ List Bool) : PiP 2 enc = SigmaP 2 enc := by
  refine (PiP_two_subset_SigmaP_two_of_SAT hSAT enc).antisymm fun A hA => ?_
  simpa using compl_mem_PiP_of_mem_SigmaP
    (PiP_two_subset_SigmaP_two_of_SAT hSAT enc (compl_mem_PiP_of_mem_SigmaP hA))

/-! ### The collapse -/

/-- **The Karp–Lipton theorem.** If some language in `P/poly` contains exactly the encodings of the
satisfiable formulas, then the polynomial hierarchy collapses to its second level: `PH = Σ₂`, for
every encoding of instances. -/
theorem PH_eq_SigmaP_two_of_SAT (hSAT : ∃ L ∈ PPoly, ∀ φ, φ ∈ SAT ↔ encCNF φ ∈ L) :
    PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_of_PiP_subset_SigmaP (by norm_num) fun encB =>
    PiP_two_subset_SigmaP_two_of_SAT hSAT encB

/-- **The Karp–Lipton theorem, `NP ⊆ P/poly ⇒ PH = Σ₂`.** If every problem in `NP`, with any
encoding of its instances, is the preimage of a language in `P/poly`, then `PH = Σ₂`, for every
encoding of instances. -/
theorem PH_eq_SigmaP_two_of_NP_subset_PPoly
    (h : ∀ {β : Type} (encB : β ↪ List Bool), ∀ B ∈ NP encB, ∃ L ∈ PPoly, ∀ b, b ∈ B ↔ encB b ∈ L) :
    PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_two_of_SAT (h encCNF SAT SAT.mem_NP)

end Cslib.Complexity
