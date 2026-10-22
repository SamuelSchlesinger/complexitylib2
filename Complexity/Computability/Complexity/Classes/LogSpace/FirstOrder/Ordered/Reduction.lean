/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered
public import Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder.Transducer
public import Complexity.Logics.FirstOrder.Ordered.DomainInterpretation.Encoding
public import Complexity.Logics.FirstOrder.Ordered.FullTuple.DomainInterpretation
import Complexity.Computability.Complexity.Reduction.ManyOne

/-!
# Ordered interpretations in logarithmic space

The encoded map of a fixed ordered interpretation with a domain formula is computed by the
domain-counting transducer of `Cslib.Logic.FO.Interpretation.computableInLogSpace_encodedMapWith`,
instantiated with the ordered formula compiler: canonical numeric atoms (order, `BIT`, `0`, `1`,
`max`) are computed from cardinality and indices, and no numeric tables are supplied. The
coordinates are enumerated by `Fin.revPerm`, so that tuple indices are lexicographic ranks. The
transducer checks the source shape and size before emitting output, then writes the unary count of
the domain tuples and each target relation table over their ranks.

A full-tuple interpretation is the instance with domain `⊤`, through
`FullTupleInterpretation.encodedMap_toDomainInterpretation`; it has no separate program.

## Main definitions

* `Cslib.Logic.FO.Ordered.ModelChecker.formulaCompiler`: the ordered formula compiler.

## Main results

* `Cslib.Logic.FO.Ordered.DomainInterpretation.encodedMap_eq_encodedMapWith`: the encoded image is
  the output of the domain-counting transducer.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.computableInLogSpace_encodedMap`: ordered
  interpretations with a domain formula are computed in logarithmic space.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.logSpaceReducible`: admissible interpretations
  reducing one ordered query to another induce logspace reductions of their encodings.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.computableInLogSpace_encodedMap`: the full-domain
  instance.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.logSpaceReducible_onSentence`: the exact map
  reduces the pulled-back ordered query to the target query.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Theorem 3.1 and Propositions 3.5/3.10.
  Capture remains open.
* The order-free interpretation writer, shared counter-program simulation and Christian
  Reitwiessner's native arithmetic are reused with their source authorship retained.
-/

@[expose] public section

open FirstOrder Language Structure Turing

namespace Cslib.Logic.FO.Ordered

open Vocabulary.ModelChecker
open FO.Interpretation (modelCard rankEquiv rankEquiv_apply_val domainRank_mono)

/-- Encodings agree when the numberings have equal sizes and the size cast preserves every
relation. -/
private theorem encode_congr {L : Language} (v : Vocabulary L) {M N : Type} [L.Structure M]
    [L.Structure N] {m n : ℕ} (e₁ : M ≃ Fin m) (e₂ : N ≃ Fin n) (h : m = n)
    (hrel : ∀ {r} (R : L.Relations r) (x : Fin r → Fin m),
      RelMap R (e₁.symm ∘ x) ↔ RelMap R (e₂.symm ∘ Fin.cast h ∘ x)) :
    v.encode M e₁ = v.encode N e₂ := by
  subst h
  simp only [Vocabulary.encode, Vocabulary.relTable]
  congr 2
  funext i
  congr 1
  funext j
  exact decide_eq_decide.mpr (hrel _ _)

namespace ModelChecker

variable {L : Language} [L.IsRelational] (v : Vocabulary L)

/-- The ordered formula compiler: canonical numeric atoms are computed natively, input atoms read
from the input tables, and inputs of size below two are inadmissible. -/
def formulaCompiler : FormulaCompiler v (language L) where
  minCard := 2
  expand hn s :=
    letI := s
    letI : Fact (2 ≤ _) := ⟨hn⟩
    inferInstance
  atomic := atomicCompiler v
  correct {a} ha hn _ fv base val :=
    letI : Fact (2 ≤ a.1) := ⟨hn⟩
    atomicCompiler_correct ha fv base val

end ModelChecker

namespace DomainInterpretation

variable {L L' : Language} [L.IsRelational] [L'.IsRelational] {k : ℕ}
  (I : DomainInterpretation L L' k) (v : Vocabulary L) (v' : Vocabulary L')

/-- The same formulas, as a first-order interpretation from the canonically ordered source
language. -/
def toFOInterpretation : Interpretation (language L) L' (Fin k) where
  domain := I.domain
  rel := I.rel

/-- The encoded image is the output of the domain-counting transducer with the ordered formula
compiler, numbering coordinates in reverse so that tuple indices are lexicographic ranks. -/
theorem encodedMap_eq_encodedMapWith :
    I.encodedMap v v' =
      I.toFOInterpretation.encodedMapWith (ModelChecker.formulaCompiler v) v' Fin.revPerm := by
  funext a
  by_cases h : v.WellFormed a ∧ 2 ≤ a.1
  · obtain ⟨ha, hn⟩ := h
    rw [I.encodedMap_of_admissible v v' ha hn,
      I.toFOInterpretation.encodedMapWith_of_admissible _ v' _ ha hn]
    let M := decoded v a hn
    let J := I.toFOInterpretation
    let _ := (ModelChecker.formulaCompiler v).expand hn (v.decode a)
    let g : Fin (modelCard J Fin.revPerm a.1) → Fin k → Fin M.size :=
      fun i => ((rankEquiv J Fin.revPerm a.1).symm i).1
    have hrank (i) : J.domainRank Fin.revPerm a.1 (lexRank (g i)) = i := by
      have hi := congrArg Fin.val ((rankEquiv J Fin.revPerm a.1).apply_symm_apply i)
      rw [rankEquiv_apply_val] at hi
      exact hi
    obtain ⟨hc, hu⟩ := I.unrank_eq_of_strictMono (M := M) g
      (fun i => ((rankEquiv J Fin.revPerm a.1).symm i).2)
      (fun x hx => ⟨rankEquiv J Fin.revPerm a.1 (Interpretation.Model.mk x hx), by
        simp only [g, Equiv.symm_apply_apply]
        rfl⟩)
      (fun i j hij => by
        change lexRank (g i) < lexRank (g j)
        by_contra hle
        have hmono := domainRank_mono (I := J) (e := Fin.revPerm) (n := a.1) (not_lt.mp hle)
        rw [hrank, hrank] at hmono
        have := Fin.lt_def.mp hij
        omega)
    let _ := I.inputStructure M
    refine encode_congr v' _ _ hc fun R x => ?_
    change (I.rel R).Realize (fun p => I.unrank M (x p.1) p.2) ↔
      (I.rel R).Realize (fun p => g (Fin.cast hc (x p.1)) p.2)
    simp only [hu]
  · rw [I.encodedMap_of_not_admissible v v' h,
      I.toFOInterpretation.encodedMapWith_of_not_admissible _ v' _ h]

/-- **Ordered interpretations with a domain formula are computed in logarithmic space.** For a
fixed interpretation and fixed vocabularies, the encoded image, numbered by lexicographic rank of
the domain tuples, is computed by a native transducer whose work space is logarithmic in the full
encoded input length. The domain may have fewer than two tuples. -/
theorem computableInLogSpace_encodedMap :
    MultiTapeTM.ComputableInLogSpace (I.encodedMap v v') encStructure encStructure := by
  rw [encodedMap_eq_encodedMapWith]
  exact I.toFOInterpretation.computableInLogSpace_encodedMapWith _ v' _

/-- **Ordered interpretations are logspace reductions.** An admissible ordered interpretation with
a domain formula whose image map reduces the query `K` to `K'` induces a logspace many-one
reduction between their encoded query languages. -/
theorem logSpaceReducible (hI : I.Admissible) {K : Query L} {K' : Query L'}
    (hK : ∀ M, M ∈ K ↔ I.map hI M ∈ K') :
    Complexity.LogSpaceReducible encStructure encStructure (K.encodedLanguage v)
      (K'.encodedLanguage v') := by
  have hmap : Complexity.ManyOneReducibleBy (fun f => f = I.map hI) K K' := ⟨I.map hI, rfl, hK⟩
  have h := hmap.lift
    (Good' := fun F => MultiTapeTM.ComputableInLogSpace F encStructure encStructure)
    (decode? v) (decode? v')
    (fun f (hf : f = I.map hI) => ⟨I.encodedMap v v', I.computableInLogSpace_encodedMap v v',
      fun a => hf ▸ I.decode?_encodedMap v v' hI a⟩)
  rw [Query.encodedLanguage_eq, Query.encodedLanguage_eq]
  obtain ⟨F, hF, hiff⟩ := h
  exact ⟨F, hF, hiff⟩

end DomainInterpretation

end Cslib.Logic.FO.Ordered

namespace Cslib.Logic.FO.Ordered.FullTupleInterpretation



variable {L L' : Language} [L.IsRelational] [L'.IsRelational] {k : ℕ}
  (I : FullTupleInterpretation L L' k) (v : Vocabulary L) (v' : Vocabulary L')

/-- The actual canonical full-tuple encoded map is computed by a native logspace transducer.
The dimension, formulas and vocabularies are fixed. Space is logarithmic in full encoded input
length; the unary target size and relation tables are streamed through the write-only output.
It is the domain-counting transducer for the full domain. -/
theorem computableInLogSpace_encodedMap :
    MultiTapeTM.ComputableInLogSpace (I.encodedMap v v') encStructure encStructure := by
  rw [← I.encodedMap_toDomainInterpretation v v']
  exact I.toDomainInterpretation.computableInLogSpace_encodedMap v v'

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
