/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Fagin.Power

/-!
# Existential second-order layout of framed structure encodings

On the canonical power structure `(Fin B, v.powerStructure a B)` for a well-formed input
`a : EncodedStructure` with `(frame (encStructure a)).length < B`, the Cook–Levin tableau needs the
input tape word `u = frame (encStructure a)` and its length `u.length` as unary predicates on
`Fin B`.

Because `encStructure a = frame (encUnary a.1) ++ (a.2.flatMap frame)` and
`u = frame (encStructure a)`, every stage of the binary encoding is an application of
`Turing.MultiTapeTM.frame` at some starting offset `base`. We therefore axiomatize a single
stride-2 framing step (`FO.frameChunkSentence`) in first-order logic using the linear order
`powerLt` on `Fin B`:
* given a domain formula `inDom(j)` (`j < w.length`), a bit formula `inBit(j)` (`w[j] = true`), and
  a unary relation `baseRel` holding of `{base}`,
* a binary relation `mapRel(j, p)` tracks `p = base + 2 * j` for `j ≤ w.length`, writing `true` at
  `base + 2 * j` and `w[j]` at `base + 2 * j + 1` into `outBitRel`, and writing the terminator
  `false` at `base + 2 * w.length` while advancing `nextBaseRel` to `{base + 2 * w.length + 1}`.

Chaining `v.count + 1` instances of `frameChunkSentence` reconstructs `encStructure a` and its
length, and one final instance reconstructs `frame (encStructure a)` and its length.

## Main definitions

* `Cslib.Logic.FO.frameChunkSentence`: the first-order sentence axiomatizing a single stride-2
  framing step on `Fin B`.
* `Cslib.Logic.Vocabulary.inputVarLanguage`: the two unary relation symbols `uBitSym` and `uLenSym`
  representing the framed input word `u = frame (encStructure a)` and its length on `Fin B`.
* `Cslib.Logic.Vocabulary.layoutESOSentence`: the existential second-order sentence over
  `v.powerLanguage.sum inputVarLanguage` characterizing `u` and `u.length`.

## Main results

* `Cslib.Logic.FO.getElem?_frame_eq_of_realize_frameChunkSentence`,
  `Cslib.Logic.FO.realize_frameChunkSentence_of_canonical`: soundness and completeness of
  `frameChunkSentence` on `Fin B`.
* `Cslib.Logic.Vocabulary.realize_layoutESOSentence`: for well-formed `a` with
  `(frame (encStructure a)).length < B`, `v.layoutESOSentence` holds on `Fin B` iff `uLenSym` holds
  solely of `(frame (encStructure a)).length` and `uBitSym` agrees with `frame (encStructure a)`
  below `(frame (encStructure a)).length`.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v

open FirstOrder Language Structure BoundedFormula Turing.MultiTapeTM

namespace Cslib.Logic

/-! ### Indexed bit access in `frame w` -/

theorem getElem?_frame_two_mul_length (w : List Bool) :
    (frame w)[2 * w.length]? = some false := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have hidx : 2 * (b :: w).length = 2 * w.length + 2 := by simp; omega
    rw [hidx, frame_cons]
    exact ih

theorem getElem?_frame_two_mul {w : List Bool} {j : ℕ} (hj : j < w.length) :
    (frame w)[2 * j]? = some true := by
  induction w generalizing j with
  | nil => simp at hj
  | cons b w ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have hj' : j < w.length := by simpa using hj
      have hidx : 2 * (j + 1) = 2 * j + 2 := by omega
      rw [hidx, frame_cons]
      exact ih hj'

theorem getElem?_frame_two_mul_add_one {w : List Bool} {j : ℕ} (hj : j < w.length) :
    (frame w)[2 * j + 1]? = w[j]? := by
  induction w generalizing j with
  | nil => simp at hj
  | cons b w ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have hj' : j < w.length := by simpa using hj
      have hidx : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by omega
      rw [hidx, frame_cons]
      exact ih hj'

/-- A predicate `P : ℕ → Prop` agrees with `frame w` shifted by `base` on
`[base, base + (frame w).length)` iff it is `false` at `base + 2 * w.length` and, for each
`j < w.length`, is `true` at `base + 2 * j` and agrees with `w[j]` at `base + 2 * j + 1`. -/
theorem forall_getElem?_frame_iff (w : List Bool) (base : ℕ) (P : ℕ → Prop) :
    (∀ p, base ≤ p → p < base + (frame w).length →
        (P p ↔ (frame w)[p - base]? = some true)) ↔
      (¬ P (base + 2 * w.length) ∧
        ∀ j < w.length, P (base + 2 * j) ∧ (P (base + 2 * j + 1) ↔ w[j]? = some true)) := by
  rw [length_frame]
  constructor
  · intro h
    refine ⟨?_, fun j hj => ⟨?_, ?_⟩⟩
    · have h0 := h (base + 2 * w.length) (by omega) (by omega)
      rw [Nat.add_sub_cancel_left, getElem?_frame_two_mul_length] at h0
      simpa using h0
    · have h1 := h (base + 2 * j) (by omega) (by omega)
      rw [Nat.add_sub_cancel_left, getElem?_frame_two_mul hj] at h1
      simpa using h1
    · have h2 := h (base + 2 * j + 1) (by omega) (by omega)
      have hsub : base + 2 * j + 1 - base = 2 * j + 1 := by omega
      rw [hsub, getElem?_frame_two_mul_add_one hj] at h2
      exact h2
  · rintro ⟨hend, hstep⟩ p hlo hhi
    by_cases hlast : p = base + 2 * w.length
    · subst hlast
      rw [Nat.add_sub_cancel_left, getElem?_frame_two_mul_length]
      simp [hend]
    · have hd : p - base < 2 * w.length := by omega
      let j := (p - base) / 2
      have hj : j < w.length := by omega
      rcases Nat.mod_two_eq_zero_or_one (p - base) with hmod | hmod
      · have hp : p = base + 2 * j := by omega
        have hsub : p - base = 2 * j := by omega
        rw [hsub, getElem?_frame_two_mul hj, hp]
        simp [(hstep j hj).1]
      · have hp : p = base + 2 * j + 1 := by omega
        have hsub : p - base = 2 * j + 1 := by omega
        rw [hsub, getElem?_frame_two_mul_add_one hj, hp]
        exact (hstep j hj).2

theorem forall_getElem?_append_iff (u w : List Bool) (P : ℕ → Prop) :
    (∀ p < (u ++ w).length, (P p ↔ (u ++ w)[p]? = some true)) ↔
      (∀ p < u.length, (P p ↔ u[p]? = some true)) ∧
        (∀ p, u.length ≤ p → p < u.length + w.length →
          (P p ↔ w[p - u.length]? = some true)) := by
  rw [List.length_append]
  constructor
  · intro h
    refine ⟨fun p hp => ?_, fun p hlo hhi => ?_⟩
    · have hp' := h p (by omega)
      rwa [List.getElem?_append_left hp] at hp'
    · have hp' := h p hhi
      rwa [List.getElem?_append_right hlo] at hp'
  · rintro ⟨hu, hw⟩ p hp
    by_cases hlt : p < u.length
    · rw [List.getElem?_append_left hlt]
      exact hu p hlt
    · have hle : u.length ≤ p := by omega
      rw [List.getElem?_append_right hle]
      exact hw p hle hp

/-! ### Generic stride-2 framing sentence -/

namespace FO

variable {L' : Language.{u, v}}

/-- The first-order sentence axiomatizing a single stride-2 framing step on `Fin B`:
starting at `baseRel`, the binary relation `mapRel(j, p)` maps `j ≤ w.length` to `base + 2 * j`,
writes `[true, w[j]]` into `outBitRel` at `base + 2 * j` and `base + 2 * j + 1`, writes the
terminator `false` at `base + 2 * w.length`, and sets `nextBaseRel` to
`{base + 2 * w.length + 1}`. -/
noncomputable def frameChunkSentence (r : L'.Relations 2)
    (inDom inBit : L'.Formula (Fin 1))
    (baseRel nextBaseRel : L'.Relations 1) (mapRel : L'.Relations 2)
    (outBitRel : L'.Relations 1) : L'.Sentence :=
  -- 1. Functionality of `mapRel`: `mapRel(j, p₁) ∧ mapRel(j, p₂) → p₁ = p₂`
  closeAll (Fin 3) ((rel₂ mapRel 0 1 ⊓ rel₂ mapRel 0 2) ⟹ varEq 1 2) ⊓
  -- 2. Base step at `j = 0`: `mapRel(0, p) ↔ baseRel(p)`
  closeAll (Fin 2) (isZero r 0 ⟹ (rel₂ mapRel 0 1 ⇔ rel₁ baseRel 1)) ⊓
  -- 3. Inductive step for `j` in `inDom`:
  closeAll (Fin 1) (atVar inDom 0 ⟹
    Formula.iExs (Fin 4) (
      rel₂ mapRel (.inl 0) (.inr 0) ⊓
      succ r (.inr 0) (.inr 1) ⊓
      succ r (.inr 1) (.inr 2) ⊓
      succ r (.inl 0) (.inr 3) ⊓
      rel₂ mapRel (.inr 3) (.inr 2) ⊓
      rel₁ outBitRel (.inr 0) ⊓
      (rel₁ outBitRel (.inr 1) ⇔ atVar inBit (.inl 0)))) ⊓
  -- 4. Terminator step at the first element `j` outside `inDom`:
  closeAll (Fin 1) (isFirstOut r inDom 0 ⟹
    Formula.iExs (Fin 2) (
      rel₂ mapRel (.inl 0) (.inr 0) ⊓
      succ r (.inr 0) (.inr 1) ⊓
      ∼(rel₁ outBitRel (.inr 0)) ⊓
      Formula.iAlls (Fin 1) (rel₁ nextBaseRel (.inr 0) ⇔ varEq (.inr 0) (.inl (.inr 1)))))

section FinOrder

variable {B : ℕ} [L'.Structure (Fin B)] {r : L'.Relations 2}
  (hlt : ∀ x : Fin 2 → Fin B, RelMap r x ↔ x 0 < x 1)

include hlt

/-- Soundness of `frameChunkSentence`: when `baseRel` holds solely of `base` and
`base + (frame w).length < B`, any realization of `frameChunkSentence` forces `nextBaseRel` to hold
solely of `base + (frame w).length` and `outBitRel` to agree with `frame w` on
`[base, base + (frame w).length)`. -/
theorem getElem?_frame_eq_of_realize_frameChunkSentence
    {inDom inBit : L'.Formula (Fin 1)}
    {baseRel nextBaseRel : L'.Relations 1} {mapRel : L'.Relations 2}
    {outBitRel : L'.Relations 1}
    {w : List Bool} {base : ℕ} (hbound : base + (frame w).length < B)
    (hdom : ∀ j : Fin B, inDom.Realize ![j] ↔ (j : ℕ) < w.length)
    (hbit : ∀ j : Fin B, (j : ℕ) < w.length → (inBit.Realize ![j] ↔ w[(j : ℕ)]? = some true))
    (hbase : ∀ z : Fin B, RelMap baseRel ![z] ↔ (z : ℕ) = base)
    (hreal : (frameChunkSentence r inDom inBit baseRel nextBaseRel mapRel outBitRel).Realize
      (Fin B)) :
    (∀ z : Fin B, RelMap nextBaseRel ![z] ↔ (z : ℕ) = base + (frame w).length) ∧
      (∀ p : Fin B, base ≤ (p : ℕ) → (p : ℕ) < base + (frame w).length →
        (RelMap outBitRel ![p] ↔ (frame w)[(p : ℕ) - base]? = some true)) := by
  have hlen : (frame w).length = 2 * w.length + 1 := length_frame w
  have hMB : w.length < B := by omega
  simp only [frameChunkSentence, Sentence.realize_inf, realize_closeAll,
    Formula.realize_imp, Formula.realize_inf, Formula.realize_iff, Formula.realize_not,
    Formula.realize_iExs, Formula.realize_iAlls, realize_rel₂, realize_rel₁,
    realize_varEq, realize_isZero hlt, realize_succ hlt, realize_atVar,
    realize_isFirstOut hlt hMB hdom, Sum.elim_inl, Sum.elim_inr] at hreal
  rcases hreal with ⟨⟨⟨hfunc, hzero⟩, hstep⟩, hend⟩
  -- Prove by induction on `m ≤ w.length` that `mapRel` maps `⟨m, _⟩` uniquely to `base + 2 * m`.
  have hmap : ∀ m ≤ w.length, ∀ (j p : Fin B), (j : ℕ) = m →
      (RelMap mapRel ![j, p] ↔ (p : ℕ) = base + 2 * m) := by
    intro m hm
    induction m with
    | zero =>
      intro j p hj
      have hz := hzero ![j, p] hj
      simpa [hbase] using hz
    | succ m ih =>
      intro j p hj
      have hm' : m < w.length := by omega
      let j₀ : Fin B := ⟨m, by omega⟩
      have hj₀ : (j₀ : ℕ) < w.length := hm'
      obtain ⟨y, ⟨⟨⟨⟨⟨hmap0, hs0⟩, hs1⟩, hsj⟩, hmap1⟩, _⟩, _⟩ :=
        hstep ![j₀] ((hdom j₀).2 hj₀)
      simp only [Matrix.cons_val_zero] at hmap0 hsj
      have hj₀_val : (j₀ : ℕ) = m := rfl
      have hy0 : (y 0 : ℕ) = base + 2 * m := (ih (by omega) j₀ (y 0) rfl).1 hmap0
      have hy2 : (y 2 : ℕ) = base + 2 * (m + 1) := by omega
      have hy3 : y 3 = j := Fin.ext (by omega)
      rw [hy3] at hmap1
      constructor
      · intro hjp
        have heq : p = y 2 :=
          hfunc ![j, p, y 2] ⟨hjp, hmap1⟩
        rw [heq, hy2]
      · intro hp
        have heq : p = y 2 := Fin.ext (by omega)
        rwa [heq]
  -- Extract the end condition at `m = w.length`.
  let jM : Fin B := ⟨w.length, hMB⟩
  obtain ⟨yEnd, ⟨⟨hmapEnd, hsEnd⟩, houtEnd⟩, hnextEnd⟩ := hend ![jM] rfl
  simp only [Matrix.cons_val_zero] at hmapEnd
  have hyEnd0 : (yEnd 0 : ℕ) = base + 2 * w.length :=
    (hmap w.length (le_refl _) jM (yEnd 0) rfl).1 hmapEnd
  have hyEnd1 : (yEnd 1 : ℕ) = base + (frame w).length := by omega
  have hnext : ∀ z : Fin B, RelMap nextBaseRel ![z] ↔ (z : ℕ) = base + (frame w).length := by
    intro z
    simpa [Fin.ext_iff, hyEnd1] using hnextEnd ![z]
  refine ⟨hnext, ?_⟩
  -- Apply `forall_getElem?_frame_iff` to `fun n => ∃ h : n < B, RelMap outBitRel ![⟨n, h⟩]`.
  have hP : ∀ n, base ≤ n → n < base + (frame w).length →
      ((∃ h : n < B, RelMap outBitRel ![(⟨n, h⟩ : Fin B)]) ↔
        (frame w)[n - base]? = some true) := by
    apply (forall_getElem?_frame_iff w base
      (fun n => ∃ h : n < B, RelMap outBitRel ![(⟨n, h⟩ : Fin B)])).2
    refine ⟨?_, fun m hm => ?_⟩
    · rintro ⟨hltB, hout⟩
      have heq : (⟨base + 2 * w.length, hltB⟩ : Fin B) = yEnd 0 := Fin.ext hyEnd0.symm
      rw [heq] at hout
      exact houtEnd hout
    · let jm : Fin B := ⟨m, by omega⟩
      obtain ⟨y, ⟨⟨⟨⟨⟨hmap0, hs0⟩, hs1⟩, _⟩, _⟩, hout0⟩, hout1⟩ :=
        hstep ![jm] ((hdom jm).2 hm)
      simp only [Matrix.cons_val_zero] at hmap0 hout1
      have hy0 : (y 0 : ℕ) = base + 2 * m := (hmap m (by omega) jm (y 0) rfl).1 hmap0
      have hy1 : (y 1 : ℕ) = base + 2 * m + 1 := by omega
      have h0B : base + 2 * m < B := by omega
      have h1B : base + 2 * m + 1 < B := by omega
      refine ⟨⟨h0B, ?_⟩, ?_⟩
      · have heq : (⟨base + 2 * m, h0B⟩ : Fin B) = y 0 := Fin.ext hy0.symm
        rwa [heq]
      · rw [← hbit jm hm, ← hout1]
        constructor
        · rintro ⟨h1, hout'⟩
          have heq : (⟨base + 2 * m + 1, h1⟩ : Fin B) = y 1 := Fin.ext hy1.symm
          rwa [← heq]
        · intro hout'
          refine ⟨h1B, ?_⟩
          have heq : (⟨base + 2 * m + 1, h1B⟩ : Fin B) = y 1 := Fin.ext hy1.symm
          rwa [heq]
  intro p hlo hhi
  have hp := hP (p : ℕ) hlo hhi
  simpa [p.2] using hp

/-- Completeness of `frameChunkSentence`: the canonical stride-2 relation
`mapRel(j, p) ↔ j ≤ w.length ∧ p = base + 2 * j` satisfies `frameChunkSentence` whenever
`baseRel` is `{base}`, `nextBaseRel` is `{base + (frame w).length}`, and `outBitRel` agrees with
`frame w` on `[base, base + (frame w).length)`. -/
theorem realize_frameChunkSentence_of_canonical
    {inDom inBit : L'.Formula (Fin 1)}
    {baseRel nextBaseRel : L'.Relations 1} {mapRel : L'.Relations 2}
    {outBitRel : L'.Relations 1}
    {w : List Bool} {base : ℕ} (hbound : base + (frame w).length < B)
    (hdom : ∀ j : Fin B, inDom.Realize ![j] ↔ (j : ℕ) < w.length)
    (hbit : ∀ j : Fin B, (j : ℕ) < w.length → (inBit.Realize ![j] ↔ w[(j : ℕ)]? = some true))
    (hbase : ∀ z : Fin B, RelMap baseRel ![z] ↔ (z : ℕ) = base)
    (hnext : ∀ z : Fin B, RelMap nextBaseRel ![z] ↔ (z : ℕ) = base + (frame w).length)
    (hmap : ∀ j p : Fin B,
      RelMap mapRel ![j, p] ↔ (j : ℕ) ≤ w.length ∧ (p : ℕ) = base + 2 * (j : ℕ))
    (hout : ∀ p : Fin B, base ≤ (p : ℕ) → (p : ℕ) < base + (frame w).length →
      (RelMap outBitRel ![p] ↔ (frame w)[(p : ℕ) - base]? = some true)) :
    (frameChunkSentence r inDom inBit baseRel nextBaseRel mapRel outBitRel).Realize (Fin B) := by
  have hlen : (frame w).length = 2 * w.length + 1 := length_frame w
  have hMB : w.length < B := by omega
  simp only [frameChunkSentence, Sentence.realize_inf, realize_closeAll,
    Formula.realize_imp, Formula.realize_inf, Formula.realize_iff, Formula.realize_not,
    Formula.realize_iExs, Formula.realize_iAlls, realize_rel₂, realize_rel₁,
    realize_varEq, realize_isZero hlt, realize_succ hlt, realize_atVar,
    realize_isFirstOut hlt hMB hdom, Sum.elim_inl, Sum.elim_inr]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro v ⟨h1, h2⟩
    rw [hmap] at h1 h2
    exact Fin.ext (by omega)
  · intro v hv0
    rw [hmap, hbase, hv0]
    omega
  · intro v hv
    have hj : (v 0 : ℕ) < w.length := (hdom (v 0)).1 hv
    let p0 : Fin B := ⟨base + 2 * (v 0 : ℕ), by omega⟩
    let p1 : Fin B := ⟨base + 2 * (v 0 : ℕ) + 1, by omega⟩
    let p2 : Fin B := ⟨base + 2 * ((v 0 : ℕ) + 1), by omega⟩
    let j1 : Fin B := ⟨(v 0 : ℕ) + 1, by omega⟩
    refine ⟨![p0, p1, p2, j1],
      ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · change RelMap mapRel ![v 0, p0]
      rw [hmap]; exact ⟨by omega, rfl⟩
    · change (p1 : ℕ) = (p0 : ℕ) + 1; rfl
    · change (p2 : ℕ) = (p1 : ℕ) + 1
      change base + 2 * ((v 0 : ℕ) + 1) = (base + 2 * (v 0 : ℕ) + 1) + 1; omega
    · change (j1 : ℕ) = (v 0 : ℕ) + 1; rfl
    · change RelMap mapRel ![j1, p2]
      rw [hmap]
      exact ⟨by change (v 0 : ℕ) + 1 ≤ w.length; omega, rfl⟩
    · change RelMap outBitRel ![p0]
      rw [hout p0 (by change base ≤ base + 2 * (v 0 : ℕ); omega)
        (by change base + 2 * (v 0 : ℕ) < base + (frame w).length; omega)]
      change (frame w)[base + 2 * (v 0 : ℕ) - base]? = some true
      rw [Nat.add_sub_cancel_left, getElem?_frame_two_mul hj]
    · change RelMap outBitRel ![p1] ↔ inBit.Realize ![v 0]
      rw [hout p1 (by change base ≤ base + 2 * (v 0 : ℕ) + 1; omega)
        (by change base + 2 * (v 0 : ℕ) + 1 < base + (frame w).length; omega),
        hbit (v 0) hj]
      have hsub : (p1 : ℕ) - base = 2 * (v 0 : ℕ) + 1 := by
        change base + 2 * (v 0 : ℕ) + 1 - base = _; omega
      rw [hsub, getElem?_frame_two_mul_add_one hj]
  · intro v hv
    let p0 : Fin B := ⟨base + 2 * w.length, by omega⟩
    let p1 : Fin B := ⟨base + (frame w).length, hbound⟩
    refine ⟨![p0, p1], ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · change RelMap mapRel ![v 0, p0]
      rw [hmap, hv]; exact ⟨le_refl _, rfl⟩
    · change (p1 : ℕ) = (p0 : ℕ) + 1
      change base + (frame w).length = base + 2 * w.length + 1; omega
    · change ¬ RelMap outBitRel ![p0]
      rw [hout p0 (by change base ≤ base + 2 * w.length; omega)
        (by change base + 2 * w.length < base + (frame w).length; omega)]
      change ¬ ((frame w)[base + 2 * w.length - base]? = some true)
      rw [Nat.add_sub_cancel_left, getElem?_frame_two_mul_length]
      decide
    · intro z
      change RelMap nextBaseRel ![z 0] ↔ z 0 = p1
      rw [hnext, Fin.ext_iff]

end FinOrder

end FO

/-! ### Prefix decomposition of `encStructure a` -/

namespace Vocabulary

variable {L : Language.{u, v}} (v : Vocabulary L)

/-- The prefix of `encStructure a` consisting of `frame (encUnary a.1)` followed by the framed
truth tables of the first `m` relation symbols of `v`. -/
def encStructurePrefix (a : EncodedStructure) (m : ℕ) : List Bool :=
  frame (encUnary a.1) ++
    (((List.ofFn fun i : Fin v.count => v.table a (v.symbol i)).take m).flatMap frame)

@[simp]
theorem encStructurePrefix_zero (a : EncodedStructure) :
    v.encStructurePrefix a 0 = frame (encUnary a.1) := by
  simp [encStructurePrefix]

theorem encStructurePrefix_succ (a : EncodedStructure) (i : Fin v.count) :
    v.encStructurePrefix a (i.1 + 1) =
      v.encStructurePrefix a i.1 ++ frame (v.table a (v.symbol i)) := by
  simp only [encStructurePrefix]
  have htake :
      (List.ofFn fun j : Fin v.count => v.table a (v.symbol j)).take (i.1 + 1) =
        (List.ofFn fun j : Fin v.count => v.table a (v.symbol j)).take i.1 ++
          [v.table a (v.symbol i)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp [i.2]), List.getElem_ofFn]
    simp
  rw [htake, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

theorem encStructurePrefix_count {a : EncodedStructure} (ha : v.WellFormed a) :
    v.encStructurePrefix a v.count = encStructure a := by
  simp only [encStructurePrefix, encStructure, encPair_apply, encList]
  congr 1
  have htables : (List.ofFn fun i : Fin v.count => v.table a (v.symbol i)) = a.2 := by
    refine List.ext_getElem (by simp [ha.1]) fun i hi hi' => ?_
    simp only [List.getElem_ofFn, table, index, Equiv.symm_apply_apply]
    exact List.getD_eq_getElem a.2 [] hi'
  rw [List.take_of_length_le (by simp), htables]
  rfl

theorem length_encStructurePrefix_le (a : EncodedStructure) {m : ℕ} (hm : m ≤ v.count) :
    (v.encStructurePrefix a m).length ≤ (v.encStructurePrefix a v.count).length := by
  simp only [encStructurePrefix, List.length_append]
  exact Nat.add_le_add_left (((List.take_sublist_take_left hm).flatMap frame).length_le) _

/-! ### The input variable language and layout ESO sentence -/

/-- The language of the two unary relations exposed by `layoutESOSentence` to the Cook–Levin
tableau:
* `false` (`uBitSym`): bit `p` of `u = frame (encStructure a)`, and
* `true` (`uLenSym`): the singleton `{u.length}`. -/
abbrev inputVarLanguage : Language.{0, 0} :=
  ESO.varLanguage (fun _ : Bool => 1)

/-- The unary relation symbol `uBit(p)` in `inputVarLanguage`. -/
def uBitSym : inputVarLanguage.Relations 1 :=
  ⟨false, rfl⟩

/-- The unary relation symbol `uLen(p)` in `inputVarLanguage`. -/
def uLenSym : inputVarLanguage.Relations 1 :=
  ⟨true, rfl⟩

/-- The index type of internal relation variables quantified by `v.layoutESOSentence`:
* `.inl (.inl m)` (`m : Fin (v.count + 2)`): unary `base_m`,
* `.inl (.inr ())`: unary `rawBit`,
* `.inr (.inl m)` (`m : Fin (v.count + 1)`): binary `chunkMap_m`,
* `.inr (.inr ())`: binary `outerMap`. -/
abbrev LayoutVar (count : ℕ) : Type :=
  (Fin (count + 2) ⊕ Unit) ⊕ (Fin (count + 1) ⊕ Unit)

/-- The arities of `LayoutVar`: `1` on the left summand and `2` on the right summand. -/
def layoutArity (count : ℕ) : LayoutVar count → ℕ
  | .inl _ => 1
  | .inr _ => 2

/-- The combined language of `v.layoutESOSentence`'s first-order matrix. -/
abbrev layoutMatrixLanguage : Language.{0, 0} :=
  (v.powerLanguage.sum inputVarLanguage).sum (ESO.varLanguage (layoutArity v.count))

/-- Binary `<` inside `v.layoutMatrixLanguage`. -/
def layoutLt : v.layoutMatrixLanguage.Relations 2 :=
  .inl (.inl v.powerLt)

/-- Unary `< n` inside `v.layoutMatrixLanguage`. -/
def layoutIsElem : v.layoutMatrixLanguage.Relations 1 :=
  .inl (.inl v.powerIsElem)

/-- Unary `< n ^ v.arity i` inside `v.layoutMatrixLanguage`. -/
def layoutInTable (i : Fin v.count) : v.layoutMatrixLanguage.Relations 1 :=
  .inl (.inl (v.powerInTable i))

/-- Unary relation table bit `i` inside `v.layoutMatrixLanguage`. -/
def layoutTableBit (i : Fin v.count) : v.layoutMatrixLanguage.Relations 1 :=
  .inl (.inl (v.powerTableBit i))

/-- Unary `uBit` inside `v.layoutMatrixLanguage`. -/
def layoutUBit : v.layoutMatrixLanguage.Relations 1 :=
  .inl (.inr uBitSym)

/-- Unary `uLen` inside `v.layoutMatrixLanguage`. -/
def layoutULen : v.layoutMatrixLanguage.Relations 1 :=
  .inl (.inr uLenSym)

/-- Unary `base_m` (`m : Fin (v.count + 2)`) inside `v.layoutMatrixLanguage`. -/
def layoutBase (m : Fin (v.count + 2)) : v.layoutMatrixLanguage.Relations 1 :=
  .inr ⟨.inl (.inl m), rfl⟩

/-- Unary `rawBit` inside `v.layoutMatrixLanguage`. -/
def layoutRawBit : v.layoutMatrixLanguage.Relations 1 :=
  .inr ⟨.inl (.inr ()), rfl⟩

/-- Binary `chunkMap_m` (`m : Fin (v.count + 1)`) inside `v.layoutMatrixLanguage`. -/
def layoutChunkMap (m : Fin (v.count + 1)) : v.layoutMatrixLanguage.Relations 2 :=
  .inr ⟨.inr (.inl m), rfl⟩

/-- Binary `outerMap` inside `v.layoutMatrixLanguage`. -/
def layoutOuterMap : v.layoutMatrixLanguage.Relations 2 :=
  .inr ⟨.inr (.inr ()), rfl⟩

/-- The domain formula `j < rawLen` for the outer framing step
(`base_{v.count + 1}` is `rawLen`). -/
noncomputable def layoutInRaw : v.layoutMatrixLanguage.Formula (Fin 1) :=
  Formula.iExs (Fin 1) (FO.rel₁ (v.layoutBase (Fin.last (v.count + 1))) (.inr 0) ⊓
    FO.lt v.layoutLt (.inl 0) (.inr 0))

/-- The first-order matrix of `v.layoutESOSentence`:
1. `base_0` holds solely of `0`,
2. chunk `0` frames `encUnary a.1` (`inDom = powerIsElem`, `inBit = ⊤`) from `base_0` to `base_1`
   into `rawBit`,
3. for each `i : Fin v.count`, chunk `i + 1` frames table `i` (`inDom = powerInTable i`,
   `inBit = powerTableBit i`) from `base_{i + 1}` to `base_{i + 2}` into `rawBit`, and
4. the outer chunk frames `encStructure a` (`inDom = layoutInRaw`, `inBit = rawBit`) from `base_0`
   to `uLen` into `uBit`. -/
noncomputable def layoutMatrix : v.layoutMatrixLanguage.Sentence :=
  FO.closeAll (Fin 1) (FO.rel₁ (v.layoutBase 0) 0 ⇔ FO.isZero v.layoutLt 0) ⊓
  FO.frameChunkSentence v.layoutLt (FO.rel₁ v.layoutIsElem 0) ⊤
    (v.layoutBase 0) (v.layoutBase 1) (v.layoutChunkMap 0) v.layoutRawBit ⊓
  (Formula.iInf fun i : Fin v.count =>
    FO.frameChunkSentence v.layoutLt
      (FO.rel₁ (v.layoutInTable i) 0) (FO.rel₁ (v.layoutTableBit i) 0)
      (v.layoutBase i.succ.castSucc) (v.layoutBase i.succ.succ)
      (v.layoutChunkMap i.succ) v.layoutRawBit) ⊓
  FO.frameChunkSentence v.layoutLt v.layoutInRaw (FO.rel₁ v.layoutRawBit 0)
    (v.layoutBase 0) v.layoutULen v.layoutOuterMap v.layoutUBit

/-- The existential second-order sentence over `v.powerLanguage.sum inputVarLanguage` that forces
`uLenSym` to hold solely of `(frame (encStructure a)).length` and `uBitSym` to agree with
`frame (encStructure a)` below `(frame (encStructure a)).length`. -/
noncomputable def layoutESOSentence : ESO.Sentence (v.powerLanguage.sum inputVarLanguage) where
  Var := LayoutVar v.count
  arity := layoutArity v.count
  matrix := v.layoutMatrix

/-- **Characterization of `layoutESOSentence`**: on `(Fin B, v.powerStructure a B)` for a
well-formed input `a` with `(frame (encStructure a)).length < B`, an interpretation `I_in` of
`inputVarLanguage` satisfies `v.layoutESOSentence` iff `I_in true` (`uLenSym`) holds solely of
`(frame (encStructure a)).length` and `I_in false` (`uBitSym`) agrees with `frame (encStructure a)`
on all positions `< (frame (encStructure a)).length`. -/
theorem realize_layoutESOSentence {a : EncodedStructure} (ha : v.WellFormed a) {B : ℕ}
    (hB : (frame (encStructure a)).length < B)
    (I_in : ∀ b : Bool, Set (Fin ((fun _ : Bool => 1) b) → Fin B)) :
    (letI := v.powerStructure a B;
      letI := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in;
      v.layoutESOSentence.Realize (Fin B)) ↔
      (∀ z : Fin B, ![z] ∈ I_in true ↔ (z : ℕ) = (frame (encStructure a)).length) ∧
        (∀ p : Fin B, (p : ℕ) < (frame (encStructure a)).length →
          (![p] ∈ I_in false ↔ (frame (encStructure a))[(p : ℕ)]? = some true)) := by
  let _ := v.powerStructure a B
  let _ := ESO.varLanguage.structure (arity := fun _ : Bool => 1) I_in
  rw [layoutESOSentence, ESO.Sentence.Realize]
  have hrawB : (encStructure a).length < B := by
    have := length_frame (encStructure a)
    omega
  have hb0 : 0 + (frame (encUnary a.1)).length < B := by
    have := v.length_encStructurePrefix_le a (Nat.zero_le v.count)
    rw [v.encStructurePrefix_zero, v.encStructurePrefix_count ha] at this
    omega
  have hb_idx (idx : Fin v.count) :
      (v.encStructurePrefix a idx.1).length + (frame (v.table a (v.symbol idx))).length < B := by
    have h1 := v.length_encStructurePrefix_le a (by omega : idx.1 + 1 ≤ v.count)
    rw [v.encStructurePrefix_count ha] at h1
    rw [← List.length_append, ← v.encStructurePrefix_succ a idx]
    omega
  have hdom0 (R : ∀ i : LayoutVar v.count, Set (Fin (layoutArity v.count i) → Fin B)) (j : Fin B) :
      letI := ESO.varLanguage.structure (arity := layoutArity v.count) R
      (FO.rel₁ v.layoutIsElem (0 : Fin 1)).Realize ![j] ↔ (j : ℕ) < (encUnary a.1).length := by
    let _ := ESO.varLanguage.structure (arity := layoutArity v.count) R
    rw [FO.realize_rel₁]; simp [encUnary_apply]; rfl
  have hbit0 (R : ∀ i : LayoutVar v.count, Set (Fin (layoutArity v.count i) → Fin B))
      (j : Fin B) (hj : (j : ℕ) < (encUnary a.1).length) :
      letI := ESO.varLanguage.structure (arity := layoutArity v.count) R
      ((⊤ : v.layoutMatrixLanguage.Formula (Fin 1)).Realize ![j] ↔
        (encUnary a.1)[(j : ℕ)]? = some true) := by
    let _ := ESO.varLanguage.structure (arity := layoutArity v.count) R
    simp only [Formula.realize_top, true_iff, encUnary_apply]
    rw [List.getElem?_eq_getElem (by simpa using hj), List.getElem_replicate]
  have hdom_idx (R : ∀ i : LayoutVar v.count, Set (Fin (layoutArity v.count i) → Fin B))
      (idx : Fin v.count) (j : Fin B) :
      letI := ESO.varLanguage.structure (arity := layoutArity v.count) R
      (FO.rel₁ (v.layoutInTable idx) (0 : Fin 1)).Realize ![j] ↔
        (j : ℕ) < (v.table a (v.symbol idx)).length := by
    let _ := ESO.varLanguage.structure (arity := layoutArity v.count) R
    rw [FO.realize_rel₁, Vocabulary.WellFormed.length_table v ha (v.symbol idx)]
    exact v.relMap_powerInTable a B idx ![j]
  have hbit_idx (R : ∀ i : LayoutVar v.count, Set (Fin (layoutArity v.count i) → Fin B))
      (idx : Fin v.count) (j : Fin B) (hj : (j : ℕ) < (v.table a (v.symbol idx)).length) :
      letI := ESO.varLanguage.structure (arity := layoutArity v.count) R
      ((FO.rel₁ (v.layoutTableBit idx) (0 : Fin 1)).Realize ![j] ↔
        (v.table a (v.symbol idx))[(j : ℕ)]? = some true) := by
    let _ := ESO.varLanguage.structure (arity := layoutArity v.count) R
    have hlen_table := Vocabulary.WellFormed.length_table v ha (v.symbol idx)
    rw [FO.realize_rel₁]
    change ((j : ℕ) < a.1 ^ (v.symbol idx).1 ∧
      (v.table a (v.symbol idx)).getD (j : ℕ) false = true) ↔ _
    rw [← hlen_table, and_iff_right hj, List.getD_eq_getElem _ _ hj,
      List.getElem?_eq_getElem hj, Option.some.injEq]
  have hdom_outer (R : ∀ i : LayoutVar v.count, Set (Fin (layoutArity v.count i) → Fin B))
      (hbase_last : letI := ESO.varLanguage.structure (arity := layoutArity v.count) R;
        ∀ z : Fin B, RelMap (v.layoutBase (Fin.last (v.count + 1))) ![z] ↔
          (z : ℕ) = (encStructure a).length)
      (j : Fin B) :
      letI := ESO.varLanguage.structure (arity := layoutArity v.count) R
      v.layoutInRaw.Realize ![j] ↔ (j : ℕ) < (encStructure a).length := by
    let _ := ESO.varLanguage.structure (arity := layoutArity v.count) R
    have hlt : ∀ x : Fin 2 → Fin B, RelMap v.layoutLt x ↔ x 0 < x 1 := fun _ => Iff.rfl
    simp only [layoutInRaw, Formula.realize_iExs, Formula.realize_inf,
      FO.realize_rel₁, FO.realize_lt hlt, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero]
    refine ⟨fun ⟨y, hy, hjy⟩ => ?_, fun hj => ⟨![⟨(encStructure a).length, hrawB⟩],
      (hbase_last _).2 rfl, by simpa [Fin.lt_def] using hj⟩⟩
    have hy' := (hbase_last (y 0)).1 hy
    rw [Fin.lt_def] at hjy; omega
  constructor
  · -- Soundness: any witness `R` for `layoutMatrix` forces `uLen` and `uBit`.
    rintro ⟨R, hR⟩
    let _ := ESO.varLanguage.structure (arity := layoutArity v.count) R
    have hlt : ∀ x : Fin 2 → Fin B, RelMap v.layoutLt x ↔ x 0 < x 1 := fun _ => Iff.rfl
    simp only [layoutMatrix, Sentence.realize_inf, FO.realize_closeAll,
      Formula.realize_iff, FO.realize_rel₁, FO.realize_isZero hlt] at hR
    rcases hR with ⟨⟨⟨hbase0, hchunk0⟩, hchunks⟩, houter⟩
    rw [Sentence.Realize, Formula.realize_iInf] at hchunks
    have hbase0' : ∀ z : Fin B, RelMap (v.layoutBase 0) ![z] ↔ (z : ℕ) = 0 := fun z =>
      hbase0 ![z]
    -- Prove by induction on `m ≤ v.count` that `base_{m+1}` is `(encStructurePrefix a m).length`
    -- and `rawBit` agrees with `encStructurePrefix a m` below `(encStructurePrefix a m).length`.
    have hprefix : ∀ (m : ℕ) (hm : m ≤ v.count),
        (∀ z : Fin B, RelMap (v.layoutBase ⟨m + 1, by omega⟩) ![z] ↔
          (z : ℕ) = (v.encStructurePrefix a m).length) ∧
        (∀ p : Fin B, (p : ℕ) < (v.encStructurePrefix a m).length →
          (RelMap v.layoutRawBit ![p] ↔ (v.encStructurePrefix a m)[(p : ℕ)]? = some true)) := by
      intro m hm
      induction m with
      | zero =>
        obtain ⟨hnext, hout⟩ :=
          FO.getElem?_frame_eq_of_realize_frameChunkSentence hlt hb0 (hdom0 R) (hbit0 R)
            hbase0' hchunk0
        simp only [Nat.zero_add, Nat.sub_zero, ← v.encStructurePrefix_zero a] at hnext hout
        exact ⟨hnext, fun p hp => hout p (Nat.zero_le _) hp⟩
      | succ m ih =>
        let idx : Fin v.count := ⟨m, by omega⟩
        obtain ⟨hbase_m, hout_m⟩ := ih (by omega)
        have hsucc_eq := v.encStructurePrefix_succ a idx
        have hb_m : (v.encStructurePrefix a m).length +
            (frame (v.table a (v.symbol idx))).length < B := hb_idx idx
        obtain ⟨hnext, hout⟩ :=
          FO.getElem?_frame_eq_of_realize_frameChunkSentence hlt hb_m (hdom_idx R idx)
            (hbit_idx R idx) hbase_m (hchunks idx)
        refine ⟨fun z => ?_, fun p hp => ?_⟩
        · change RelMap (v.layoutBase idx.succ.succ) ![z] ↔
            (z : ℕ) = (v.encStructurePrefix a (idx.1 + 1)).length
          rw [hsucc_eq, List.length_append]
          exact hnext z
        · change (p : ℕ) < (v.encStructurePrefix a (idx.1 + 1)).length at hp
          change RelMap v.layoutRawBit ![p] ↔
            (v.encStructurePrefix a (idx.1 + 1))[(p : ℕ)]? = some true
          rw [hsucc_eq] at hp ⊢
          have hP : ∀ n < (v.encStructurePrefix a m ++ frame (v.table a (v.symbol idx))).length,
              ((∃ hn : n < B, RelMap v.layoutRawBit ![(⟨n, hn⟩ : Fin B)]) ↔
                (v.encStructurePrefix a m ++
                  frame (v.table a (v.symbol idx)))[n]? = some true) := by
            apply (forall_getElem?_append_iff (v.encStructurePrefix a m)
              (frame (v.table a (v.symbol idx)))
              (fun n => ∃ hn : n < B, RelMap v.layoutRawBit ![(⟨n, hn⟩ : Fin B)])).2
            refine ⟨fun n hn => ?_, fun n hlo hhi => ?_⟩
            · have hnB : n < B := by omega
              simpa [hnB] using hout_m ⟨n, hnB⟩ hn
            · have hnB : n < B := by omega
              simpa [hnB] using hout ⟨n, hnB⟩ hlo hhi
          simpa [p.2] using hP (p : ℕ) hp
    -- Specialize `hprefix` at `m = v.count`.
    obtain ⟨hbase_last, hout_last⟩ := hprefix v.count (le_refl _)
    rw [v.encStructurePrefix_count ha] at hbase_last hout_last
    have hbit_outer : ∀ j : Fin B, (j : ℕ) < (encStructure a).length →
        ((FO.rel₁ v.layoutRawBit (0 : Fin 1)).Realize ![j] ↔
          (encStructure a)[(j : ℕ)]? = some true) := fun j hj => by
      rw [FO.realize_rel₁, Matrix.cons_val_zero]; exact hout_last j hj
    obtain ⟨hnext_outer, hout_outer⟩ :=
      FO.getElem?_frame_eq_of_realize_frameChunkSentence hlt (by omega)
        (hdom_outer R hbase_last) hbit_outer hbase0' houter
    simp only [Nat.zero_add, Nat.sub_zero] at hnext_outer hout_outer
    exact ⟨hnext_outer, fun p hp => hout_outer p (Nat.zero_le _) hp⟩
  · -- Completeness: construct the canonical relation assignment `R` for `layoutMatrix`.
    rintro ⟨huLen, huBit⟩
    let baseAt : Fin (v.count + 2) → ℕ := fun m =>
      if (m : ℕ) = 0 then 0 else (v.encStructurePrefix a ((m : ℕ) - 1)).length
    let R : ∀ i : LayoutVar v.count, Set (Fin (layoutArity v.count i) → Fin B)
      | .inl (.inl m) => {x : Fin 1 → Fin B | (x 0 : ℕ) = baseAt m}
      | .inl (.inr ()) => {x : Fin 1 → Fin B | (encStructure a)[(x 0 : ℕ)]? = some true}
      | .inr (.inl m) =>
        if h : (m : ℕ) = 0 then
          {x : Fin 2 → Fin B | (x 0 : ℕ) ≤ a.1 ∧ (x 1 : ℕ) = 2 * (x 0 : ℕ)}
        else
          let idx : Fin v.count := ⟨(m : ℕ) - 1, by omega⟩
          {x : Fin 2 → Fin B | (x 0 : ℕ) ≤ a.1 ^ v.arity idx ∧
            (x 1 : ℕ) = (v.encStructurePrefix a idx.1).length + 2 * (x 0 : ℕ)}
      | .inr (.inr ()) =>
        {x : Fin 2 → Fin B | (x 0 : ℕ) ≤ (encStructure a).length ∧ (x 1 : ℕ) = 2 * (x 0 : ℕ)}
    refine ⟨R, ?_⟩
    let _ := ESO.varLanguage.structure (arity := layoutArity v.count) R
    have hlt : ∀ x : Fin 2 → Fin B, RelMap v.layoutLt x ↔ x 0 < x 1 := fun _ => Iff.rfl
    have hbase_char : ∀ (m : Fin (v.count + 2)) (z : Fin B),
        RelMap (v.layoutBase m) ![z] ↔ (z : ℕ) = baseAt m := fun _ _ => Iff.rfl
    have hbase0 : ∀ z : Fin B, RelMap (v.layoutBase 0) ![z] ↔ (z : ℕ) = 0 := by
      intro z; simp [hbase_char, baseAt]
    have hraw_prefix : ∀ (m : ℕ) (hm : m ≤ v.count) (p : Fin B),
        (p : ℕ) < (v.encStructurePrefix a m).length →
          (RelMap v.layoutRawBit ![p] ↔ (v.encStructurePrefix a m)[(p : ℕ)]? = some true) := by
      intro m hm p hp
      change (encStructure a)[(p : ℕ)]? = some true ↔ _
      rw [← v.encStructurePrefix_count ha]
      have hsub : v.encStructurePrefix a v.count =
          v.encStructurePrefix a m ++
            ((List.ofFn fun i : Fin v.count => v.table a (v.symbol i)).drop m |>.flatMap
              frame) := by
        simp only [encStructurePrefix, List.append_assoc, ← List.flatMap_append]
        congr 2
        rw [List.take_append_drop, List.take_of_length_le (by simp)]
      rw [hsub, List.getElem?_append_left hp]
    simp only [layoutMatrix, Sentence.realize_inf, FO.realize_closeAll,
      Formula.realize_iff, FO.realize_rel₁, FO.realize_isZero hlt]
    refine ⟨⟨⟨fun x => hbase0 (x 0), ?_⟩, ?_⟩, ?_⟩
    · -- Chunk 0 (`encUnary a.1`)
      have hnext0 : ∀ z : Fin B,
          RelMap (v.layoutBase 1) ![z] ↔ (z : ℕ) = 0 + (frame (encUnary a.1)).length := by
        intro z; rw [hbase_char]; simp [baseAt, v.encStructurePrefix_zero]
      have hmap0 : ∀ j p : Fin B,
          RelMap (v.layoutChunkMap 0) ![j, p] ↔
            (j : ℕ) ≤ (encUnary a.1).length ∧ (p : ℕ) = 0 + 2 * (j : ℕ) := by
        intro j p; change ((j : ℕ) ≤ a.1 ∧ (p : ℕ) = 2 * (j : ℕ)) ↔ _; simp
      have hout0 : ∀ p : Fin B, 0 ≤ (p : ℕ) → (p : ℕ) < 0 + (frame (encUnary a.1)).length →
          (RelMap v.layoutRawBit ![p] ↔ (frame (encUnary a.1))[(p : ℕ) - 0]? = some true) := by
        intro p _ hp
        simpa [v.encStructurePrefix_zero] using hraw_prefix 0 (Nat.zero_le _) p
          (by simpa [v.encStructurePrefix_zero] using hp)
      exact FO.realize_frameChunkSentence_of_canonical hlt hb0 (hdom0 R) (hbit0 R) hbase0
        hnext0 hmap0 hout0
    · -- Chunk `idx + 1` (table `idx`)
      rw [Sentence.Realize, Formula.realize_iInf]
      intro idx
      have hsucc_eq := v.encStructurePrefix_succ a idx
      have hbase_idx : ∀ z : Fin B,
          RelMap (v.layoutBase idx.succ.castSucc) ![z] ↔
            (z : ℕ) = (v.encStructurePrefix a idx.1).length := by
        intro z; rw [hbase_char]; simp [baseAt]
      have hnext_idx : ∀ z : Fin B,
          RelMap (v.layoutBase idx.succ.succ) ![z] ↔
            (z : ℕ) = (v.encStructurePrefix a idx.1).length +
              (frame (v.table a (v.symbol idx))).length := by
        intro z; rw [hbase_char, ← List.length_append, ← hsucc_eq]; simp [baseAt]
      have hmap_idx : ∀ j p : Fin B,
          RelMap (v.layoutChunkMap idx.succ) ![j, p] ↔
            (j : ℕ) ≤ (v.table a (v.symbol idx)).length ∧
              (p : ℕ) = (v.encStructurePrefix a idx.1).length + 2 * (j : ℕ) := by
        intro j p; rw [Vocabulary.WellFormed.length_table v ha (v.symbol idx)]
        change ![j, p] ∈ R (.inr (.inl idx.succ)) ↔ _; simp [R]; rfl
      have hout_idx : ∀ p : Fin B,
          (v.encStructurePrefix a idx.1).length ≤ (p : ℕ) →
          (p : ℕ) < (v.encStructurePrefix a idx.1).length +
            (frame (v.table a (v.symbol idx))).length →
          (RelMap v.layoutRawBit ![p] ↔
            (frame (v.table a (v.symbol idx)))[(p : ℕ) - (v.encStructurePrefix a idx.1).length]? =
              some true) := by
        intro p hlo hhi
        have hp' : (p : ℕ) < (v.encStructurePrefix a (idx.1 + 1)).length := by
          rw [hsucc_eq, List.length_append]; exact hhi
        rw [hraw_prefix (idx.1 + 1) (by omega) p hp', hsucc_eq, List.getElem?_append_right hlo]
      exact FO.realize_frameChunkSentence_of_canonical hlt (hb_idx idx) (hdom_idx R idx)
        (hbit_idx R idx) hbase_idx hnext_idx hmap_idx hout_idx
    · -- Outer chunk (`frame (encStructure a)`)
      have hbase_last : ∀ z : Fin B,
          RelMap (v.layoutBase (Fin.last (v.count + 1))) ![z] ↔
            (z : ℕ) = (encStructure a).length := by
        intro z; rw [hbase_char]; simp [baseAt, v.encStructurePrefix_count ha]
      have hnext_outer : ∀ z : Fin B,
          RelMap v.layoutULen ![z] ↔ (z : ℕ) = 0 + (frame (encStructure a)).length := by
        intro z; rw [Nat.zero_add]; exact huLen z
      have hmap_outer : ∀ j p : Fin B,
          RelMap v.layoutOuterMap ![j, p] ↔
            (j : ℕ) ≤ (encStructure a).length ∧ (p : ℕ) = 0 + 2 * (j : ℕ) := by
        intro j p; change ((j : ℕ) ≤ (encStructure a).length ∧ (p : ℕ) = 2 * (j : ℕ)) ↔ _; simp
      have hout_outer : ∀ p : Fin B, 0 ≤ (p : ℕ) → (p : ℕ) < 0 + (frame (encStructure a)).length →
          (RelMap v.layoutUBit ![p] ↔ (frame (encStructure a))[(p : ℕ) - 0]? = some true) := by
        intro p _ hp; rw [Nat.zero_add] at hp; rw [Nat.sub_zero]; exact huBit p hp
      exact FO.realize_frameChunkSentence_of_canonical hlt (by omega) (hdom_outer R hbase_last)
        (fun _ _ => Iff.rfl) hbase0 hnext_outer hmap_outer hout_outer

end Vocabulary

end Cslib.Logic
