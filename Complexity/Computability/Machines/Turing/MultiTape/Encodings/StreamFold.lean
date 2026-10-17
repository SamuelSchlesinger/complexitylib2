/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.StreamFold
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Streaming folds of tidily computable functions

A list encoded as the concatenation of the *tokens* of its elements, each read by a finite-state
input reader, can be folded in one pass over the input. The fold keeps a state, starting with
`init l`; for each element `a` it moves from the state `s` to `next (s, a)` and emits `emit (s, a)`;
at the end it emits `finish` of the final state. Only the state and one element are ever held on
the work tapes.

## Main definitions

* `Turing.MultiTapeTM.streamState`: the state of the fold after the first `j` elements.
* `Turing.MultiTapeTM.streamEmit`: the words the fold emits.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.streamFold_sum`: streaming folds with
  cumulative computation and copying costs, and peak workspace bounds.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.streamFold`: the uniform-round corollary.

The cumulative theorem generalizes Christian Reitwiessner's original encoding-layer proof;
its machine assembly is shared with the uniform-round corollary.
-/

namespace Turing.MultiTapeTM

universe u

variable {α σ : Type*}

/-- The state of a streaming fold after the first `j` elements of `l`. -/
@[expose] public def streamState (init : σ) (next : σ × α → σ) (l : List α) (j : ℕ) : σ :=
  (l.take j).foldl (fun s a => next (s, a)) init

/-- The words emitted by a streaming fold from the state `s` on the list `l`. -/
@[expose] public def streamEmit (next : σ × α → σ) (emit : σ × α → List Bool) :
    σ → List α → List Bool
  | _, [] => []
  | s, a :: l => emit (s, a) ++ streamEmit next emit (next (s, a)) l

@[simp]
public lemma streamState_zero (init : σ) (next : σ × α → σ) (l : List α) :
    streamState init next l 0 = init := rfl

public lemma streamState_succ (init : σ) (next : σ × α → σ) (l : List α) {j : ℕ}
    (hj : j < l.length) :
    streamState init next l (j + 1) = next (streamState init next l j, l[j]) := by
  rw [streamState, List.take_succ_eq_append_getElem hj, List.foldl_append]
  rfl

/-- The emitted words, round by round. -/
public lemma streamEmit_eq (next : σ × α → σ) (emit : σ × α → List Bool) (s : σ) (l : List α) :
    streamEmit next emit s l = ((List.range l.length).map fun j =>
      (l[j]?.map fun a => emit (streamState s next l j, a)).getD []).flatten := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    rw [streamEmit, ih, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.flatten_cons]
    rfl

/-- The lengths of the tokens add up to the length of the input. -/
public lemma sum_length_getD (toks : List (List Bool)) :
    ∑ j ∈ Finset.range toks.length, (toks[j]?.getD []).length = toks.flatten.length := by
  induction toks with
  | nil => rfl
  | cons t toks ih => rw [List.length_cons, Finset.sum_range_succ']; simp [ih, Nat.add_comm]

-- upstream: candidate
-- vendored: generalize the original proof to sum actual round costs; retain the assembly once.
/-- **Streaming folds with cumulative round costs.** The input `x` is encoded by concatenating the
non-empty tokens `tok a` of the elements `elems x`, from each of which the finite-state reader `r`
reads `encA a`. If `init`, `next`, `emit` and `finish` are tidily computable, and `g x` is encoded
by the words emitted by the fold over `elems x` followed by `finish` of its final state, then `g`
is tidily computable. The time bound sums `roundCost`, including each round's computation, current
and next states, decoded element storage and control. Initialization, finalization, input scanning
and cleanup are charged separately. `sMax` and `lMax` bound peak callback workspace and stored
words; output is emitted directly and does not count as workspace. -/
public theorem ComputableTidilyInTimeAndSpace.streamFold_sum {α σ : Type u} {γ ε φ ω : Type*}
    {encA : α ↪ List Bool} {encS : σ ↪ List Bool} {encE : ε ↪ List Bool} {encF : φ ↪ List Bool}
    {encIn : γ ↪ List Bool} {encOut : ω ↪ List Bool} {Q : Type} [Finite Q]
    (r : InputReader Bool Q) (tok : α → List Bool) (htok : ∀ a, tok a ≠ [])
    (hread : ∀ a rest, r.read r.q₀ (tok a ++ rest) = (encA a, (tok a).length))
    (elems : γ → List α) (hL : ∀ x, encIn x = (elems x).flatMap tok)
    {init : γ → σ} {next : σ × α → σ} {emit : σ × α → ε} {finish : σ → φ} {g : γ → ω}
    {tI sI : γ → ℕ} {tN sN tE sE : σ × α → ℕ} {tF sF : σ → ℕ}
    (hinit : ComputableTidilyInTimeAndSpace init encIn encS tI sI)
    (hnext : ComputableTidilyInTimeAndSpace next (encPair encS encA) encS tN sN)
    (hemit : ComputableTidilyInTimeAndSpace emit (encPair encS encA) encE tE sE)
    (hfinish : ComputableTidilyInTimeAndSpace finish encS encF tF sF)
    (hg : ∀ x, encOut (g x) = streamEmit next (fun p => encE (emit p)) (init x) (elems x) ++
      encF (finish (streamState (init x) next (elems x) (elems x).length)))
    {roundCost : γ → ℕ → ℕ} {sMax lMax : γ → ℕ}
    (hcost : ∀ x j (hj : j < (elems x).length),
      tN (streamState (init x) next (elems x) j, (elems x)[j]) +
        tE (streamState (init x) next (elems x) j, (elems x)[j]) +
        (encS (streamState (init x) next (elems x) j)).length +
        (encS (streamState (init x) next (elems x) (j + 1))).length +
        (encA (elems x)[j]).length + 1 ≤ roundCost x j)
    (hsMax : ∀ x j (hj : j < (elems x).length),
      sN (streamState (init x) next (elems x) j, (elems x)[j]) +
        sE (streamState (init x) next (elems x) j, (elems x)[j]) ≤ sMax x)
    (hS : ∀ x, ∀ j ≤ (elems x).length,
      (encS (streamState (init x) next (elems x) j)).length ≤ lMax x)
    (hA : ∀ x j (hj : j < (elems x).length), (encA (elems x)[j]).length ≤ lMax x) :
    ∃ c, ComputableTidilyInTimeAndSpace g encIn encOut
      (fun x => c * (tI x + tF (streamState (init x) next (elems x) (elems x).length) +
        (encIn x).length + (∑ j ∈ Finset.range (elems x).length, roundCost x j) + lMax x + 1))
      (fun x => c * (sI x + sF (streamState (init x) next (elems x) (elems x).length) + sMax x +
        lMax x + 1)) := by
  -- the framed initial state and the framed next state
  obtain ⟨cfr, hfr⟩ := ComputableTidilyInLinearTimeAndSpace.of_frame (f := id) (encIn := encS)
    (encOut := encFramed encS) fun _ => rfl
  -- vendored: crei's `comp` is `comp_linear` here, as cslib #1111 restates `comp`
  obtain ⟨cI, hI'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hfr hinit
  obtain ⟨cN, hN'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hfr hnext
  obtain ⟨cuf, huf⟩ := ComputableTidilyInLinearTimeAndSpace.of_unframe (f := id)
    (encIn := encFramed encS) (encOut := encS) fun s => by simp
  -- vendored: crei's `comp` is `comp_linear` here, as cslib #1111 restates `comp`
  obtain ⟨cF, hF'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hfinish huf
  obtain ⟨kI, SI, _, tmI, htmI⟩ := hI'
  obtain ⟨kE, SE, _, tmE, htmE⟩ := hemit
  obtain ⟨kN, SN, _, tmN, htmN⟩ := hN'
  obtain ⟨kF, SF, _, tmF, htmF⟩ := hF'
  -- the tapes: those of the machines, then the state `V`, the next state `N` and a flag `F`
  obtain ⟨M, hM⟩ : ∃ M, M = kI + kE + kN + kF + 8 := ⟨_, rfl⟩
  let V : Fin (M + 3) := ⟨M, by omega⟩
  let N : Fin (M + 3) := ⟨M + 1, by omega⟩
  let F : Fin (M + 3) := ⟨M + 2, by omega⟩
  have hVN : V ≠ N := by simp [V, N, Fin.ext_iff]
  have hVF : V ≠ F := by simp [V, F, Fin.ext_iff]
  have hNF : N ≠ F := by simp [N, F, Fin.ext_iff]
  obtain ⟨eI, heI⟩ := exists_embedding_eq (K := M + 3) (by omega) (Fin.last kI) V
  obtain ⟨eE, heE⟩ := exists_embedding_eq (K := M + 3) (by omega) (Fin.natAdd kE (0 : Fin 2)) V
  obtain ⟨eN, heN, heN'⟩ := exists_embedding_eq₂ (K := M + 3) (by omega)
    (i := Fin.natAdd (kN + 1) (0 : Fin 2)) (o := (Fin.last kN).castAdd 2)
    (by simp [Fin.ext_iff]) hVN
  obtain ⟨eF, heF⟩ := exists_embedding_eq (K := M + 3) (by omega) (Fin.natAdd kF (0 : Fin 2)) V
  refine ⟨(40 * M + 200) * (cfr + cN + cI + cuf + cF + M + 100), _, _, inferInstance,
    streamTM r ((tmI.outputToWord).extendTapes eI)
    ((tmE.inputFromWord true).extendTapes eE) ((tmN.onWords true).extendTapes eN)
    ((tmF.inputFromWord true).extendTapes eF) V N F hVN hVF hNF, fun x => ?_⟩
  set l := elems x with hl
  -- the run on `l`: its tokens, states, elements and emitted words
  set n := l.length with hn
  let st := streamState (init x) next l
  let toks := l.map tok
  let cont (j : ℕ) : List Bool := (l[j]?.map encA).getD []
  let es (j : ℕ) : List Bool := (l[j]?.map fun a => encE (emit (st j, a))).getD []
  have hcont (j : ℕ) (hj : j < n) : cont j = encA l[j] := by
    simp [cont, List.getElem?_eq_getElem hj]
  have hes (j : ℕ) (hj : j < n) : es j = encE (emit (st j, l[j])) := by
    simp [es, List.getElem?_eq_getElem hj]
  have hx : encIn x = toks.flatten := by rw [hL, List.flatMap_def]
  have htoks : ∀ t ∈ toks, t ≠ [] := by
    intro t ht
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp ht
    exact htok a
  have hlen : toks.length = n := by simp [toks, n]
  have hread' : ∀ j (hj : j < toks.length), r.read r.q₀ (toks.flatten.drop
      ((toks.take j).flatten).length) = (cont j, toks[j].length) := by
    intro j hj
    rw [drop_flatten_take toks hj]
    simp [toks, hcont j (by omega), hread]
  -- the four machines on the common tapes
  have hI := ((htmI x).outputToWord.imp
      (P' := fun inp ws => inp = encIn x ∧ ws = Function.update (fun _ => []) (Fin.last kI) [])
      (Q' := fun _ ws ws' em => ws' = Function.update ws (Fin.last kI)
        (frame (encS (init x))) ∧ em = [])
      (fun _ _ ⟨hin, hws⟩ => ⟨hin, by simp [hws]⟩)
      (fun _ _ _ _ ⟨_, hws⟩ ⟨hws', he⟩ => ⟨by simp [hws', hws], he⟩) le_rfl le_rfl
    ).extendTapes_update eI
  rw [heI] at hI
  have hI₀ := hI.imp (P' := fun inp ws => inp = toks.flatten ∧ ws = fun _ => [])
    (Q' := fun _ _ ws' em => ws' = Function.update (fun _ => []) V (frame (encS (st 0))) ∧ em = [])
    (fun _ _ ⟨hin, hws⟩ => ⟨hin.trans hx.symm, by simp [hws]⟩)
    (fun _ _ _ _ ⟨_, hws⟩ ⟨hws', he⟩ => ⟨by rw [hws', hws]; simp [st], he⟩) le_rfl le_rfl
  have hE : ∀ j < toks.length, TransformsTapes ((tmE.inputFromWord true).extendTapes eE)
      (fun _ ws => ws = Function.update (fun _ => []) V (frame (encS (st j)) ++ cont j))
      (fun _ ws ws' em => ws' = ws ∧ em = es j)
      ((l[j]?.map fun a => tE (st j, a) + 4).getD 0)
      ((l[j]?.map fun a => sE (st j, a) + 2 * ((encPair encS encA (st j, a)).length + 2) +
        2 * kE + 8 + (M + 3 - (kE + 2))).getD 0) := by
    intro j hj
    have hjn : j < n := by omega
    have h := ((htmE (st j, l[j])).inputFromWord true).extendTapes_update eE
    rw [heE] at h
    refine h.imp (fun _ _ hws => ⟨trivial, by rw [hws, hcont j hjn]; rfl⟩)
      (fun _ ws _ _ hws ⟨h, he⟩ => ⟨by rw [h, hws, hcont j hjn, Function.update_idem]; rfl,
        by rw [he, hes j hjn]⟩) ?_ ?_ <;> simp [List.getElem?_eq_getElem hjn]
  have hN : ∀ j < toks.length, TransformsTapes ((tmN.onWords true).extendTapes eN)
      (fun _ ws => ws = Function.update (fun _ => []) V (frame (encS (st j)) ++ cont j))
      (fun _ ws ws' em => ws' = Function.update ws N (frame (encS (st (j + 1)))) ∧ em = [])
      ((l[j]?.map fun a => tN (st j, a) + cfr * ((encS (next (st j, a))).length + 1) +
        cN * ((encS (next (st j, a))).length + 1) + (frame (encS (next (st j, a)))).length +
        6).getD 0)
      ((l[j]?.map fun a => sN (st j, a) + cfr * ((encS (next (st j, a))).length + 1) +
        cN * ((encS (next (st j, a))).length + 1) + 2 * (encPair encS encA (st j, a)).length +
        2 * (frame (encS (next (st j, a)))).length + 3 * kN + 18 +
        (M + 3 - (kN + 1 + 2))).getD 0) := by
    intro j hj
    have hjn : j < n := by omega
    have h := (((htmN (st j, l[j])).onWords true).imp
      (P' := fun _ ws => True ∧ ws = Function.update (fun _ => []) (Fin.natAdd (kN + 1) 0)
        (encPair encS encA (st j, l[j])))
      (fun _ _ h => h.2) (fun _ _ _ _ _ h => h) le_rfl le_rfl).extendTapes_update eN
    rw [heN, heN'] at h
    refine h.imp (fun _ _ hws => ⟨trivial, by rw [hws, hcont j hjn]; rfl⟩)
      (fun _ _ _ _ _ ⟨h, he⟩ => ⟨by rw [h]; simp only [st, streamState_succ _ _ _ hjn]; rfl, he⟩)
      ?_ ?_ <;> simp [List.getElem?_eq_getElem hjn]
  have hF := (((htmF (st toks.length)).inputFromWord true).extendTapes_update eF)
  rw [heF] at hF
  have hF₀ := hF.imp (P' := fun _ ws => ws = Function.update (fun _ => []) V
      (frame (encS (st toks.length))))
    (Q' := fun _ ws ws' em => ws' = ws ∧ em = encF (finish (st toks.length)))
    (fun _ _ hws => ⟨trivial, hws⟩)
    (fun _ _ _ _ hws ⟨h, he⟩ => ⟨by rw [h, hws, Function.update_idem]; rfl, he⟩) le_rfl le_rfl
  -- the space of a round, bounded by the largest one
  let sRound (j : ℕ) : ℕ := (frame (encS (st j)) ++ cont j).length + 2 + (M + 3 - 1) +
    (((l[j]?.map fun a => sE (st j, a) + 2 * ((encPair encS encA (st j, a)).length + 2) +
        2 * kE + 8 + (M + 3 - (kE + 2))).getD 0) +
      (((l[j]?.map fun a => sN (st j, a) + cfr * ((encS (next (st j, a))).length + 1) +
        cN * ((encS (next (st j, a))).length + 1) + 2 * (encPair encS encA (st j, a)).length +
        2 * (frame (encS (next (st j, a)))).length + 3 * kN + 18 +
        (M + 3 - (kN + 1 + 2))).getD 0) +
      (((frame (encS (st j)) ++ cont j).length + 1 + (M + 3)) +
        ((4 * (frame (encS (st (j + 1)))).length + (M + 3) + 15) +
          ((frame (encS (st (j + 1)))).length + 1 + (M + 3))))))
  have h := computesTidily_streamTM (r := r) hVN hVF hNF toks htoks cont
    (fun j => frame (encS (st j))) es (encF (finish (st toks.length))) hread' hI₀ hE hN hF₀
    (sR := (Finset.range toks.length).sup sRound)
    (fun j hj => Finset.le_sup (f := sRound) (Finset.mem_range.mpr hj))
  simp only [streamRoundTime] at h
  rw [← hx, hlen] at h
  rw [hg x, streamEmit_eq]
  -- bounds on the words involved
  set L := lMax x with hLdef
  have hSj (j : ℕ) (hj : j ≤ n) : (encS (st j)).length ≤ L := hS x j hj
  have hround (j : ℕ) (hj : j < n) :
      (frame (encS (st j))).length + 1 +
          ((toks[j]?.getD []).length + 1 + ((frame (encS (st j)) ++ cont j).length + 2)) +
        ((Option.map (fun a => tE (st j, a) + 4) l[j]?).getD 0 +
          ((Option.map (fun a => tN (st j, a) + cfr * ((encS (next (st j, a))).length + 1) +
            cN * ((encS (next (st j, a))).length + 1) + (frame (encS (next (st j, a)))).length + 6)
              l[j]?).getD 0 +
            (3 * ((frame (encS (st j)) ++ cont j).length + 1) +
              (3 * (frame (encS (st (j + 1)))).length + 10 +
                3 * ((frame (encS (st (j + 1)))).length + 1))))) + 1 ≤
      (toks[j]?.getD []).length + (cfr + cN + 60) * roundCost x j := by
    have ht := hcost x j hj
    have hnext : next (st j, l[j]) = st (j + 1) := (streamState_succ _ _ _ hj).symm
    have hsize : (encS (st (j + 1))).length + 1 ≤ roundCost x j := by lia
    have hm₁ := Nat.mul_le_mul_left cfr hsize
    have hm₂ := Nat.mul_le_mul_left cN hsize
    simp only [List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some, hnext,
      hcont j hj, length_frame, List.length_append]
    linarith only [ht, hm₁, hm₂]
  have hS0 : (encS (init x)).length ≤ L := hSj 0 (Nat.zero_le _)
  have hSn : (encS (st n)).length ≤ L := hSj n le_rfl
  set D := cfr + cN + cI + cuf + cF + M + 100 with hD
  have hsum := (Finset.sum_le_sum fun j hj => hround j (Finset.mem_range.mp hj)).trans_eq
    (by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hlen, sum_length_getD, ← hx])
  refine h.mono ?_ ?_
  · simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame, st] at hsum hSn ⊢
    rw [← hn, ← hLdef]
    rw [hlen] at hsum
    clear_value D L
    have hD1 : 1 ≤ D := by omega
    have f₁ := Nat.mul_le_mul (show cfr + cI ≤ D by omega) (Nat.add_le_add_right hS0 1)
    have f₂ := Nat.mul_le_mul (show cuf ≤ D by omega)
      (show 2 * (encS (streamState (init x) next l n)).length + 1 + 1 ≤ 2 * (L + 1) by omega)
    have f₃ := Nat.mul_le_mul (show cF ≤ D by omega) (Nat.add_le_add_right hSn 1)
    have f₄ := Nat.mul_le_mul_right (∑ j ∈ Finset.range n, roundCost x j)
      (show cfr + cN + 60 ≤ D by lia)
    have f₅ := Nat.mul_le_mul_right (tI x + tF (streamState (init x) next l n) + (encIn x).length +
      (∑ j ∈ Finset.range n, roundCost x j) + L + 1)
      (show 26 * D ≤ (40 * M + 200) * D from Nat.mul_le_mul_right _ (by omega))
    have f₆ := Nat.le_mul_of_pos_left (tI x) hD1
    have f₇ := Nat.le_mul_of_pos_left (tF (streamState (init x) next l n)) hD1
    have f₈ := Nat.le_mul_of_pos_left (encIn x).length hD1
    have f₉ := Nat.mul_le_mul_right (L + 1) (show 20 ≤ D by omega)
    refine le_trans
      (Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_right hsum 1) _) _) ?_
    have z₁ := Nat.zero_le (D * L)
    have z₂ := Nat.zero_le (D * ∑ j ∈ Finset.range n, roundCost x j)
    ring_nf at f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ z₁ ⊢
    linarith
  · simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame, st] at hSn ⊢
    rw [← hn, ← hLdef]
    -- the space of a round
    have hsup : (Finset.range n).sup sRound ≤ sMax x + (cfr + cN + 20 * M + 100) * (L + 1) := by
      refine Finset.sup_le fun j hj => ?_
      have hj := Finset.mem_range.mp hj
      have h₀ := hSj j hj.le
      have h₁ := hSj (j + 1) hj
      have hA' := hA x j hj
      have hs := hsMax x j hj
      have hnext : next (st j, l[j]) = st (j + 1) := (streamState_succ _ _ _ hj).symm
      have hm₁ := Nat.mul_le_mul_left cfr (Nat.add_le_add_right h₁ 1)
      have hm₂ := Nat.mul_le_mul_left cN (Nat.add_le_add_right h₁ 1)
      simp only [sRound, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some, hnext,
        hcont j hj, length_frame, List.length_append, encPair_apply]
      have : kE ≤ M := by omega
      have : kN ≤ M := by omega
      have : M + 3 - 1 = M + 2 := by omega
      have : M + 3 - (kE + 2) ≤ M + 1 := by omega
      have : M + 3 - (kN + 1 + 2) ≤ M := by omega
      have := Nat.zero_le (M * L)
      linarith
    clear_value D L
    have hD1 : 1 ≤ D := by omega
    have hED : cfr + cN + 20 * M + 100 ≤ 20 * D := by omega
    have g₁ := Nat.mul_le_mul_left (2 * (M + 3)) hsup
    have g₂ : 2 * (M + 3) * ((cfr + cN + 20 * M + 100) * (L + 1)) ≤
        (40 * M + 120) * (D * (L + 1)) :=
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hED)).trans_eq (by ring)
    have g₃ : 2 * (M + 3) * sMax x ≤ (40 * M + 200) * D * sMax x :=
      Nat.mul_le_mul_right _ ((show 2 * (M + 3) ≤ 40 * M + 200 by omega).trans
        (Nat.le_mul_of_pos_right _ hD1))
    have g₄ : sI x ≤ (40 * M + 200) * D * sI x :=
      Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) hD1)
    have g₅ : sF (streamState (init x) next l n) ≤
        (40 * M + 200) * D * sF (streamState (init x) next l n) :=
      Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) hD1)
    have g₆ := Nat.mul_le_mul (show cfr + cI ≤ D by omega) (Nat.add_le_add_right hS0 1)
    have g₇ := Nat.mul_le_mul (show cuf ≤ D by omega)
      (show 2 * (encS (streamState (init x) next l n)).length + 1 + 1 ≤ 2 * (L + 1) by omega)
    have g₈ := Nat.mul_le_mul (show cF ≤ D by omega) (Nat.add_le_add_right hSn 1)
    have q₂ : L + 1 ≤ D * (L + 1) := Nat.le_mul_of_pos_left _ hD1
    have : kI ≤ M := by omega
    have : kF ≤ M := by omega
    have : M ≤ D := by omega
    have hd₁ : M + 3 - (kI + 1) ≤ M + 2 := by omega
    have hd₂ : M + 3 - (kF + 2) ≤ M + 1 := by omega
    generalize M + 3 - (kI + 1) = d₁ at hd₁ ⊢
    generalize M + 3 - (kF + 2) = d₂ at hd₂ ⊢
    have z₁ := Nat.zero_le (D * L)
    generalize (Finset.range n).sup sRound = sup at g₁ ⊢
    ring_nf at g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ q₂ z₁ ⊢
    linarith


-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: derived from `streamFold_sum` to share the machine and resource proof.
/-- **Streaming folds are tidily computable.** The input `x` is encoded by concatenating the non-
empty tokens `tok a` of the elements `elems x`, from each of which the finite-state reader `r`
reads `encA a`. If `init`, `next`, `emit` and `finish` are tidily computable, and `g x` is encoded
by the words emitted by the fold over `elems x` followed by `finish` of its final state, then `g`
is tidily computable. Its time is linear in the input plus the rounds. Workspace uses peak bounds
on states, elements and callbacks. The bounds `tMax`, `sMax` and `lMax` bound the time and space
of a round and the lengths of the states and elements. -/
public theorem ComputableTidilyInTimeAndSpace.streamFold {α σ : Type u} {γ ε φ ω : Type*}
    {encA : α ↪ List Bool} {encS : σ ↪ List Bool} {encE : ε ↪ List Bool} {encF : φ ↪ List Bool}
    {encIn : γ ↪ List Bool} {encOut : ω ↪ List Bool} {Q : Type} [Finite Q]
    (r : InputReader Bool Q) (tok : α → List Bool) (htok : ∀ a, tok a ≠ [])
    (hread : ∀ a rest, r.read r.q₀ (tok a ++ rest) = (encA a, (tok a).length))
    (elems : γ → List α) (hL : ∀ x, encIn x = (elems x).flatMap tok)
    {init : γ → σ} {next : σ × α → σ} {emit : σ × α → ε} {finish : σ → φ} {g : γ → ω}
    {tI sI : γ → ℕ} {tN sN tE sE : σ × α → ℕ} {tF sF : σ → ℕ}
    (hinit : ComputableTidilyInTimeAndSpace init encIn encS tI sI)
    (hnext : ComputableTidilyInTimeAndSpace next (encPair encS encA) encS tN sN)
    (hemit : ComputableTidilyInTimeAndSpace emit (encPair encS encA) encE tE sE)
    (hfinish : ComputableTidilyInTimeAndSpace finish encS encF tF sF)
    (hg : ∀ x, encOut (g x) = streamEmit next (fun p => encE (emit p)) (init x) (elems x) ++
      encF (finish (streamState (init x) next (elems x) (elems x).length)))
    {tMax sMax lMax : γ → ℕ}
    (htMax : ∀ x j (hj : j < (elems x).length),
      tN (streamState (init x) next (elems x) j, (elems x)[j]) +
        tE (streamState (init x) next (elems x) j, (elems x)[j]) ≤ tMax x)
    (hsMax : ∀ x j (hj : j < (elems x).length),
      sN (streamState (init x) next (elems x) j, (elems x)[j]) +
        sE (streamState (init x) next (elems x) j, (elems x)[j]) ≤ sMax x)
    (hS : ∀ x, ∀ j ≤ (elems x).length,
      (encS (streamState (init x) next (elems x) j)).length ≤ lMax x)
    (hA : ∀ x j (hj : j < (elems x).length), (encA (elems x)[j]).length ≤ lMax x) :
    ∃ c, ComputableTidilyInTimeAndSpace g encIn encOut
      (fun x => c * (tI x + tF (streamState (init x) next (elems x) (elems x).length) +
        (encIn x).length + (elems x).length * (tMax x + lMax x + 1) + lMax x + 1))
      (fun x => c * (sI x + sF (streamState (init x) next (elems x) (elems x).length) + sMax x +
        lMax x + 1)) := by
  obtain ⟨c, h⟩ := streamFold_sum r tok htok hread elems hL hinit hnext hemit hfinish hg
    (roundCost := fun x _ => tMax x + 3 * lMax x + 1) (sMax := sMax) (lMax := lMax)
    (fun x j hj => by
      have ht := htMax x j hj
      have h₀ := hS x j hj.le
      have h₁ := hS x (j + 1) hj
      have ha := hA x j hj
      lia) hsMax hS hA
  refine ⟨c * 3, h.mono (fun x => ?_) (fun x => ?_)⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    lia

end Turing.MultiTapeTM
