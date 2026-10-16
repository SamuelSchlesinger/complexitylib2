/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.MultiPass
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Multi-pass folds of tidily computable functions

A multi-pass fold reads a list, encoded as the concatenation of the tokens of its elements, several
times. Each pass folds `next` over the elements, emitting `emit` for each of them, then emits
`passEmit` of the resulting state and moves on to `passEnd` of it. The passes stop once `cont` of
the state is false, and the fold ends by emitting `finish` of the final state. Only the state and
one element are ever held on the work tapes, so the space does not grow with the input.

## Main definitions

* `Turing.MultiTapeTM.passState`: the state at the start of a pass.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.multiPassFold`: multi-pass folds are tidily
  computable, in time linear in the input plus the rounds for each pass, and in space independent
  of the input.
-/

namespace Turing.MultiTapeTM

universe u

variable {α σ : Type*}

/-- The state at the start of pass `i` of a multi-pass fold over `l`: a pass folds `next` over `l`
and then applies `passEnd`. -/
@[expose] public def passState (init : σ) (next : σ × α → σ) (passEnd : σ → σ) (l : List α) :
    ℕ → σ
  | 0 => init
  | i + 1 => passEnd (streamState (passState init next passEnd l i) next l l.length)

/-- The flag after a pass: `[true]` if another pass follows, blank otherwise. -/
@[expose] public def flagWord (b : Bool) : List Bool := if b then [true] else []

open ComputableTidilyInLinearTimeAndSpace in
lemma linear_flagWord : ComputableTidilyInLinearTimeAndSpace flagWord encBool encBits := by
  convert (of_eq (f := id) (encIn := encBool) (encMid := encBool) fun _ => rfl).ite
    ((const [true]).restrict _) ((const []).restrict _) using 1
  funext c
  cases c <;> rfl

/-! ### Tidy machines on selected tapes -/

section Tapes

variable {β δ : Type*} {k K : ℕ} {S : Type*} {tm : MultiTapeTM k Bool S} {encB : β ↪ List Bool}
  {encD : δ ↪ List Bool} {f : β → δ} {t s : β → ℕ}

/-- A tidy machine writing its output to tape `V`. -/
lemma transformsTapes_outputToWord (h : ComputesFunTidilyInTimeAndSpace tm encB encD f t s)
    {e : Fin (k + 1) ↪ Fin K} {V : Fin K} (he : e (Fin.last k) = V) (b : β) :
    TransformsTapes (tm.outputToWord.extendTapes e) (fun inp ws => inp = encB b ∧ ws = fun _ => [])
      (fun _ _ ws' em => ws' = Function.update (fun _ => []) V (encD (f b)) ∧ em = [])
      (t b + (encD (f b)).length + 2) (s b + 2 * (encD (f b)).length + 2 * K + 3) := by
  have hk : k + 1 ≤ K := by simpa using Fintype.card_le_of_embedding e
  have h' := ((h b).outputToWord.imp
      (P' := fun inp ws => inp = encB b ∧ ws = Function.update (fun _ => []) (Fin.last k) [])
      (Q' := fun _ ws ws' em => ws' = Function.update ws (Fin.last k) (encD (f b)) ∧ em = [])
      (fun _ _ ⟨hin, hws⟩ => ⟨hin, by simp [hws]⟩)
      (fun _ _ _ _ ⟨_, hws⟩ ⟨hws', he⟩ => ⟨by simp [hws', hws], he⟩) le_rfl le_rfl
    ).extendTapes_update e
  rw [he] at h'
  exact h'.imp (fun _ _ ⟨hin, hws⟩ => ⟨hin, by simp [hws]⟩)
    (fun _ _ _ _ ⟨_, hws⟩ ⟨hws', he⟩ => ⟨by simp [hws', hws], he⟩) le_rfl (by omega)

-- vendored: `transformsTapes_inputFromWord` in crei:crei/tidy-universal, a name that cslib #1111
-- gives to a public lemma of `Plumbing/InputFromTape`
/-- A tidy machine run on the word on tape `V`, emitting its output. -/
lemma transformsTapes_inputFromWord_tape (h : ComputesFunTidilyInTimeAndSpace tm encB encD f t s)
    {e : Fin (k + 2) ↪ Fin K} {V : Fin K} (he : e (Fin.natAdd k 0) = V) (b : β) :
    TransformsTapes ((tm.inputFromWord true).extendTapes e)
      (fun _ ws => ws = Function.update (fun _ => []) V (encB b))
      (fun _ ws ws' em => ws' = ws ∧ em = encD (f b))
      (t b + 4) (s b + 2 * (encB b).length + 3 * K + 10) := by
  have hk : k + 2 ≤ K := by simpa using Fintype.card_le_of_embedding e
  have h' := ((h b).inputFromWord true).extendTapes_update e
  rw [he] at h'
  exact h'.imp (fun _ _ hws => ⟨trivial, hws⟩)
    (fun _ _ _ _ hws ⟨h, he⟩ => ⟨by rw [h, hws, Function.update_idem], he⟩) le_rfl (by omega)

/-- A tidy machine run on the word on tape `V`, writing its output to tape `O`. -/
lemma transformsTapes_onWords (h : ComputesFunTidilyInTimeAndSpace tm encB encD f t s)
    {e : Fin (k + 1 + 2) ↪ Fin K} {V O : Fin K} (hi : e (Fin.natAdd (k + 1) 0) = V)
    (ho : e ((Fin.last k).castAdd 2) = O) (b : β) :
    TransformsTapes ((tm.onWords true).extendTapes e)
      (fun _ ws => ws = Function.update (fun _ => []) V (encB b))
      (fun _ ws ws' em => ws' = Function.update ws O (encD (f b)) ∧ em = [])
      (t b + (encD (f b)).length + 6)
      (s b + 2 * (encB b).length + 2 * (encD (f b)).length + 4 * K + 15) := by
  have hk : k + 1 + 2 ≤ K := by simpa using Fintype.card_le_of_embedding e
  have h' := (((h b).onWords true).imp
    (P' := fun _ ws => True ∧ ws = Function.update (fun _ => []) (Fin.natAdd (k + 1) 0) (encB b))
    (fun _ _ h => h.2) (fun _ _ _ _ _ h => h) le_rfl le_rfl).extendTapes_update e
  rw [hi, ho] at h'
  exact h'.imp (fun _ _ hws => ⟨trivial, hws⟩) (fun _ _ _ _ _ h => h) le_rfl (by omega)

end Tapes

/-- **Multi-pass folds are tidily computable.** The input `x` is encoded by concatenating the
non-empty tokens `tok a` of the elements `elems x`, from each of which the finite-state reader `r`
reads `encA a`. Pass `i` starts from `passState … i`; the fold makes `passes x + 1` passes, which
`cont` signals after each of them. If all the parts are tidily computable and `g x` is encoded by
what the passes emit followed by `finish` of the final state, then `g` is tidily computable. Its
time is that of a streaming fold for every pass; its space does not grow with the input. The
bounds `tMax`, `sMax` and `lMax` bound the time and space of a round and of the end of a pass, and
the lengths of the states and elements. -/
public theorem ComputableTidilyInTimeAndSpace.multiPassFold {α σ : Type u} {γ ε ε' φ ω : Type*}
    {encA : α ↪ List Bool} {encS : σ ↪ List Bool} {encE : ε ↪ List Bool}
    {encE' : ε' ↪ List Bool} {encF : φ ↪ List Bool} {encIn : γ ↪ List Bool}
    {encOut : ω ↪ List Bool} {Q : Type} [Finite Q]
    (r : InputReader Bool Q) (tok : α → List Bool) (htok : ∀ a, tok a ≠ [])
    (hread : ∀ a rest, r.read r.q₀ (tok a ++ rest) = (encA a, (tok a).length))
    (elems : γ → List α) (hL : ∀ x, encIn x = (elems x).flatMap tok)
    {init : γ → σ} {next : σ × α → σ} {emit : σ × α → ε} {passEmit : σ → ε'}
    {passEnd : σ → σ} {cont : σ → Bool} {finish : σ → φ} {g : γ → ω} {passes : γ → ℕ}
    {tI sI : γ → ℕ} {tN sN tE sE : σ × α → ℕ} {tPE sPE tPN sPN tC sC tF sF : σ → ℕ}
    (hinit : ComputableTidilyInTimeAndSpace init encIn encS tI sI)
    (hnext : ComputableTidilyInTimeAndSpace next (encPair encS encA) encS tN sN)
    (hemit : ComputableTidilyInTimeAndSpace emit (encPair encS encA) encE tE sE)
    (hpassEmit : ComputableTidilyInTimeAndSpace passEmit encS encE' tPE sPE)
    (hpassEnd : ComputableTidilyInTimeAndSpace passEnd encS encS tPN sPN)
    (hcont : ComputableTidilyInTimeAndSpace cont encS encBool tC sC)
    (hfinish : ComputableTidilyInTimeAndSpace finish encS encF tF sF)
    (hpasses : ∀ x, ∀ i ≤ passes x,
      cont (passState (init x) next passEnd (elems x) (i + 1)) = decide (i < passes x))
    (hg : ∀ x, encOut (g x) = ((List.range (passes x + 1)).map fun i =>
      streamEmit next (fun p => encE (emit p)) (passState (init x) next passEnd (elems x) i)
        (elems x) ++ encE' (passEmit (streamState (passState (init x) next passEnd (elems x) i)
          next (elems x) (elems x).length))).flatten ++
      encF (finish (passState (init x) next passEnd (elems x) (passes x + 1))))
    {tMax sMax lMax : γ → ℕ}
    (htMax : ∀ x, ∀ i ≤ passes x, ∀ j (hj : j < (elems x).length),
      tN (streamState (passState (init x) next passEnd (elems x) i) next (elems x) j,
          (elems x)[j]) +
        tE (streamState (passState (init x) next passEnd (elems x) i) next (elems x) j,
          (elems x)[j]) ≤ tMax x)
    (hsMax : ∀ x, ∀ i ≤ passes x, ∀ j (hj : j < (elems x).length),
      sN (streamState (passState (init x) next passEnd (elems x) i) next (elems x) j,
          (elems x)[j]) +
        sE (streamState (passState (init x) next passEnd (elems x) i) next (elems x) j,
          (elems x)[j]) ≤ sMax x)
    (htEnd : ∀ x, ∀ i ≤ passes x,
      tPE (streamState (passState (init x) next passEnd (elems x) i) next (elems x)
          (elems x).length) +
        tPN (streamState (passState (init x) next passEnd (elems x) i) next (elems x)
          (elems x).length) +
        tC (passState (init x) next passEnd (elems x) (i + 1)) ≤ tMax x)
    (hsEnd : ∀ x, ∀ i ≤ passes x,
      sPE (streamState (passState (init x) next passEnd (elems x) i) next (elems x)
          (elems x).length) +
        sPN (streamState (passState (init x) next passEnd (elems x) i) next (elems x)
          (elems x).length) +
        sC (passState (init x) next passEnd (elems x) (i + 1)) ≤ sMax x)
    (hS : ∀ x, ∀ i ≤ passes x, ∀ j ≤ (elems x).length,
      (encS (streamState (passState (init x) next passEnd (elems x) i) next (elems x) j)).length ≤
        lMax x)
    (hSlast : ∀ x,
      (encS (passState (init x) next passEnd (elems x) (passes x + 1))).length ≤ lMax x)
    (hA : ∀ x j (hj : j < (elems x).length), (encA (elems x)[j]).length ≤ lMax x) :
    ∃ c, ComputableTidilyInTimeAndSpace g encIn encOut
      (fun x => c * (tI x + tF (passState (init x) next passEnd (elems x) (passes x + 1)) +
        (passes x + 1) * ((encIn x).length + ((elems x).length + 1) * (tMax x + lMax x + 1))))
      (fun x => c * (sI x + sF (passState (init x) next passEnd (elems x) (passes x + 1)) +
        sMax x + lMax x + 1)) := by
  -- the parts, on framed states
  obtain ⟨cfr, hfr⟩ := ComputableTidilyInLinearTimeAndSpace.of_frame (f := id) (encIn := encS)
    (encOut := encFramed encS) fun _ => rfl
  obtain ⟨cuf, huf⟩ := ComputableTidilyInLinearTimeAndSpace.of_unframe (f := id)
    (encIn := encFramed encS) (encOut := encS) fun s => by simp
  obtain ⟨cfl, hfl⟩ := linear_flagWord
  -- vendored: crei's `comp` is `comp_linear` here, as cslib #1111 restates `comp`
  obtain ⟨cI, hI'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hfr hinit
  obtain ⟨cN, hN'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hfr hnext
  obtain ⟨cF, hF'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hfinish huf
  obtain ⟨cPE, hPE'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hpassEmit huf
  obtain ⟨cPN₁, hPN₁⟩ := ComputableTidilyInTimeAndSpace.comp_linear hpassEnd huf
  obtain ⟨cPN, hPN'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hfr hPN₁
  obtain ⟨cC₁, hC₁⟩ := ComputableTidilyInTimeAndSpace.comp_linear hcont huf
  obtain ⟨cC, hC'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hfl hC₁
  obtain ⟨kI, SI, _, tmI, htmI⟩ := hI'
  obtain ⟨kE, SE, _, tmE, htmE⟩ := hemit
  obtain ⟨kN, SN, _, tmN, htmN⟩ := hN'
  obtain ⟨kF, SF, _, tmF, htmF⟩ := hF'
  obtain ⟨kPE, SPE, _, tmPE, htmPE⟩ := hPE'
  obtain ⟨kPN, SPN, _, tmPN, htmPN⟩ := hPN'
  obtain ⟨kC, SC, _, tmC, htmC⟩ := hC'
  -- the tapes: those of the machines, then the state `V`, the next state `N`, a flag `F` for
  -- copying and the flag `C` for another pass
  obtain ⟨M, hM⟩ : ∃ M, M = kI + kE + kN + kF + kPE + kPN + kC + 8 := ⟨_, rfl⟩
  let V : Fin (M + 4) := ⟨M, by omega⟩
  let N : Fin (M + 4) := ⟨M + 1, by omega⟩
  let F : Fin (M + 4) := ⟨M + 2, by omega⟩
  let C : Fin (M + 4) := ⟨M + 3, by omega⟩
  have hVN : V ≠ N := by simp [V, N, Fin.ext_iff]
  have hVF : V ≠ F := by simp [V, F, Fin.ext_iff]
  have hNF : N ≠ F := by simp [N, F, Fin.ext_iff]
  have hVC : V ≠ C := by simp [V, C, Fin.ext_iff]
  obtain ⟨eI, heI⟩ := exists_embedding_eq (K := M + 4) (by omega) (Fin.last kI) V
  obtain ⟨eE, heE⟩ := exists_embedding_eq (K := M + 4) (by omega) (Fin.natAdd kE (0 : Fin 2)) V
  obtain ⟨eN, heN, heN'⟩ := exists_embedding_eq₂ (K := M + 4) (by omega)
    (i := Fin.natAdd (kN + 1) (0 : Fin 2)) (o := (Fin.last kN).castAdd 2)
    (by simp [Fin.ext_iff]) hVN
  obtain ⟨eF, heF⟩ := exists_embedding_eq (K := M + 4) (by omega) (Fin.natAdd kF (0 : Fin 2)) V
  obtain ⟨ePE, hePE⟩ := exists_embedding_eq (K := M + 4) (by omega)
    (Fin.natAdd kPE (0 : Fin 2)) V
  obtain ⟨ePN, hePN, hePN'⟩ := exists_embedding_eq₂ (K := M + 4) (by omega)
    (i := Fin.natAdd (kPN + 1) (0 : Fin 2)) (o := (Fin.last kPN).castAdd 2)
    (by simp [Fin.ext_iff]) hVN
  obtain ⟨eC, heC, heC'⟩ := exists_embedding_eq₂ (K := M + 4) (by omega)
    (i := Fin.natAdd (kC + 1) (0 : Fin 2)) (o := (Fin.last kC).castAdd 2)
    (by simp [Fin.ext_iff]) hVC
  -- the machines on the common tapes
  have hI := transformsTapes_outputToWord htmI heI
  have hE := transformsTapes_inputFromWord_tape htmE heE
  have hN := transformsTapes_onWords htmN heN heN'
  have hF := transformsTapes_inputFromWord_tape htmF heF
  have hPE := transformsTapes_inputFromWord_tape htmPE hePE
  have hPN := transformsTapes_onWords htmPN hePN hePN'
  have hC := transformsTapes_onWords (encD := encBits) htmC heC heC'
  set D := cfr + cuf + cfl + cI + cN + cF + cPE + cPN₁ + cPN + cC₁ + cC + M + 100 with hD
  -- the state type nests the states of eight machines, beyond the default instance size limit
  refine ⟨2000 * (D * D * D), _, _, by set_option synthInstance.maxSize 1024 in infer_instance,
    multiPassTM (tmI.outputToWord.extendTapes eI)
      (passTM r ((tmE.inputFromWord true).extendTapes eE) ((tmN.onWords true).extendTapes eN)
        ((tmPE.inputFromWord true).extendTapes ePE) ((tmPN.onWords true).extendTapes ePN)
        ((tmC.onWords true).extendTapes eC) V N F C hVN hVF hNF)
      ((tmF.inputFromWord true).extendTapes eF) V C, fun x => ?_⟩
  set l := elems x with hl
  set n := l.length with hn
  set ps : ℕ → σ := passState (init x) next passEnd l with hps
  let ms (i j : ℕ) : σ := streamState (ps i) next l j
  let toks := l.map tok
  let cont' (j : ℕ) : List Bool := (l[j]?.map encA).getD []
  have hcont (j : ℕ) (hj : j < n) : cont' j = encA l[j] := by
    simp [cont', List.getElem?_eq_getElem hj]
  have hx : encIn x = toks.flatten := by rw [hL, List.flatMap_def]
  have htoks : ∀ t ∈ toks, t ≠ [] := by
    intro t ht
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp ht
    exact htok a
  have hlen : toks.length = n := by simp [toks, n]
  have hread' : ∀ j (hj : j < toks.length), r.read r.q₀ (toks.flatten.drop
      ((toks.take j).flatten).length) = (cont' j, toks[j].length) := by
    intro j hj
    rw [drop_flatten_take toks hj]
    simp [toks, hcont j (by omega), hread]
  -- uniform bounds on the parts
  set L := lMax x with hLdef
  set T := tMax x with hTdef
  set Sm := sMax x with hSdef
  have hKD : M + 4 ≤ D := by omega
  have hLD : 100 * (L + 1) ≤ D * (L + 1) := Nat.mul_le_mul_right _ (by omega)
  have hc2 : ∀ c ≤ D, ∀ a ≤ 1, c * (a + 1) ≤ 2 * (D * (L + 1)) := fun c hc a ha =>
    (Nat.mul_le_mul hc (show a + 1 ≤ 2 * (L + 1) by omega)).trans_eq (by ring)
  have hmul : ∀ c ≤ D, ∀ a ≤ L, c * (a + 1) ≤ D * (L + 1) :=
    fun c hc a ha => Nat.mul_le_mul hc (by omega)
  have hmul₂ : ∀ c ≤ D, ∀ a ≤ L, c * (2 * a + 1 + 1) ≤ 2 * (D * (L + 1)) :=
    fun c hc a ha => (Nat.mul_le_mul hc (show 2 * a + 1 + 1 ≤ 2 * (L + 1) by omega)).trans_eq
      (by ring)
  have hmsS (i : ℕ) (hi : i ≤ passes x) (j : ℕ) (hj : j ≤ n) : (encS (ms i j)).length ≤ L :=
    hS x i hi j hj
  have hpsS (i : ℕ) (hi : i ≤ passes x + 1) : (encS (ps i)).length ≤ L := by
    rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · exact hmsS i (by omega) 0 (Nat.zero_le _)
    · exact hSlast x
  have hnextS (i : ℕ) (hi : i ≤ passes x) (j : ℕ) (hj : j < n) :
      next (ms i j, l[j]) = ms i (j + 1) := (streamState_succ _ _ _ hj).symm
  have hendS (i : ℕ) : passEnd (ms i n) = ps (i + 1) := rfl
  -- the passes
  let es (i j : ℕ) : List Bool := (l[j]?.map fun a => encE (emit (ms i j, a))).getD []
  let cs (i : ℕ) : List Bool := if i = 0 then [] else flagWord (cont (ps i))
  let R := 3 * T + 60 * (D * (L + 1))
  let tP := 2 * (encIn x).length + (n + 1) * R + 100
  let sR := 2 * Sm + 6 * (D * (L + 1)) + 30 * L + 20 * (M + 4) + 100
  let sP := 2 * (M + 4) * sR + 3 * Sm + 60 * (D * (L + 1)) + 20 * (M + 4) + 100
  have hpass : ∀ i ≤ passes x, TransformsTapes (passTM r ((tmE.inputFromWord true).extendTapes eE)
      ((tmN.onWords true).extendTapes eN) ((tmPE.inputFromWord true).extendTapes ePE)
      ((tmPN.onWords true).extendTapes ePN) ((tmC.onWords true).extendTapes eC) V N F C hVN hVF hNF)
      (fun inp ws => inp = encIn x ∧ ws = passTapes V C (frame (encS (ps i))) (cs i))
      (fun _ _ ws' em => ws' = passTapes V C (frame (encS (ps (i + 1)))) (cs (i + 1)) ∧
        em = ((List.range n).map (es i)).flatten ++ encE' (passEmit (ms i n))) tP sP := by
    intro i hi
    have hT (j : ℕ) (hj : j < n) : tN (ms i j, l[j]) + tE (ms i j, l[j]) ≤ T := htMax x i hi j hj
    have hSm (j : ℕ) (hj : j < n) : sN (ms i j, l[j]) + sE (ms i j, l[j]) ≤ Sm :=
      hsMax x i hi j hj
    have hTe : tPE (ms i n) + tPN (ms i n) + tC (ps (i + 1)) ≤ T := htEnd x i hi
    have hSe : sPE (ms i n) + sPN (ms i n) + sC (ps (i + 1)) ≤ Sm := hsEnd x i hi
    have hAj (j : ℕ) (hj : j < n) : (encA l[j]).length ≤ L := hA x j hj
    have hE' : ∀ j < toks.length, TransformsTapes ((tmE.inputFromWord true).extendTapes eE)
        (fun _ ws => ws = Function.update (fun _ => []) V (frame (encS (ms i j)) ++ cont' j))
        (fun _ ws ws' em => ws' = ws ∧ em = es i j) (T + 4)
        (Sm + 6 * L + 3 * (M + 4) + 12) := by
      intro j hj
      have hjn : j < n := by omega
      refine (hE (ms i j, l[j])).imp (fun _ _ hws => by rw [hws, hcont j hjn]; rfl)
        (fun _ _ _ _ _ ⟨h, he⟩ => ⟨h, by rw [he]; simp [es, List.getElem?_eq_getElem hjn]⟩) ?_ ?_
      · have := hT j hjn
        omega
      · have := hSm j hjn
        have := hmsS i hi j hjn.le
        have := hAj j hjn
        simp only [encPair_apply, List.length_append, length_frame]
        omega
    have hN' : ∀ j < toks.length, TransformsTapes ((tmN.onWords true).extendTapes eN)
        (fun _ ws => ws = Function.update (fun _ => []) V (frame (encS (ms i j)) ++ cont' j))
        (fun _ ws ws' em => ws' = Function.update ws N (frame (encS (ms i (j + 1)))) ∧ em = [])
        (T + 3 * (D * (L + 1)) + 7) (Sm + 3 * (D * (L + 1)) + 10 * L + 4 * (M + 4) + 20) := by
      intro j hj
      have hjn : j < n := by omega
      have h₁ := hmsS i hi (j + 1) hjn
      refine (hN (ms i j, l[j])).imp (fun _ _ hws => by rw [hws, hcont j hjn]; rfl)
        (fun _ _ _ _ _ ⟨h, he⟩ => ⟨by rw [h]; simp [hnextS i hi j hjn], he⟩) ?_ ?_
      · have := hT j hjn
        have := hmul cfr (by omega) _ h₁
        have := hmul cN (by omega) _ h₁
        simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame, hnextS i hi j hjn]
        omega
      · have := hSm j hjn
        have := hmsS i hi j hjn.le
        have := hAj j hjn
        have := hmul cfr (by omega) _ h₁
        have := hmul cN (by omega) _ h₁
        simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame, hnextS i hi j hjn,
          encPair_apply, List.length_append]
        omega
    have hn₀ := hmsS i hi n le_rfl
    have hn₁ := hpsS (i + 1) (by omega)
    have hEe : TransformsTapes ((tmPE.inputFromWord true).extendTapes ePE)
        (fun _ ws => ws = Function.update (fun _ => []) V (frame (encS (ms i toks.length))))
        (fun _ ws ws' em => ws' = ws ∧ em = encE' (passEmit (ms i toks.length)))
        (T + 3 * (D * (L + 1)) + 4) (Sm + 3 * (D * (L + 1)) + 4 * L + 3 * (M + 4) + 12) := by
      rw [hlen]
      refine (hPE (ms i n)).imp (fun _ _ h => h) (fun _ _ _ _ _ h => h) ?_ ?_
      · have := hTe
        have := hmul₂ cuf (by omega) _ hn₀
        have := hmul cPE (by omega) _ hn₀
        simp only [id_eq, encFramed_apply, length_frame]
        omega
      · have := hSe
        have := hmul₂ cuf (by omega) _ hn₀
        have := hmul cPE (by omega) _ hn₀
        simp only [id_eq, encFramed_apply, length_frame]
        omega
    have hNe : TransformsTapes ((tmPN.onWords true).extendTapes ePN)
        (fun _ ws => ws = Function.update (fun _ => []) V (frame (encS (ms i toks.length))))
        (fun _ ws ws' em => ws' = Function.update ws N (frame (encS (ps (i + 1)))) ∧ em = [])
        (T + 10 * (D * (L + 1)) + 7) (Sm + 20 * (D * (L + 1)) + 4 * (M + 4) + 20) := by
      rw [hlen]
      refine (hPN (ms i n)).imp (fun _ _ h => h) (fun _ _ _ _ _ h => h) ?_ ?_
      · have := hTe
        have := hmul₂ cuf (by omega) _ hn₀
        have := hmul cPN₁ (by omega) _ hn₀
        have := hmul cfr (by omega) _ hn₁
        have := hmul cPN (by omega) _ hn₁
        simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame, hendS]
        omega
      · have := hSe
        have := hmul₂ cuf (by omega) _ hn₀
        have := hmul cPN₁ (by omega) _ hn₀
        have := hmul cfr (by omega) _ hn₁
        have := hmul cPN (by omega) _ hn₁
        simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame, hendS]
        omega
    have hCm : TransformsTapes ((tmC.onWords true).extendTapes eC)
        (fun _ ws => ws = Function.update (fun _ => []) V (frame (encS (ps (i + 1)))))
        (fun _ ws ws' em => ws' = Function.update ws C (cs (i + 1)) ∧ em = [])
        (T + 10 * (D * (L + 1)) + 7) (Sm + 20 * (D * (L + 1)) + 4 * (M + 4) + 20) := by
      have hfl1 : (flagWord (cont (ps (i + 1)))).length ≤ 1 := by
        unfold flagWord; split_ifs <;> simp
      refine (hC (ps (i + 1))).imp (fun _ _ h => h)
        (fun _ _ _ _ _ ⟨h, he⟩ => ⟨by rw [h]; simp [cs], he⟩) ?_ ?_
      · have := hTe
        have := hmul₂ cuf (by omega) _ hn₁
        have := hmul cC₁ (by omega) _ hn₁
        have := hc2 cfl (by omega) 1 le_rfl
        have := hc2 cC (by omega) 1 le_rfl
        simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame, encBool_apply,
          List.length_singleton, encBits_apply]
        omega
      · have := hSe
        have := hmul₂ cuf (by omega) _ hn₁
        have := hmul cC₁ (by omega) _ hn₁
        have := hc2 cfl (by omega) 1 le_rfl
        have := hc2 cC (by omega) 1 le_rfl
        simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame, encBool_apply,
          List.length_singleton, encBits_apply]
        omega
    have hsR : ∀ j < toks.length, (frame (encS (ms i j)) ++ cont' j).length + 2 + (M + 4 - 1) +
        ((Sm + 6 * L + 3 * (M + 4) + 12) + ((Sm + 3 * (D * (L + 1)) + 10 * L + 4 * (M + 4) + 20) +
          (((frame (encS (ms i j)) ++ cont' j).length + 1 + (M + 4)) +
            ((4 * (frame (encS (ms i (j + 1)))).length + (M + 4) + 15) +
              ((frame (encS (ms i (j + 1)))).length + 1 + (M + 4)))))) ≤ sR := by
      intro j hj
      have hjn : j < n := by omega
      have := hmsS i hi j hjn.le
      have := hmsS i hi (j + 1) hjn
      have := hAj j hjn
      simp only [List.length_append, length_frame, hcont j hjn]
      omega
    have hsum : ∑ j ∈ Finset.range toks.length, (streamRoundTime toks cont'
        (fun j => frame (encS (ms i j))) (fun _ => T + 4) (fun _ => T + 3 * (D * (L + 1)) + 7) j +
          1) ≤ (encIn x).length + n * (2 * T + 4 * (D * (L + 1))) := by
      refine (Finset.sum_le_sum fun j hj => (?_ : _ ≤ (toks[j]?.getD []).length +
        (2 * T + 4 * (D * (L + 1))))).trans_eq ?_
      · have hjn : j < n := by simp at hj; omega
        have := hmsS i hi j hjn.le
        have := hmsS i hi (j + 1) hjn
        have := hAj j hjn
        simp only [streamRoundTime, List.length_append, length_frame, hcont j hjn]
        omega
      · rw [Finset.sum_add_distrib, sum_length_getD, ← hx, Finset.sum_const, Finset.card_range,
          smul_eq_mul, hlen]
    have hcs (i : ℕ) : (cs i).length ≤ 1 := by
      simp only [cs, flagWord]
      split_ifs <;> simp
    refine (transformsTapes_passTM (r := r) hVN hVF hNF hVC toks htoks cont'
      (fun j => frame (encS (ms i j))) (es i) (encE' (passEmit (ms i toks.length)))
      (frame (encS (ps (i + 1)))) (cs i) (cs (i + 1)) hread' hE' hN' hsR hEe hNe hCm).imp
      (fun _ _ ⟨hin, hws⟩ => ⟨hin.trans hx, hws⟩)
      (fun _ _ _ _ _ ⟨hws, he⟩ => ⟨hws, by rw [he, hlen]⟩) ?_ ?_
    · have := hcs i
      have := hmsS i hi n le_rfl
      have hnR : n * (2 * T + 4 * (D * (L + 1))) ≤ n * R := Nat.mul_le_mul_left _ (by omega)
      have hR : (n + 1) * R = n * R + R := by ring
      have hRdef : R = 3 * T + 60 * (D * (L + 1)) := rfl
      simp only [hlen, length_frame, tP, hR, ← hx] at hsum ⊢
      omega
    · have := hcs i
      have := hmsS i hi n le_rfl
      simp only [hlen, length_frame, sP]
      omega
  -- the initial state and the final emission
  have hP0 : (encS (init x)).length ≤ L := hpsS 0 (Nat.zero_le _)
  have hPl := hpsS (passes x + 1) le_rfl
  have hI₀ : TransformsTapes (tmI.outputToWord.extendTapes eI)
      (fun inp ws => inp = encIn x ∧ ws = fun _ => [])
      (fun _ _ ws' em => ws' = Function.update (fun _ => []) V (frame (encS (ps 0))) ∧ em = [])
      (tI x + 4 * (D * (L + 1))) (sI x + 4 * (D * (L + 1)) + 2 * (M + 4)) := by
    refine (hI x).imp (fun _ _ h => h) (fun _ _ _ _ _ h => h) ?_ ?_ <;>
    · have := hmul cfr (by omega) _ hP0
      have := hmul cI (by omega) _ hP0
      simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame]
      omega
  have hF₀ : TransformsTapes ((tmF.inputFromWord true).extendTapes eF)
      (fun _ ws => ws = Function.update (fun _ => []) V (frame (encS (ps (passes x + 1)))))
      (fun _ ws ws' em => ws' = ws ∧ em = encF (finish (ps (passes x + 1))))
      (tF (ps (passes x + 1)) + 4 * (D * (L + 1)))
      (sF (ps (passes x + 1)) + 4 * (D * (L + 1)) + 3 * (M + 4) + 10) := by
    refine (hF (ps (passes x + 1))).imp (fun _ _ h => h) (fun _ _ _ _ _ h => h) ?_ ?_ <;>
    · have := hmul₂ cuf (by omega) _ hPl
      have := hmul cF (by omega) _ hPl
      simp only [id_eq, encFramed_apply, length_frame]
      omega
  have hcs : ∀ i < passes x, cs (i + 1) ≠ [] := fun i hi => by
    have : cont (ps (i + 1)) = decide (i < passes x) := hpasses x i hi.le
    simp [cs, this, hi, flagWord]
  have hlast : cs (passes x + 1) = [] := by
    have : cont (ps (passes x + 1)) = decide (passes x < passes x) := hpasses x _ le_rfl
    simp [cs, this, flagWord]
  have h := computesTidily_multiPassTM hVC (encIn x) (passes x) (fun i => frame (encS (ps i))) cs
    (fun i => ((List.range n).map (es i)).flatten ++ encE' (passEmit (ms i n)))
    (encF (finish (ps (passes x + 1)))) hI₀ hpass rfl hcs hlast hF₀
  have hout : encOut (g x) = ((List.range (passes x + 1)).map fun i =>
      ((List.range n).map (es i)).flatten ++ encE' (passEmit (ms i n))).flatten ++
        encF (finish (ps (passes x + 1))) := by
    rw [hg x]
    simp only [streamEmit_eq]
    rfl
  rw [hout]
  have htPdef : tP = 2 * (encIn x).length + (n + 1) * R + 100 := rfl
  have hRdef : R = 3 * T + 60 * (D * (L + 1)) := rfl
  have hsRdef : sR = 2 * Sm + 6 * (D * (L + 1)) + 30 * L + 20 * (M + 4) + 100 := rfl
  have hsPdef : sP = 2 * (M + 4) * sR + 3 * Sm + 60 * (D * (L + 1)) + 20 * (M + 4) + 100 := rfl
  clear_value tP R sP sR D L T Sm
  have hD1 : 1 ≤ D := by omega
  have hDE : D ≤ D * D * D := Nat.le_mul_of_pos_left _ (Nat.mul_pos hD1 hD1)
  have hE1 : 1 ≤ D * D * D := hD1.trans hDE
  have hPl' : (frame (encS (ps (passes x + 1)))).length ≤ 2 * L + 1 := by rw [length_frame]; omega
  refine h.mono ?_ ?_
  · beta_reduce
    rw [← hTdef, ← hLdef]
    change _ ≤ 2000 * (D * D * D) * (tI x + tF (ps (passes x + 1)) +
      (passes x + 1) * ((encIn x).length + (n + 1) * (T + L + 1)))
    set P := passes x + 1
    set E := D * D * D
    set Nn := (encIn x).length
    set W := P * (Nn + (n + 1) * (T + L + 1))
    have htP : tP + 1 ≤ 200 * D * (Nn + (n + 1) * (T + L + 1)) := by
      have ha : (n + 1) * T ≤ D * ((n + 1) * T) := Nat.le_mul_of_pos_left _ hD1
      have hb : 1 ≤ (n + 1) * (L + 1) := Nat.mul_pos (by omega) (by omega)
      have hb' : (n + 1) * (L + 1) ≤ D * ((n + 1) * (L + 1)) := Nat.le_mul_of_pos_left _ hD1
      have hN : Nn ≤ D * Nn := Nat.le_mul_of_pos_left _ hD1
      calc tP + 1 = 2 * Nn + (3 * ((n + 1) * T) + 60 * (D * ((n + 1) * (L + 1)))) + 101 := by
            rw [htPdef, hRdef]; ring
        _ ≤ 200 * (D * Nn) + 200 * (D * ((n + 1) * T)) + 200 * (D * ((n + 1) * (L + 1))) := by
            omega
        _ = 200 * D * (Nn + (n + 1) * (T + L + 1)) := by ring
    have hW : L + 1 ≤ W :=
      calc L + 1 ≤ T + L + 1 := by omega
        _ ≤ (n + 1) * (T + L + 1) := Nat.le_mul_of_pos_left _ (by omega)
        _ ≤ Nn + (n + 1) * (T + L + 1) := by omega
        _ ≤ W := Nat.le_mul_of_pos_left _ (by omega)
    have h₁ : P * (tP + 1) ≤ 200 * (D * W) :=
      (Nat.mul_le_mul_left P htP).trans_eq (by simp only [W]; ring)
    have h₂ : D * (L + 1) ≤ D * W := Nat.mul_le_mul_left D hW
    have h₃ : D * W ≤ E * W := Nat.mul_le_mul_right W hDE
    have h₄ : tI x ≤ E * tI x := Nat.le_mul_of_pos_left _ hE1
    have h₅ : tF (ps P) ≤ E * tF (ps P) := Nat.le_mul_of_pos_left _ hE1
    have h₆ : 2000 * E * (tI x + tF (ps P) + W) = 2000 * (E * tI x) + 2000 * (E * tF (ps P)) +
        2000 * (E * W) := by ring
    rw [h₆]
    omega
  · beta_reduce
    rw [← hSdef, ← hLdef]
    change _ ≤ 2000 * (D * D * D) * (sI x + sF (ps (passes x + 1)) + Sm + L + 1)
    set E := D * D * D
    set Y := Sm + L + 1
    have hY : D * Y = D * Sm + D * (L + 1) := by simp only [Y]; ring
    have hSm : Sm ≤ D * Sm := Nat.le_mul_of_pos_left _ hD1
    have hDL : D ≤ D * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have hsR : sR ≤ 200 * (D * Y) := by omega
    have hKs : (M + 4) * sR ≤ 200 * (D * (D * Y)) :=
      (Nat.mul_le_mul (by omega) hsR).trans_eq (by ring)
    have hDY : D * Y ≤ D * (D * Y) := Nat.le_mul_of_pos_left _ hD1
    have hsP : (M + 4) * sP ≤ 600 * (E * Y) := by
      have : sP ≤ 600 * (D * (D * Y)) := by rw [hsPdef, Nat.mul_assoc]; omega
      exact (Nat.mul_le_mul (by omega) this).trans_eq (by simp only [E]; ring)
    have hEY : D * Y ≤ E * Y := Nat.mul_le_mul_right Y hDE
    have h₄ : sI x ≤ E * sI x := Nat.le_mul_of_pos_left _ hE1
    have h₅ : sF (ps (passes x + 1)) ≤ E * sF (ps (passes x + 1)) :=
      Nat.le_mul_of_pos_left _ hE1
    have h₆ : 2000 * E * (sI x + sF (ps (passes x + 1)) + Sm + L + 1) =
        2000 * (E * sI x) + 2000 * (E * sF (ps (passes x + 1))) + 2000 * (E * Y) := by
      simp only [Y]; ring
    have h₇ : 2 * (M + 4) * sP = 2 * ((M + 4) * sP) := by ring
    rw [h₆, h₇]
    omega

end Turing.MultiTapeTM
