/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.CopyWord
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ReadInput
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.WhileInput
public import Complexity.Foundations.Data.Fin.Tuple
import Mathlib.Tactic.FinCases

/-!
# Streaming folds

A streaming fold reads its input once, from left to right, one token at a time. It keeps a state
on a work tape; for each token it appends the token's content to the state, computes the next
state from the result and emits a word to the output. The input is never copied, so a round costs
time and space in the size of the state and the token only.

## Main definitions

* `Turing.MultiTapeTM.frozenRound`: the part of a round that does not use the input.

## Main results

* `Turing.MultiTapeTM.transformsTapes_frozenRound`: the specification of `frozenRound`.
-/

namespace Turing.MultiTapeTM

variable {m K : ℕ} {Symbol S : Type*}

/-! ### Specifications on selected tapes -/

/-- An embedding of `Fin m` into a larger `Fin K` sending `i` to `a`. -/
public theorem exists_embedding_eq (h : m ≤ K) (i : Fin m) (a : Fin K) :
    ∃ e : Fin m ↪ Fin K, e i = a :=
  ⟨(Fin.castLEEmb h).trans (Equiv.swap (Fin.castLE h i) a).toEmbedding, by simp⟩

/-- An embedding of `Fin m` into a larger `Fin K` sending `i` to `a` and `o` to `b`. -/
public theorem exists_embedding_eq₂ (h : m ≤ K) {i o : Fin m} (hio : i ≠ o) {a b : Fin K}
    (hab : a ≠ b) : ∃ e : Fin m ↪ Fin K, e i = a ∧ e o = b := by
  obtain ⟨e, he⟩ := exists_embedding_eq h i a
  refine ⟨e.trans (Equiv.swap (e o) b).toEmbedding, ?_, by simp⟩
  have hoa : e o ≠ a := fun h => hio (e.injective (h.trans he.symm)).symm
  simp [he, Equiv.swap_apply_of_ne_of_ne hoa.symm hab]

/-! ### The part of a round that does not use the input -/

section Frozen

variable {SE SN : Type*} {E : MultiTapeTM K Bool SE} {Nm : MultiTapeTM K Bool SN}
  {V N F : Fin K}

/-- The three tapes `V`, `N`, `F` of `copyWord`: target, source and flag. -/
public def threeTapes (V N F : Fin K) (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F) :
    Fin (0 + 1 + 2) ↪ Fin K :=
  ⟨![V, N, F], by intro a b h; fin_cases a <;> fin_cases b <;> simp_all [eq_comm]⟩

/-- Emit with `E` from the word on tape `V`, write the next state to tape `N` with `Nm`, and move
it to tape `V`, using tape `F` to flag the left end of the word. -/
public noncomputable def frozenRound (E : MultiTapeTM K Bool SE) (Nm : MultiTapeTM K Bool SN)
    (V N F : Fin K) (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F) :=
  E.seq (Nm.seq (((clearWork Bool).extendTapes (tapeEmb V)).seq
    ((copyWord (threeTapes V N F hVN hVF hNF) true).seq
      ((clearWork Bool).extendTapes (tapeEmb N)))))

open Sequential in
/-- `frozenRound` takes the word `w` on tape `V` and every other tape blank to `next` on tape `V`
and every other tape blank, emitting `emit`, if `E` emits `emit` from `w` and `Nm` writes `next`
to tape `N`. -/
public theorem transformsTapes_frozenRound (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F)
    {w emit next : List Bool} {tE sE tN sN : ℕ}
    (hE : TransformsTapes E (fun _ ws => ws = Function.update (fun _ => []) V w)
      (fun _ ws ws' em => ws' = ws ∧ em = emit) tE sE)
    (hN : TransformsTapes Nm (fun _ ws => ws = Function.update (fun _ => []) V w)
      (fun _ ws ws' em => ws' = Function.update ws N next ∧ em = []) tN sN) :
    TransformsTapes (frozenRound E Nm V N F hVN hVF hNF)
      (fun _ ws => ws = Function.update (fun _ => []) V w)
      (fun _ _ ws' em => ws' = Function.update (fun _ => []) V next ∧ em = emit)
      (tE + (tN + (3 * (w.length + 1) + ((3 * next.length + 10) + 3 * (next.length + 1)))))
      (sE + (sN + ((w.length + 1 + K) + ((4 * next.length + K + 15) +
        (next.length + 1 + K))))) := by
  set W₀ := Function.update (fun _ => ([] : List Bool)) V w
  set W₁ := Function.update W₀ N next
  set W₂ := Function.update W₁ V []
  set W₃ := Function.update W₂ V next
  have hW₄ : Function.update W₃ N [] = Function.update (fun _ => []) V next := by
    funext l
    simp only [W₃, W₂, W₁, W₀, Function.update_apply]
    split_ifs <;> simp_all
  have h₀ : TransformsTapes E (fun _ ws => ws = W₀) (fun _ _ ws' em => ws' = W₀ ∧ em = emit)
      tE sE := hE.imp (fun _ _ h => h) (fun _ _ _ _ hws ⟨h, he⟩ => ⟨h.trans hws, he⟩) le_rfl le_rfl
  have h₁ : TransformsTapes Nm (fun _ ws => ws = W₀) (fun _ _ ws' em => ws' = W₁ ∧ em = [])
      tN sN := hN.imp (fun _ _ h => h) (fun _ _ _ _ hws ⟨h, he⟩ => ⟨by rw [h, hws], he⟩)
      le_rfl le_rfl
  have h₂ : TransformsTapes ((clearWork Bool).extendTapes (tapeEmb V)) (fun _ ws => ws = W₁)
      (fun _ _ ws' em => ws' = W₂ ∧ em = []) (3 * (w.length + 1)) (w.length + 1 + K) :=
    (transformsTapes_clearWork_tapeEmb V w).imp (fun _ _ h => by simp [h, W₁, W₀, hVN])
      (fun _ _ _ _ hws ⟨h, he⟩ => ⟨by rw [h, hws], he⟩) le_rfl le_rfl
  have h₃ := (transformsTapes_copyWord (threeTapes V N F hVN hVF hNF) true next).imp
    (P' := fun _ ws => ws = W₂) (Q' := fun _ _ ws' em => ws' = W₃ ∧ em = [])
    (fun _ _ h => by
      subst h
      change W₂ N = next ∧ W₂ V = [] ∧ W₂ F = []
      simp [W₂, W₁, W₀, hVN.symm, hVF.symm, hNF.symm])
    (fun _ _ _ _ hws ⟨h, he⟩ => ⟨by rw [h, hws]; rfl, he⟩) le_rfl le_rfl
  have h₄ : TransformsTapes ((clearWork Bool).extendTapes (tapeEmb N)) (fun _ ws => ws = W₃)
      (fun _ _ ws' em => ws' = Function.update (fun _ => []) V next ∧ em = [])
      (3 * (next.length + 1)) (next.length + 1 + K) :=
    (transformsTapes_clearWork_tapeEmb N next).imp
      (fun _ _ h => by simp [h, W₃, W₂, W₁, hVN.symm])
      (fun _ _ _ _ hws ⟨h, he⟩ => ⟨by rw [h, hws, hW₄], he⟩) le_rfl le_rfl
  refine (h₀.seq_eq (h₁.seq_eq (h₂.seq_eq (h₃.seq_eq h₄)))).imp (fun _ _ h => h)
    (fun _ _ _ _ _ ⟨h, he⟩ => ⟨h, by simp [he]⟩) le_rfl le_rfl

end Frozen

/-! ### Rounds and the whole machine -/

section Stream

variable {Q SI SE SN SF : Type*} {r : InputReader Bool Q} {I : MultiTapeTM K Bool SI}
  {E : MultiTapeTM K Bool SE} {Nm : MultiTapeTM K Bool SN} {Fm : MultiTapeTM K Bool SF}
  {V N F : Fin K}

/-- One round: append the content of the next token to the state on tape `V`, then run
`frozenRound` with the input head frozen. -/
public noncomputable def streamRound (r : InputReader Bool Q) (E : MultiTapeTM K Bool SE)
    (Nm : MultiTapeTM K Bool SN) (V N F : Fin K) (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F) :=
  (appendRead r V).seq (frozenRound E Nm V N F hVN hVF hNF).freezeInput

/-- The streaming fold: write the initial state to tape `V` with `I`, run rounds while there is
input left, emit from the final state with `Fm`, clear tape `V` and rewind the input. -/
public noncomputable def streamTM (r : InputReader Bool Q) (I : MultiTapeTM K Bool SI)
    (E : MultiTapeTM K Bool SE) (Nm : MultiTapeTM K Bool SN) (Fm : MultiTapeTM K Bool SF)
    (V N F : Fin K) (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F) :=
  I.seq ((whileInput (streamRound r E Nm V N F hVN hVF hNF)).seq
    ((Fm.seq ((clearWork Bool).extendTapes (tapeEmb V))).freezeInput.seq (rewindInputOn K Bool)))

/-- One round at the input position `p₀` of `x`, on the state `v`: if `E` emits `emit` from the
state with the token's content appended and `Nm` computes `next` from it, the round leaves `next`
on tape `V`, emits `emit` and moves the input head over the token. -/
public theorem transformsTapesAt_streamRound (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F)
    (x : List Bool) (p₀ : Fin (x.length + 2)) (hp₀ : p₀.val ≠ 0) (v : List Bool)
    {emit next : List Bool} {tE sE tN sN : ℕ}
    (hE : TransformsTapes E
      (fun _ ws => ws = Function.update (fun _ => []) V
        (v ++ (r.read r.q₀ (x.drop (p₀.val - 1))).1))
      (fun _ ws ws' em => ws' = ws ∧ em = emit) tE sE)
    (hN : TransformsTapes Nm
      (fun _ ws => ws = Function.update (fun _ => []) V
        (v ++ (r.read r.q₀ (x.drop (p₀.val - 1))).1))
      (fun _ ws ws' em => ws' = Function.update ws N next ∧ em = []) tN sN) :
    let rd := r.read r.q₀ (x.drop (p₀.val - 1))
    TransformsTapesAt (streamRound r E Nm V N F hVN hVF hNF)
      (fun input p ws => input = x ∧ p.val = p₀.val ∧ ws = Function.update (fun _ => []) V v)
      (fun _ _ _ p' ws' em => p'.val = p₀.val + rd.2 ∧
        ws' = Function.update (fun _ => []) V next ∧ em = emit)
      (v.length + 1 + ((rd.2 + 1) + ((v ++ rd.1).length + 2)) +
        (tE + (tN + (3 * ((v ++ rd.1).length + 1) + ((3 * next.length + 10) +
          3 * (next.length + 1))))))
      ((v ++ rd.1).length + 2 + (K - 1) +
        (sE + (sN + (((v ++ rd.1).length + 1 + K) + ((4 * next.length + K + 15) +
          (next.length + 1 + K)))))) := by
  intro rd
  have hread := (transformsTapesAt_appendRead r V x p₀ hp₀ v).imp
    (P' := fun input p ws => input = x ∧ p.val = p₀.val ∧ ws = Function.update (fun _ => []) V v)
    (fun _ _ ws ⟨hx, hp, hws⟩ => ⟨hx, hp, by simp [hws]⟩) (fun _ _ _ _ _ _ _ h => h) le_rfl le_rfl
  refine (transformsTapesAt_seq hread
    (transformsTapes_frozenRound hVN hVF hNF hE hN).freezeInput ?_).imp
    (fun _ _ _ h => h) ?_ le_rfl le_rfl
  · rintro _ _ ws _ _ _ ⟨-, -, hws⟩ ⟨-, hws', -⟩
    rw [hws', hws, Function.update_idem]
  · rintro _ _ _ _ _ _ _ ⟨_, _, _, _, ⟨hp, -, rfl⟩, ⟨rfl, hws, rfl⟩, rfl⟩
    exact ⟨hp, hws, rfl⟩

/-- The input position after the first `j` tokens. -/
public lemma streamPos_lt (toks : List (List Bool)) (j : ℕ) :
    1 + ((toks.take j).flatten).length < toks.flatten.length + 2 := by
  have := (List.take_sublist j toks).flatten.length_le
  omega

public lemma drop_flatten_take (toks : List (List Bool)) {j : ℕ} (hj : j < toks.length) :
    toks.flatten.drop ((toks.take j).flatten).length =
      toks[j] ++ (toks.drop (j + 1)).flatten := by
  calc toks.flatten.drop ((toks.take j).flatten).length
      = ((toks.take j).flatten ++ (toks.drop j).flatten).drop ((toks.take j).flatten).length := by
        rw [← List.flatten_append, List.take_append_drop]
    _ = (toks.drop j).flatten := List.drop_left
    _ = toks[j] ++ (toks.drop (j + 1)).flatten := by
        rw [List.drop_eq_getElem_cons hj, List.flatten_cons]

public lemma length_flatten_take_succ (toks : List (List Bool)) {j : ℕ} (hj : j < toks.length) :
    ((toks.take (j + 1)).flatten).length = ((toks.take j).flatten).length + toks[j].length := by
  rw [List.take_succ_eq_append_getElem hj, List.flatten_append, List.length_append]
  simp

/-- The time of round `j` of the streaming loop. -/
@[expose] public def streamRoundTime (toks : List (List Bool)) (cont vs : ℕ → List Bool)
    (tE tN : ℕ → ℕ) (j : ℕ) : ℕ :=
  (vs j).length + 1 + ((toks[j]?.getD []).length + 1 + ((vs j ++ cont j).length + 2)) +
    (tE j + (tN j + (3 * ((vs j ++ cont j).length + 1) + ((3 * (vs (j + 1)).length + 10) +
      3 * ((vs (j + 1)).length + 1)))))

/-- **The streaming loop.** The input `x` is the concatenation of the non-empty tokens `toks`, from
each of which the reader `r` reads the content `cont j`. If for every token `j` the machine `E`
emits `es j` and `Nm` computes the next state `vs (j + 1)` from the state `vs j` followed by
`cont j`, then the loop of rounds, started on the state `vs 0` at the start of the input, leaves
the final state on tape `V`, emits the words `es j` and stops at the end of the input. -/
public theorem transformsTapesAt_streamLoop (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F)
    (toks : List (List Bool)) (htoks : ∀ t ∈ toks, t ≠ []) (cont vs es : ℕ → List Bool)
    {sR : ℕ} {tE sE tN sN : ℕ → ℕ}
    (hread : ∀ j (hj : j < toks.length),
      r.read r.q₀ (toks.flatten.drop ((toks.take j).flatten).length) = (cont j, toks[j].length))
    (hE : ∀ j < toks.length, TransformsTapes E
      (fun _ ws => ws = Function.update (fun _ => []) V (vs j ++ cont j))
      (fun _ ws ws' em => ws' = ws ∧ em = es j) (tE j) (sE j))
    (hN : ∀ j < toks.length, TransformsTapes Nm
      (fun _ ws => ws = Function.update (fun _ => []) V (vs j ++ cont j))
      (fun _ ws ws' em => ws' = Function.update ws N (vs (j + 1)) ∧ em = []) (tN j) (sN j))
    (hsR : ∀ j < toks.length, (vs j ++ cont j).length + 2 + (K - 1) +
        (sE j + (sN j + (((vs j ++ cont j).length + 1 + K) + ((4 * (vs (j + 1)).length + K + 15) +
          ((vs (j + 1)).length + 1 + K))))) ≤ sR) :
    TransformsTapesAt (whileInput (streamRound r E Nm V N F hVN hVF hNF))
      (fun input p ws => input = toks.flatten ∧ p.val = 1 ∧
        ws = Function.update (fun _ => []) V (vs 0))
      (fun input _ _ p' ws' em => input = toks.flatten ∧ p'.val = 1 + toks.flatten.length ∧
        ws' = Function.update (fun _ => []) V (vs toks.length) ∧
        em = ((List.range toks.length).map es).flatten)
      (∑ j ∈ Finset.range toks.length, (streamRoundTime toks cont vs tE tN j + 1) + 1)
      (2 * K * sR + K) := by
  set x := toks.flatten with hx
  let L (j : ℕ) : ℕ := ((toks.take j).flatten).length
  let P (n : ℕ) (input : List Bool) (p : Fin (input.length + 2)) (ws : Fin K → List Bool)
      (em : List Bool) : Prop :=
    input = x ∧ p.val = 1 + L n ∧ ws = Function.update (fun _ => []) V (vs n) ∧
      em = ((List.range n).map es).flatten
  have hround : ∀ n < toks.length, ∀ acc, TransformsTapesAt (streamRound r E Nm V N F hVN hVF hNF)
      (fun input p ws => P n input p ws acc)
      (fun input _ _ p' ws' e => P (n + 1) input p' ws' (acc ++ e))
      (streamRoundTime toks cont vs tE tN n) sR := by
    intro n hn acc
    let p₀ : Fin (x.length + 2) := ⟨1 + L n, streamPos_lt toks n⟩
    have hrd : r.read r.q₀ (x.drop (p₀.val - 1)) = (cont n, toks[n].length) := by
      simpa [p₀, L] using hread n hn
    have h := transformsTapesAt_streamRound (r := r) hVN hVF hNF x p₀ (by simp [p₀]) (vs n)
      (hE := by rw [hrd]; exact hE n hn) (hN := by rw [hrd]; exact hN n hn)
    simp only [hrd] at h
    refine h.imp (fun _ _ _ ⟨hin, hp, hws, _⟩ => ⟨hin, hp, hws⟩) ?_ ?_ ?_
    · rintro _ _ _ p' ws' em ⟨rfl, -, -, rfl⟩ ⟨hp', hws', rfl⟩
      refine ⟨rfl, ?_, hws', by simp [List.range_succ]⟩
      rw [hp']
      change (1 + ((toks.take n).flatten).length) + toks[n].length =
        1 + ((toks.take (n + 1)).flatten).length
      rw [length_flatten_take_succ toks hn]
      omega
    · simp [streamRoundTime, List.getElem?_eq_getElem hn]
    · exact hsR n hn
  have hmore : ∀ n < toks.length, ∀ input p ws em, P n input p ws em →
      inputSymbolAt input p ≠ none := by
    rintro n hn input p ws em ⟨rfl, hp, -, -⟩
    have hlt : ((toks.take n).flatten).length < x.length := by
      have h₁ := length_flatten_take_succ toks hn
      have h₂ := streamPos_lt toks (n + 1)
      have : 0 < toks[n].length := List.length_pos_iff.mpr (htoks _ (List.getElem_mem hn))
      have : x.length = toks.flatten.length := rfl
      omega
    simp only [inputSymbolAt, hp, L]
    split_ifs
    · omega
    · rw [Nat.add_sub_cancel_left, List.getElem?_eq_getElem hlt]
      simp
  have hL : L toks.length = x.length := by simp only [L, List.take_length]; rfl
  refine (transformsTapesAt_whileInput hround hmore
    (R := fun input p ws em => P toks.length input p ws em)
    (fun input p ws em h => ⟨by
      obtain ⟨rfl, hp, -, -⟩ := h
      simp [inputSymbolAt, hp, hL], h⟩)).imp
    (fun _ _ _ ⟨hin, hp, hws⟩ => ⟨hin, by simp [hp, L], hws, rfl⟩)
    (fun _ _ _ _ _ _ _ ⟨hin, hp, hws, he⟩ => ⟨hin, hp.trans (by rw [hL]), hws, he⟩) le_rfl le_rfl

/-- **The streaming fold on words.** The input `x` is the concatenation of the non-empty tokens
`toks`, from each of which the reader `r` reads the content `cont j`. If `I` writes the initial
state `vs 0` to tape `V`, and for every token `j` the machine `E` emits `es j` and `Nm` computes
the next state `vs (j + 1)` from the state `vs j` followed by `cont j`, and `Fm` emits `ef` from
the final state, then `streamTM` emits the words `es j` followed by `ef`, tidily. -/
public theorem computesTidily_streamTM (hVN : V ≠ N) (hVF : V ≠ F) (hNF : N ≠ F)
    (toks : List (List Bool)) (htoks : ∀ t ∈ toks, t ≠ []) (cont vs es : ℕ → List Bool)
    (ef : List Bool) {tI sI tF sF sR : ℕ} {tE sE tN sN : ℕ → ℕ}
    (hread : ∀ j (hj : j < toks.length),
      r.read r.q₀ (toks.flatten.drop ((toks.take j).flatten).length) = (cont j, toks[j].length))
    (hI : TransformsTapes I (fun inp ws => inp = toks.flatten ∧ ws = fun _ => [])
      (fun _ _ ws' em => ws' = Function.update (fun _ => []) V (vs 0) ∧ em = []) tI sI)
    (hE : ∀ j < toks.length, TransformsTapes E
      (fun _ ws => ws = Function.update (fun _ => []) V (vs j ++ cont j))
      (fun _ ws ws' em => ws' = ws ∧ em = es j) (tE j) (sE j))
    (hN : ∀ j < toks.length, TransformsTapes Nm
      (fun _ ws => ws = Function.update (fun _ => []) V (vs j ++ cont j))
      (fun _ ws ws' em => ws' = Function.update ws N (vs (j + 1)) ∧ em = []) (tN j) (sN j))
    (hF : TransformsTapes Fm (fun _ ws => ws = Function.update (fun _ => []) V (vs toks.length))
      (fun _ ws ws' em => ws' = ws ∧ em = ef) tF sF)
    (hsR : ∀ j < toks.length, (vs j ++ cont j).length + 2 + (K - 1) +
        (sE j + (sN j + (((vs j ++ cont j).length + 1 + K) + ((4 * (vs (j + 1)).length + K + 15) +
          ((vs (j + 1)).length + 1 + K))))) ≤ sR) :
    (streamTM r I E Nm Fm V N F hVN hVF hNF).ComputesTidilyInTimeAndSpace toks.flatten
      (((List.range toks.length).map es).flatten ++ ef)
      (tI + ((∑ j ∈ Finset.range toks.length, (streamRoundTime toks cont vs tE tN j + 1)) + 1) +
        ((tF + 3 * ((vs toks.length).length + 1)) + (toks.flatten.length + 2)))
      (sI + ((2 * K * sR + K) + ((sF + ((vs toks.length).length + 1 + K)) + K))) := by
  set x := toks.flatten with hx
  have hloop := transformsTapesAt_streamLoop (r := r) hVN hVF hNF toks htoks cont vs es hread
    hE hN hsR
  -- emitting from the final state and clearing it, with the input head frozen
  have hF' : TransformsTapes Fm
      (fun _ ws => ws = Function.update (fun _ => []) V (vs toks.length))
      (fun _ _ ws' em => ws' = Function.update (fun _ => []) V (vs toks.length) ∧ em = ef)
      tF sF :=
    hF.imp (fun _ _ h => h) (fun _ _ _ _ hws ⟨h, he⟩ => ⟨h.trans hws, he⟩) le_rfl le_rfl
  have hclear : TransformsTapes ((clearWork Bool).extendTapes (tapeEmb V))
      (fun _ ws => ws = Function.update (fun _ => []) V (vs toks.length))
      (fun _ _ ws' em => ws' = (fun _ => []) ∧ em = [])
      (3 * ((vs toks.length).length + 1)) ((vs toks.length).length + 1 + K) :=
    (transformsTapes_clearWork_tapeEmb V (vs toks.length)).imp (fun _ _ h => by simp [h])
      (fun _ _ _ _ hws ⟨h, he⟩ => ⟨by rw [h, hws]; simp, he⟩) le_rfl le_rfl
  have hfin := (hF'.seq_eq hclear).freezeInput.imp
    (P' := fun input _ ws => input = x ∧ ws = Function.update (fun _ => []) V (vs toks.length))
    (fun _ _ _ h => h.2) (fun _ _ _ _ _ _ _ h => h) le_rfl le_rfl
  have hend := transformsTapesAt_seq hfin (transformsTapesAt_rewindInput (k := K) x)
    (fun _ _ _ _ _ _ h _ => h.1)
  have hmain := transformsTapesAt_seq hloop hend
    (fun _ _ _ _ _ _ _ ⟨hin, _, hws, _⟩ => ⟨hin, hws⟩)
  have hall := transformsTapesAt_seq hI.transformsTapesAt hmain
    (fun _ _ _ p' _ _ ⟨_, hin, _⟩ ⟨hp', hws', he⟩ => ⟨hin, by simp [hp'], hws'⟩)
  refine (hall.transformsTapes ?_).imp (fun _ _ ⟨hin, hws⟩ => ⟨rfl, hin, hws⟩) ?_ ?_ ?_
  · rintro _ _ _ _ _ _ ⟨_, _, _, _, -, ⟨_, _, _, _, -, ⟨_, _, _, _, -, ⟨hp, -⟩, -⟩, -⟩, -⟩
    exact hp
  · rintro _ _ _ _ _ ⟨_, _, _, _, ⟨-, -, rfl⟩, ⟨_, _, _, _, ⟨-, -, -, rfl⟩,
      ⟨_, _, _, _, ⟨-, rfl, rfl⟩, ⟨-, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    simp
  · omega
  · omega

end Stream

end Turing.MultiTapeTM
