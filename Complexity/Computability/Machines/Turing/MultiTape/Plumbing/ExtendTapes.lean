/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: submitted #1111 @3441fa81
-- `space_embed_le`, `space_tapeEmb_le` and `space_noTapes_le` are from
-- crei:crei/tidy-universal @7f7c0696 (unsubmitted).

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Complexity.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Specifications on the selected tapes

The additions of cslib PR #1111 and of Christian Reitwiessner's branch `crei/tidy-universal` to
`Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes`.

## Main results

* `Turing.MultiTapeTM.space_embed_le`, `Turing.MultiTapeTM.space_tapeEmb_le`,
  `Turing.MultiTapeTM.space_noTapes_le`: the space of a reindexed run.
* `Turing.MultiTapeTM.TransformsTapes.extendTapes`: a specification, read on the tapes selected by
  `e`.
-/

namespace Turing.MultiTapeTM

variable {k k' : ℕ} {Symbol State : Type*} {input : List Symbol}

/-! ### Specifications on the selected tapes -/

/-- Placing the words `v` on the tapes selected by `e` and the words `ws` on the others gives the
`wordsCfg` configuration of any `ws'` that agrees with `v` through `e` and with `ws` elsewhere. -/
public lemma embed_wordsCfg (e : Fin k ↪ Fin k') {q : Option State} {v : Fin k → List Symbol}
    {ws ws' : Fin k' → List Symbol} {out : List Symbol} (h : ∀ j, ws' (e j) = v j)
    (hx : ∀ l ∉ Set.range e, ws' l = ws l) :
    embed e (wordsCfg input q v out) (fun l => tapeOfList (ws l)) (fun _ => 0) =
      wordsCfg input q ws' out := by
  refine Cfg.ext rfl rfl (funext fun l => ?_) (funext fun l => ?_) rfl
  · rcases hl : partialInv e l with _ | j
    · simp [embed, hl, wordsCfg, hx l fun ⟨j, hj⟩ => by simp [← hj] at hl]
    · simp [embed, wordsCfg, ← partialInv_eq_some e hl, h]
  · simp only [embed]
    cases partialInv e l <;> rfl

/-- **A specification on the tapes selected by `e`.** `tm.extendTapes e` transforms the words on the
selected tapes as `tm` does and leaves every other word alone; each other tape costs one cell. -/
public theorem TransformsTapes.extendTapes {tm : MultiTapeTM k Symbol State}
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop} {t s : ℕ}
    (h : TransformsTapes tm P Q t s) (e : Fin k ↪ Fin k') :
    TransformsTapes (tm.extendTapes e) (fun input ws => P input fun j => ws (e j))
      (fun input ws ws' emitted => Q input (fun j => ws (e j)) (fun j => ws' (e j)) emitted ∧
        ∀ l ∉ Set.range e, ws' l = ws l)
      t (s + (k' - k)) := by
  intro input ws out hP
  obtain ⟨v, emitted, hQ, p, hhead, hlast, htime, hspace⟩ := h input (fun j => ws (e j)) out hP
  -- `v` on the selected tapes, `ws` on the others
  let ws' : Fin k' → List Symbol := fun l => (partialInv e l).elim (ws l) v
  have hv : ∀ j, ws' (e j) = v j := by simp [ws']
  have hx : ∀ l ∉ Set.range e, ws' l = ws l := fun l hl => by simp [ws', partialInv_eq_none e hl]
  -- the path of the extended machine is the path of `tm`, placed on the selected tapes
  refine ⟨ws', emitted, ⟨by simpa only [hv] using hQ, hx⟩,
    p.map (embedHom tm e (fun l => tapeOfList (ws l)) (fun _ => 0)), ?_, ?_, htime,
    (space_map_embedHom_le ..).trans (Nat.add_le_add_right hspace _)⟩
  · simp only [RelSeries.head_map, hhead, embedHom_apply, extendTapes_q₀]
    exact embed_wordsCfg e (fun _ => rfl) fun _ _ => rfl
  · simp only [RelSeries.last_map, hlast, embedHom_apply]
    exact embed_wordsCfg e hv hx

/-! ### Space of reindexed runs -/

-- vendored: `spaceUsed` is `space` since cslib #1133; the proofs go through the paths of cslib
-- #1117 (`space_map_embedHom_le`)
/-- **Space bound for a reindexed run.** The embedded tapes contribute the space used by `tm`, while
each of the remaining `k' - k` tapes never moves and contributes at most one cell. -/
public lemma space_embed_le (tm : MultiTapeTM k Symbol State) (e : Fin k ↪ Fin k')
    (cfg : Cfg k Symbol State input) (extraTapes : Fin k' → ℤ → Option Symbol)
    (extraPos : Fin k' → ℤ) (n : ℕ) :
    (tm.extendTapes e).space (embed e cfg extraTapes extraPos) n
      ≤ tm.space cfg n + (k' - k) := by
  have h := (MultiTapeNTM.RunPath.map_ofDeterministic (embedHom tm e extraTapes extraPos) cfg n)
  simp only [embedHom_apply] at h
  rw [space, ← h]
  exact space_map_embedHom_le ..

/-- **Space bound for a one-tape machine placed on tape `i`:** the space of the one-tape run, plus
one cell for each tape the machine does not use. -/
public lemma space_tapeEmb_le {k : ℕ} (tm : MultiTapeTM 1 Symbol State) (i : Fin k)
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    (tm.extendTapes (tapeEmb i)).space cfg n ≤ tm.space (oneTapeCfg i cfg) n + (k - 1) := by
  conv_lhs => rw [← embed_oneTapeCfg i cfg]
  exact space_embed_le _ _ _ _ _ _

/-- **Space bound for a machine without work tapes:** one cell for each tape it does not use. -/
public lemma space_noTapes_le {k : ℕ} (tm : MultiTapeTM 0 Symbol State)
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    (tm.extendTapes (noTapes k)).space cfg n ≤ k := by
  conv_lhs => rw [← embed_noTapesCfg cfg]
  simpa using space_embed_le tm (noTapes k) (noTapesCfg cfg) cfg.workTapes cfg.workTapePos n

end Turing.MultiTapeTM
