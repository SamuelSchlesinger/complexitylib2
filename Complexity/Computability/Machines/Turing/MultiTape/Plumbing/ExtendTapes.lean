/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: submitted #1111 @3441fa81

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Complexity.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Specifications on the selected tapes

The additions of cslib PR #1111 to
`Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes`.

## Main results

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

end Turing.MultiTapeTM
