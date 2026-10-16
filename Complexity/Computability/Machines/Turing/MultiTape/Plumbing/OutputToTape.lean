/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: submitted #1111 @3441fa81

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.RewindWork
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs

/-!
# Writing the output as a word on a work tape

The additions of cslib PR #1111 to
`Cslib.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape`.

`outputToWord tm` runs `tm` with its output redirected to a new last work tape
(`Turing.MultiTapeTM.outputToTape`), then moves the head of that tape back to cell `0`
(`Turing.MultiTapeTM.rewindWork`). If `tm` computes `output` tidily
(`Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace`), then `outputToWord tm` takes blank work tapes
to blank work tapes, except that the last one holds `output`, and emits nothing.

## Main definitions

* `Turing.MultiTapeTM.outputToWord`: the machine writing its output as a word on a work tape.

## Main results

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.outputToWord`: its specification.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-! ### Rewinding the output tape -/

/-- `tm` with its output written to a new last work tape, whose head is then moved back to
cell `0`. -/
@[expose] public noncomputable def outputToWord (tm : MultiTapeTM k Symbol State) :
    MultiTapeTM (k + 1) Symbol (State ⊕ RewindWorkState) :=
  tm.outputToTape.seq ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k)))

/-- Redirecting the output of a blank `wordsCfg` configuration adds a blank last work tape. -/
private lemma outCfg_wordsCfg (q : Option State) :
    outCfg (wordsCfg input q (fun _ : Fin k => []) []) = wordsCfg input q (fun _ => []) [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
    simp [outCfg, wordsCfg]

/-- The last work tape of `outCfg (wordsCfg input q ws out)`, as a one-tape configuration: it holds
`out`, with its head at the end of `out`. -/
private lemma oneTapeCfg_outCfg_wordsCfg (q : Option State) (ws : Fin k → List Symbol)
    (out : List Symbol) :
    oneTapeCfg (Fin.last k) (outCfg (wordsCfg input q ws out)) =
      ⟨q, 1, fun _ => tapeOfList out, fun _ => (out.length : ℤ), []⟩ := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext _ <;> simp [oneTapeCfg]

/-- Rewinding the last work tape of `outCfg (wordsCfg input q (fun _ => []) out)` takes
`out.length + 2` steps and leaves `out` as a word on that tape: it runs `rewindWork` on that tape.
-/
private lemma exists_runPath_rewindLast (out : List Symbol) :
    ∃ p : ((rewindWork Symbol).extendTapes (tapeEmb (Fin.last k))).RunPath input,
      p.head = outCfg (wordsCfg input (some (rewindWork Symbol).q₀) (fun _ : Fin k => []) out) ∧
      p.last = wordsCfg input none (Function.update (fun _ => []) (Fin.last k) out) [] ∧
      p.time = out.length + 2 ∧ p.space ≤ out.length + k + 3 := by
  let cfg := outCfg (wordsCfg input (some (rewindWork Symbol).q₀) (fun _ : Fin k => []) out)
  let r := MultiTapeNTM.RunPath.ofDeterministic (rewindWork Symbol) (oneTapeCfg (Fin.last k) cfg)
    (out.length + 2)
  refine ⟨r.map (embedHom _ (tapeEmb (Fin.last k)) cfg.workTapes cfg.workTapePos),
    embed_oneTapeCfg _ cfg, ?_, rfl, ?_⟩
  · change embed _ ((rewindWork Symbol).runFrom (oneTapeCfg _ cfg) (out.length + 2)) _ _ = _
    rw [oneTapeCfg_outCfg_wordsCfg, runFrom_rewindWork_none _ _ _ rfl le_rfl, embed_tapeEmb]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext l <;> induction l using Fin.lastCases <;>
      simp [cfg, wordsCfg]
  · -- the rewind takes `out.length + 2` steps on one tape, every other tape stays where it is
    have : r.space ≤ 1 * (out.length + 2 + 1) := r.space_le_mul_time_add_one
    exact (space_map_embedHom_le ..).trans (by omega)

open Sequential in
/-- If `tm` computes `output` tidily, then `outputToWord tm`, started on blank work tapes, halts
with `output` on its last work tape, every other work tape blank, and nothing emitted. -/
public theorem ComputesTidilyInTimeAndSpace.outputToWord {tm : MultiTapeTM k Symbol State}
    {input output : List Symbol} {t s : ℕ}
    (h : tm.ComputesTidilyInTimeAndSpace input output t s) :
    TransformsTapes tm.outputToWord
      (fun inp ws => inp = input ∧ ws = fun _ => [])
      (fun _ _ ws' e => ws' = Function.update (fun _ => []) (Fin.last k) output ∧ e = [])
      (t + output.length + 2) (s + 2 * output.length + k + 4) := by
  obtain ⟨p, hh, hl, ht, hs⟩ := computesTidily_iff.mp h
  unfold MultiTapeTM.outputToWord
  rw [transformsTapes_iff_nil_output]
  rintro inp _ ⟨hin, rfl⟩
  subst inp
  -- run `tm` with its output on the last work tape, then rewind that tape
  let p₀ := p.map (outCfgHom tm)
  have hl₀ : p₀.last = outCfg (wordsCfg input none (fun _ => []) output) := by simp [p₀, hl]
  have hs₀ : p₀.space ≤ p.space + (output.length + 1) := by
    simpa [hl] using space_map_outCfgHom_le tm p
  obtain ⟨p₁, hh₁, hl₁, ht₁, hs₁⟩ := exists_runPath_rewindLast (k := k) (input := input) output
  obtain ⟨q, hqh, hql, hqt, hqs⟩ := exists_runPath_seq_space_le (p₀ := p₀) (p₁ := p₁)
    (by rw [hl₀]; rfl) (by rw [hh₁, hl₀]; rfl) (by rw [hl₁]; rfl)
  refine ⟨_, [], ⟨rfl, rfl⟩, q, ?_, by simp [hql, hl₁, rightCfg], ?_, by omega⟩
  · simp only [hqh, p₀, RelSeries.head_map, outCfgHom_apply, hh, outCfg_wordsCfg]
    rfl
  · simp only [MultiTapeNTM.RunPath.time] at ht ht₁ ⊢
    have : p₀.length = p.length := rfl
    omega

end Turing.MultiTapeTM
