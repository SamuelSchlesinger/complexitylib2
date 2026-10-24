/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Game
public import Complexity.Languages.Probabilistic.UntilBad

/-!
# Game hops that are identical until bad

Two games that run one program against stateful handlers that agree until a bad state, followed by
the same final step, have advantage at most the probability of reaching a bad state
(`OracleComp.IdenticalUntilBad.advantage_le`, [BonehShoup2023], Theorem 4.7). This is the
two-sided difference lemma `OracleComp.IdenticalUntilBad.abs_sub_le` in the form that composes
with `Game.advantage_triangle`.

## Main results

* `Cslib.OracleComp.IdenticalUntilBad.advantage_le`: the advantage of an identical-until-bad hop.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Theorem 4.7.
-/

@[expose] public section

namespace Cslib.OracleComp.IdenticalUntilBad

open Crypto

variable {ι σ α : Type} {spec : ι → Type} {first second : (q : ι) → StateT σ PMF (spec q)}
  {bad : σ → Prop}

/-- **The difference lemma** ([BonehShoup2023], Theorem 4.7): games that run a program against
handlers agreeing until a bad state, followed by the same final step, have advantage at most the
probability of reaching a bad state. -/
theorem advantage_le (h : IdenticalUntilBad first second bad) (program : OracleComp spec α)
    (s : σ) (next : α × σ → Game) :
    (Game.advantage (((interpret first program).run s).bind next)
        (((interpret second program).run s).bind next) : ℝ) ≤
      (((interpret first program).run s).toOuterMeasure {x | bad x.2}).toReal := by
  rw [Game.coe_advantage]
  simpa only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal] using
    h.abs_sub_le program s next true

end Cslib.OracleComp.IdenticalUntilBad
