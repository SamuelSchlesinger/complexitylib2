/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Space
public import Complexity.Algorithms.Reachability.Savitch
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability
import Complexity.Computability.Kolmogorov.Incompressibility
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Savitch's decider for space-bounded nondeterministic machines

A nondeterministic machine with finitely many states, all of whose computation paths on an input
of length `n` visit at most `c * (n + 1) ^ d` work cells, is decided by the deterministic
`Turing.MultiTapeNTM.savitchDecide`: Savitch's midpoint recursion with an explicit stack
(`Cslib.Reachability.savitch`) on the codes of the finite views of the machine, asking whether
the accepting code is reachable from the code of the initial view.

Every view reachable from the initial view has an encoding of length at most
`Turing.MultiTapeNTM.viewLengthBound`, linear in `n` and the space bound, whatever the length of
the path reaching it (`Turing.MultiTapeNTM.length_encFiniteCfg_le`), so the codes have a width `W`
polynomial in `n`. Acceptance is reachability of the accepting code along the edges between codes
of `2 * W + 2` bits (`Turing.MultiTapeNTM.accepts_iff_reflTransGen_codeStep`). There are
`2 ^ (2 * W + 2)` such words, so it is reachability within as many steps, which the recursion
decides at depth `2 * W + 2`. The edge test, the codes and the width are polynomial-time, so the
decider runs in space polynomial in `n`, charging the stack of frames, the counters and the edge
test (`Cslib.Reachability.exists_polyBounded_space_savitch`); its time is exponential.

The decider retains the whole input, so this is the polynomial-space consequence of Savitch's
theorem; the quadratic bound `NSPACE(s) ⊆ DSPACE(s ^ 2)` for sublinear `s` is not claimed.

## Main definitions

* `Turing.MultiTapeNTM.codeWidth`: the width of the codes of the views.
* `Turing.MultiTapeNTM.savitchDecide`: the deterministic decider of acceptance.

## Main results

* `Turing.MultiTapeNTM.savitchDecide_eq_true_iff`: the decider decides acceptance.
* `Turing.MultiTapeNTM.exists_polyBounded_space_savitchDecide`: it runs in polynomial space.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.5][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 4.2][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeNTM

open MultiTapeTM

variable {k : ℕ} {State : Type} [Finite State] (ntm : MultiTapeNTM k Bool State)

/-- The width of the codes of the views on `input`, under the space bound
`c * (input.length + 1) ^ d`: the length of the encoding of the initial view plus the bound
`Turing.MultiTapeNTM.viewLengthBound` on the encodings of all reachable views. -/
noncomputable def codeWidth (c d : ℕ) (input : List Bool) : ℕ :=
  (encFiniteCfg (ntm.initView input)).length +
    viewLengthBound k State input.length (c * (input.length + 1) ^ d)

/-- **Savitch's decider**: whether the accepting code is reachable from the code of the initial
view, by Savitch's midpoint recursion on words of `2 * W + 2` bits at depth `2 * W + 2`, for the
width `W` of the codes. -/
noncomputable def savitchDecide (c d : ℕ) (input : List Bool) : Bool :=
  Cslib.Reachability.savitch ntm.codeEdge (2 * ntm.codeWidth c d input + 2)
    (2 * ntm.codeWidth c d input + 2) (viewCode (ntm.codeWidth c d input) (ntm.initView input))
    (acceptCode (ntm.codeWidth c d input))

variable {ntm}

/-- **Savitch's decider decides acceptance** of a machine whose computation paths on `input`
visit at most `c * (input.length + 1) ^ d` work cells. -/
theorem savitchDecide_eq_true_iff {c d s : ℕ} {input : List Bool} (hs : ntm.RunsInSpace input s)
    (hsc : s ≤ c * (input.length + 1) ^ d) :
    ntm.savitchDecide c d input = true ↔ ntm.Accepts input := by
  set width := ntm.codeWidth c d input with hwidth_def
  have hwidth : ∀ finite, Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite →
      (encFiniteCfg finite).length ≤ width := fun finite h =>
    ((length_encFiniteCfg_le hs h).trans (viewLengthBound_mono k State _ hsc)).trans
      (Nat.le_add_left _ _)
  have hsrc : (viewCode width (ntm.initView input)).length = 2 * width + 2 :=
    length_viewCode (hwidth _ .refl)
  have hdst : (acceptCode width).length = 2 * width + 2 := List.length_replicate ..
  -- the reachable codes are words of `2 * width + 2` bits
  have hcard : {code | Relation.ReflTransGen (ntm.CodeStep width)
      (viewCode width (ntm.initView input)) code}.encard ≤ 2 ^ (2 * width + 2) + 1 := by
    refine (Set.encard_le_encard fun code hcode => ?_).trans
      ((Cslib.Kolmogorov.encard_setOf_length_eq _).le.trans le_self_add)
    induction hcode with
    | refl => exact hsrc
    | tail _ hstep _ => exact hstep.2.1
  rw [savitchDecide, ← hwidth_def, Cslib.Reachability.savitch_iff hsrc hdst,
    accepts_iff_reflTransGen_codeStep hwidth]
  exact (Relation.reflTransGen_iff_relatesWithinSteps_of_encard_le hcard).symm

/-- The width of the codes is polynomial-time, in unary. -/
theorem computableTidilyInPolyTime_codeWidth {α : Type} {enc : α ↪ List Bool} (c d : ℕ) :
    ComputableTidilyInPolyTime (fun a => ntm.codeWidth c d (enc a)) enc encUnary := by
  have hlength : ComputableTidilyInPolyTime (fun a => (enc a).length) enc encUnary :=
    (ComputableTidilyInPolyTime.length encBool (encL := encBits)).comp (.encode enc)
  have hinit := ComputableTidilyInPolyTime.finiteCfg_init (k := k) (.encode enc) ntm.q₀
  have hpow : ComputableTidilyInPolyTime (fun a => ((enc a).length + 1) ^ d) enc encUnary :=
    (ComputableTidilyInPolyTime.unary_pow d).comp
      (ComputableTidilyInPolyTime.unary_add.comp (hlength.prod (.const 1)))
  have hsum : ComputableTidilyInPolyTime
      (fun a => (enc a).length + c * ((enc a).length + 1) ^ d + 1) enc encUnary :=
    ComputableTidilyInPolyTime.unary_add.comp ((ComputableTidilyInPolyTime.unary_add.comp
      (hlength.prod (ComputableTidilyInPolyTime.unary_mul.comp
        ((ComputableTidilyInPolyTime.const c).prod hpow)))).prod
        (ComputableTidilyInPolyTime.const 1))
  simp only [codeWidth, viewLengthBound]
  exact ComputableTidilyInPolyTime.unary_add.comp
    (((ComputableTidilyInPolyTime.length encBool (encL := encBits)).comp hinit.encoded).prod
      (ComputableTidilyInPolyTime.unary_mul.comp ((ComputableTidilyInPolyTime.const _).prod hsum)))

variable (ntm) in
/-- **Savitch's decider runs in polynomial space**, tidily: within some time and within space
polynomially bounded in the length of the encoded instance. -/
theorem exists_polyBounded_space_savitchDecide {α : Type} (enc : α ↪ List Bool) (c d : ℕ) :
    ∃ t s, PolyBounded (fun a => (enc a).length) s ∧
      ComputableTidilyInTimeAndSpace (fun a => ntm.savitchDecide c d (enc a)) enc encBool t s := by
  have hwidth := computableTidilyInPolyTime_codeWidth (ntm := ntm) (enc := enc) c d
  have hcodes : ComputableTidilyInPolyTime
      (fun a => 2 * ntm.codeWidth c d (enc a) + 2) enc encUnary :=
    ComputableTidilyInPolyTime.unary_add.comp ((ComputableTidilyInPolyTime.unary_mul.comp
      ((ComputableTidilyInPolyTime.const 2).prod hwidth)).prod (ComputableTidilyInPolyTime.const 2))
  have hedge : ComputableTidilyInPolyTime
      (fun q : Unit × List Bool × List Bool => (fun _ => ntm.codeEdge) q.1 q.2.1 q.2.2)
      (encPair (encFinite Unit) (encPair encBits encBits)) encBool :=
    ntm.computableTidilyInPolyTime_codeEdge ((ComputableTidilyInPolyTime.fst _ _).comp (.snd _ _))
      ((ComputableTidilyInPolyTime.snd _ _).comp (.snd _ _))
  have hin : ComputableTidilyInPolyTime
      (fun a => ((), 2 * ntm.codeWidth c d (enc a) + 2, 2 * ntm.codeWidth c d (enc a) + 2,
        viewCode (ntm.codeWidth c d (enc a)) (ntm.initView (enc a)),
        acceptCode (ntm.codeWidth c d (enc a)))) enc
      (Cslib.Reachability.encArgs (encFinite Unit)) :=
    (ComputableTidilyInPolyTime.const ()).prod (hcodes.prod (hcodes.prod
      ((computableTidilyInPolyTime_viewCode_initView hwidth (.encode enc)).prod
        (computableTidilyInPolyTime_acceptCode hwidth))))
  exact Cslib.Reachability.exists_polyBounded_space_savitch (edge := fun _ => ntm.codeEdge)
    (par := fun _ => ()) hedge hin
    (fun _ => length_viewCode (Nat.le_add_right _ _)) fun _ => List.length_replicate ..

end Turing.MultiTapeNTM
