/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.USTCON.Reader.Encode
public import Complexity.Computability.Machines.ReadMachine.Tidy
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists

/-!
# The read machine for undirected connectivity within linear work space

The halting test, the address and the step of `Cslib.USTCON.Reader.machine` are tidily computable
within work space linear in the length of the encoded state (and the bit read): every step is a
bounded number of operations on the numbers and the heads of the lists of the state — comparisons,
successors and predecessors, products for the address, divisions by the number of labels, and
functions of the finitely many controls, labels and frames. So the step machine simulating the read
machine is tidy within space linear in its states and the position of its head
(`Cslib.USTCON.Reader.tidy_machine`).

## Main definitions

* `Cslib.USTCON.Reader.encStepIn`, `Cslib.USTCON.Reader.stepBudget`: the encoded inputs of a step
  and their length.

## Main results

* `Cslib.USTCON.Reader.halt_inSpace`, `Cslib.USTCON.Reader.addr_inSpace`,
  `Cslib.USTCON.Reader.step_inSpace`: the components of the machine within linear space.
* `Cslib.USTCON.Reader.tidy_machine`: the simulating step machine is tidy.
-/

@[expose] public section

namespace Cslib.USTCON.Reader

open Turing MultiTapeTM ComputableTidilyInSpace Cslib.RotationMap Cslib.Reachability.Reingold

/-- The encoding of the inputs of a step: the tuple and the bit read. -/
noncomputable abbrev encStepIn : Tuple × Bool ↪ List Bool :=
  encPair encTuple encBool

/-- **The space budget of a step**: the length of the encoded tuple and bit. -/
noncomputable def stepBudget (y : Tuple × Bool) : ℕ :=
  (encStepIn y).length

theorem len_le_stepBudget : (fun y => (encStepIn y).length) ≼ stepBudget :=
  .refl _

/-! ### Projections -/

section Proj

theorem hTup : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1) encStepIn encTuple
    stepBudget :=
  fst _ _

theorem hBit : ComputableTidilyInSpace (fun y : Tuple × Bool => y.2) encStepIn encBool
    stepBudget :=
  snd _ _

theorem hCtl : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.1.1) encStepIn encCtl
    stepBudget :=
  fst' (fst' hTup)

theorem hCnt : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.1.2) encStepIn encNat
    stepBudget :=
  snd' (fst' hTup)

theorem hN : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.1.1.1) encStepIn encNat
    stepBudget :=
  fst' (fst' (fst' (snd' hTup)))

theorem hS : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.1.1.2.1) encStepIn encNat
    stepBudget :=
  fst' (snd' (fst' (fst' (snd' hTup))))

theorem hT : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.1.1.2.2) encStepIn encNat
    stepBudget :=
  snd' (snd' (fst' (fst' (snd' hTup))))

theorem hDepth : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.1.2.1) encStepIn encNat
    stepBudget :=
  fst' (snd' (fst' (snd' hTup)))

theorem hLen : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.1.2.2) encStepIn encNat
    stepBudget :=
  snd' (snd' (fst' (snd' hTup)))

theorem hC : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.1.1) encStepIn encNat
    stepBudget :=
  fst' (fst' (snd' (snd' hTup)))

theorem hW : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.1.2.1) encStepIn encNat
    stepBudget :=
  fst' (snd' (fst' (snd' (snd' hTup))))

theorem hJ : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.1.2.2) encStepIn encNat
    stepBudget :=
  snd' (snd' (fst' (snd' (snd' hTup))))

theorem hV₁ : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.2.1.1) encStepIn encNat
    stepBudget :=
  fst' (fst' (snd' (snd' (snd' hTup))))

theorem hV₂ : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.2.1.2) encStepIn encNat
    stepBudget :=
  snd' (fst' (snd' (snd' (snd' hTup))))

theorem hLower : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.2.2.1) encStepIn
    (encList encLab) stepBudget :=
  fst' (snd' (snd' (snd' (snd' hTup))))

theorem hFrames : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.2.2.2) encStepIn
    (encList encFrame) stepBudget :=
  snd' (snd' (snd' (snd' (snd' hTup))))

end Proj

/-! ### Building tuples and lists within the budget -/

section Build

variable {β : Type} {encIn : β ↪ List Bool} {Bs : β → ℕ}

/-- A tuple from its components. -/
theorem mkT {ctl : β → Ctl} {cnt n s t d l c w j v₁ v₂ : β → ℕ} {low : β → List Label}
    {fr : β → List (ReingoldPc × Label)}
    (h₁ : ComputableTidilyInSpace ctl encIn encCtl Bs)
    (h₂ : ComputableTidilyInSpace cnt encIn encNat Bs)
    (h₃ : ComputableTidilyInSpace n encIn encNat Bs)
    (h₄ : ComputableTidilyInSpace s encIn encNat Bs)
    (h₅ : ComputableTidilyInSpace t encIn encNat Bs)
    (h₆ : ComputableTidilyInSpace d encIn encNat Bs)
    (h₇ : ComputableTidilyInSpace l encIn encNat Bs)
    (h₈ : ComputableTidilyInSpace c encIn encNat Bs)
    (h₉ : ComputableTidilyInSpace w encIn encNat Bs)
    (h₁₀ : ComputableTidilyInSpace j encIn encNat Bs)
    (h₁₁ : ComputableTidilyInSpace v₁ encIn encNat Bs)
    (h₁₂ : ComputableTidilyInSpace v₂ encIn encNat Bs)
    (h₁₃ : ComputableTidilyInSpace low encIn (encList encLab) Bs)
    (h₁₄ : ComputableTidilyInSpace fr encIn (encList encFrame) Bs) :
    ComputableTidilyInSpace (fun x => (((ctl x, cnt x), ((n x, s x, t x), (d x, l x)),
      ((c x, w x, j x), ((v₁ x, v₂ x), low x, fr x))) : Tuple)) encIn encTuple Bs :=
  budget_prod (budget_prod h₁ h₂) (budget_prod (budget_prod (budget_prod h₃ (budget_prod h₄ h₅))
    (budget_prod h₆ h₇)) (budget_prod (budget_prod h₈ (budget_prod h₉ h₁₀))
      (budget_prod (budget_prod h₁₁ h₁₂) (budget_prod h₁₃ h₁₄))))

/-- Adding an element in front of a list. -/
theorem consS {ε : Type} {enc : ε ↪ List Bool} {a : β → ε} {l : β → List ε}
    (ha : ComputableTidilyInSpace a encIn enc Bs)
    (hl : ComputableTidilyInSpace l encIn (encList enc) Bs) :
    ComputableTidilyInSpace (fun x => a x :: l x) encIn (encList enc) Bs :=
  budget_comp_linear (of_inO (ComputableTidilyInDegree.cons enc).inO_one) (budget_prod ha hl)

/-- The head of a list. -/
theorem headDS {ε : Type} {enc : ε ↪ List Bool} (d : ε) {l : β → List ε}
    (hl : ComputableTidilyInSpace l encIn (encList enc) Bs) :
    ComputableTidilyInSpace (fun x => (l x).headD d) encIn enc Bs :=
  budget_comp_linear (of_inO (.of_linear (ListEncoding.headD (enc := encList enc) d))) hl

/-- The tail of a list. -/
theorem tailS {ε : Type} {enc : ε ↪ List Bool} {l : β → List ε}
    (hl : ComputableTidilyInSpace l encIn (encList enc) Bs) :
    ComputableTidilyInSpace (fun x => (l x).tail) encIn (encList enc) Bs :=
  budget_comp_linear (of_inO (.of_linear (ListEncoding.tail (enc₁ := enc)))) hl

/-- Whether a list is empty. -/
theorem isEmptyS {ε : Type} {enc : ε ↪ List Bool} {l : β → List ε}
    (hl : ComputableTidilyInSpace l encIn (encList enc) Bs) :
    ComputableTidilyInSpace (fun x => (l x).isEmpty) encIn encBool Bs :=
  budget_comp_linear (of_inO (.of_linear (ListEncoding.isEmpty (enc₁ := enc)))) hl

/-- The successor. -/
theorem succS {a : β → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => a x + 1) encIn encNat Bs :=
  budget_comp_lin natSucc linear_succ ha

/-- The predecessor. -/
theorem predS {a : β → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => a x - 1) encIn encNat Bs :=
  budget_comp_lin natPred linear_succ ha

/-- Zero test. -/
theorem isZeroS {a : β → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => decide (a x = 0)) encIn encBool Bs :=
  budget_comp_lin natIsZero (.refl _) ha

/-- Equality of numbers. -/
theorem eqS {a b : β → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs)
    (hb : ComputableTidilyInSpace b encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => decide (a x = b x)) encIn encBool Bs :=
  budget_comp_lin natEq (.refl _) (budget_prod ha hb)

/-- The sum. -/
theorem addS {a b : β → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs)
    (hb : ComputableTidilyInSpace b encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => a x + b x) encIn encNat Bs :=
  budget_comp_lin natAdd linear_succ (budget_prod ha hb)

/-- The product. -/
theorem mulS {a b : β → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs)
    (hb : ComputableTidilyInSpace b encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => a x * b x) encIn encNat Bs :=
  budget_comp_lin natMul (linear_mul 32) (budget_prod ha hb)

/-- The quotient. -/
theorem divS {a b : β → ℕ} (ha : ComputableTidilyInSpace a encIn encNat Bs)
    (hb : ComputableTidilyInSpace b encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => a x / b x) encIn encNat Bs :=
  budget_comp_lin natDiv (linear_mul 16) (budget_prod ha hb)

end Build

/-! ### The halting test and the address -/

/-- The tuple with the bit `false`, as an input of a step. -/
theorem pairFalse_inSpace :
    ComputableTidilyInSpace (fun x : Tuple => (x, false)) encTuple encStepIn
      fun x => stepBudget (x, false) :=
  (budget_prod (of_inO (.of_linear (.of_eq (f := id) fun _ => rfl)))
    (budget_const (encB := encBool) false (.refl _))).weaken (.of_le fun x => by
      simp only [stepBudget, length_encPair]; omega)

/-- A function of the tuple with the bit `false`, within the budget of the step. -/
theorem onTuple {β : Type} {encB : β ↪ List Bool} {f : Tuple × Bool → β}
    (h : ComputableTidilyInSpace f encStepIn encB stepBudget) :
    ComputableTidilyInSpace (fun x : Tuple => f (x, false)) encTuple encB
      fun x => stepBudget (x, false) :=
  budget_comp h pairFalse_inSpace (.refl _)

/-- A function of the control. -/
theorem hCtlFinite {β : Type} {encB : β ↪ List Bool} (g : Ctl → β) :
    ComputableTidilyInSpace (fun y : Tuple × Bool => g y.1.1.1) encStepIn encB stepBudget :=
  budget_finite g hCtl

/-- The halting test on tuples. -/
theorem haltT_inSpace :
    ComputableTidilyInSpace (fun x : Tuple => decide (x.1.1 = .done)) encTuple encBool
      fun x => stepBudget (x, false) :=
  onTuple (hCtlFinite fun k ↦ decide (k = .done))

/-- Whether the next step of the evaluation is a step of the slot graph, from the labels and the
frames. -/
def atBaseT (low : List Label) (fr : List (ReingoldPc × Label)) : Bool :=
  !low.isEmpty && low.tail.isEmpty && !fr.isEmpty &&
    (fun p : ReingoldPc × Label ↦ decide (p.1 = .call₀) || decide (p.1 = .call₁))
      (fr.headD (.zig₀, 0))

theorem atBaseT_eq (v : ℕ × ℕ) (low : List Label) (fr : List (ReingoldPc × Label)) :
    atBaseT low fr = (⟨v, low, fr⟩ : ReingoldEvalState (ℕ × ℕ) Label).atBase := by
  rcases low with _ | ⟨b, _ | ⟨b', l⟩⟩ <;> rcases fr with _ | ⟨⟨pc, a⟩, rest⟩ <;>
    try rfl
  cases pc <;> rfl

/-- Whether the next step of the evaluation is a step of the slot graph, within the budget. -/
theorem atBaseT_inSpace : ComputableTidilyInSpace
    (fun y : Tuple × Bool ↦ atBaseT y.1.2.2.2.2.1 y.1.2.2.2.2.2) encStepIn encBool stepBudget := by
  have h₄ := budget_finite (encC := encBool)
    (fun p : ReingoldPc × Label ↦ decide (p.1 = .call₀) || decide (p.1 = .call₁))
    (headDS (ReingoldPc.zig₀, (0 : Label)) hFrames)
  exact budget_finite (encC := encBool)
    (fun q : Bool × Bool × Bool × Bool ↦ !q.1 && q.2.1 && !q.2.2.1 && q.2.2.2)
    (budget_prod (isEmptyS hLower) (budget_prod (isEmptyS (tailS hLower))
      (budget_prod (isEmptyS hFrames) h₄)))

/-- `some` of a number. -/
theorem someS {β : Type} {encIn : β ↪ List Bool} {Bs : β → ℕ} {a : β → ℕ}
    (ha : ComputableTidilyInSpace a encIn encNat Bs) :
    ComputableTidilyInSpace (fun x => some (a x)) encIn (encOption encNat) Bs :=
  budget_comp_linear (of_inO (ComputableTidilyInDegree.optionSome (enc₁ := encNat)).inO_one) ha

/-- The address on tuples. -/
theorem addrT_inSpace :
    ComputableTidilyInSpace (fun x : Tuple ↦ addr (State.ofTuple x)) encTuple (encOption encNat)
      fun x => stepBudget (x, false) := by
  have hc (k : Ctl) := hCtlFinite (encB := encBool) fun k' ↦ decide (k' = k)
  have hbase := atBaseT_inSpace
  have h := budget_ite (hc .hdrN) (someS hCnt) (budget_ite (hc .hdrS)
    (someS (addS (succS hN) hCnt)) (budget_ite (hc .hdrT)
      (someS (addS (succS (addS (succS hN) hS)) hCnt)) (budget_ite (hc .eval)
        (budget_ite hbase (someS (addS (addS (addS (addS hN hS) hT) (budget_const 3 (.refl _)))
          (addS (mulS hV₁ hN) hV₂))) (budget_const (encB := encOption encNat) none (.refl _)))
        (budget_const (encB := encOption encNat) none (.refl _)))))
  refine (onTuple h).of_enc_eq fun x ↦ ?_
  obtain ⟨⟨ctl, cnt⟩, ⟨⟨n, s, t⟩, d, l⟩, ⟨c, w, j⟩, v, low, fr⟩ := x
  cases ctl
  case eval => simp only [addr, State.ofTuple, atBaseT_eq v]; rfl
  all_goals simp [addr, State.ofTuple]

/-! ### The label of a digit, by a finite-state fold over the binary digits -/

instance : NeZero numLabels :=
  ⟨numLabels_pos.ne'⟩

/-- A step of computing a number modulo the number of labels from its binary digits, least
significant first: the residue so far and the residue of the next place value. -/
def modStep (p : ZMod numLabels × ZMod numLabels) (b : Bool) : ZMod numLabels × ZMod numLabels :=
  (p.1 + (if b then p.2 else 0), 2 * p.2)

theorem foldl_modStep (w : ℕ) :
    ∀ r q : ZMod numLabels, (w.bits.foldl modStep (r, q)).1 = r + q * w := by
  induction w using Nat.binaryRec' with
  | zero => intro r q; simp [Nat.zero_bits]
  | bit b w hb ih =>
    intro r q
    rw [Nat.bits_append_bit w b hb, List.foldl_cons, modStep, ih, Nat.bit_val]
    cases b
    · simp only [Bool.false_eq_true, ite_false, add_zero, Bool.toNat_false]
      push_cast
      ring
    · simp only [ite_true, Bool.toNat_true]
      push_cast
      ring

/-- The label of a residue. -/
noncomputable def labelOfZMod (z : ZMod numLabels) : Label :=
  labelEquiv ⟨z.val, ZMod.val_lt z⟩

/-- The label of a digit is the label of the residue computed by the fold. -/
theorem labelOfNat_eq (w : ℕ) : labelOfNat w = labelOfZMod (w.bits.foldl modStep (0, 1)).1 := by
  rw [foldl_modStep, zero_add, one_mul, labelOfZMod, labelOfNat]
  congr 2

/-- **The label of a digit** is computed by a finite-state fold over the binary digits, in constant
work space. -/
theorem labelOfNat_inSpace :
    ComputableTidilyInSpace labelOfNat encNat encLab fun w => (encNat w).length := by
  have hfold := of_inO (ComputableTidilyInO.foldl_bits_finite
    (encFinite (ZMod numLabels × ZMod numLabels)) modStep (0, 1))
  have h := hfold.of_encIn_eq (α' := ℕ) (encIn' := encNat) Nat.bits fun w ↦ by
    rw [encNat_apply, encBits_apply]
  have h' := budget_comp_linear (of_finite (encIn := encFinite (ZMod numLabels × ZMod numLabels))
    (encB := encLab) fun p : ZMod numLabels × ZMod numLabels ↦ labelOfZMod p.1) h
  exact (h'.weaken (.const 0 _)).of_enc_eq fun w ↦ by rw [labelOfNat_eq]

/-! ### The step of the evaluation -/

/-- The next program counter of a frame. -/
def nextPc : ReingoldPc → ReingoldPc
  | .zig₀ => .call₀
  | .call₀ => .zag₀
  | .zag₀ => .zig₁
  | .zig₁ => .call₁
  | .call₁ => .zag₁
  | .zag₁ => .finish
  | .finish => .finish

/-- Whether a program counter is a step of `H`. -/
def isHStep : ReingoldPc → Bool
  | .zig₀ | .zag₀ | .zig₁ | .zag₁ => true
  | _ => false

/-- Whether a program counter is a rotation of the level below. -/
def isCall : ReingoldPc → Bool
  | .call₀ | .call₁ => true
  | _ => false

/-- **The step of the evaluation, from the heads of the lists**: a step of `H` on the head label and
the label of the top frame, a rotation of the level below, as a step of the slot graph at level `1`
or a push, or the final permutation and a pop. -/
def evalStepT (n : ℕ) (bit : Bool) (v : ℕ × ℕ) (low : List Label)
    (fr : List (ReingoldPc × Label)) : (ℕ × ℕ) × List Label × List (ReingoldPc × Label) :=
  if low.isEmpty || fr.isEmpty then (v, low, fr)
  else if isHStep (fr.headD (.zig₀, 0)).1 then
    ((v, (reingoldHStep base baseEquiv (fr.headD (.zig₀, 0)).1
        (low.headD 0, (fr.headD (.zig₀, 0)).2)).1 :: low.tail,
      (nextPc (fr.headD (.zig₀, 0)).1, (reingoldHStep base baseEquiv (fr.headD (.zig₀, 0)).1
        (low.headD 0, (fr.headD (.zig₀, 0)).2)).2) :: fr.tail))
  else if isCall (fr.headD (.zig₀, 0)).1 then
    if low.tail.isEmpty then
      ((baseRotN n v (low.headD 0) bit).1, (baseRotN n v (low.headD 0) bit).2 :: low.tail,
        (nextPc (fr.headD (.zig₀, 0)).1, (fr.headD (.zig₀, 0)).2) :: fr.tail)
    else
      (v, low.tail, (.zig₀, low.headD 0) ::
        (nextPc (fr.headD (.zig₀, 0)).1, (fr.headD (.zig₀, 0)).2) :: fr.tail)
  else (v, reingoldFinish baseEquiv (fr.headD (.zig₀, 0)).2 :: low, fr.tail)

theorem evalStepT_eq (n : ℕ) (bit : Bool) (s : ReingoldEvalState (ℕ × ℕ) Label) :
    evalStepT n bit s.vertex s.lower s.frames =
      ((reingoldEvalStep base baseEquiv (evalBase n bit) s).vertex,
        (reingoldEvalStep base baseEquiv (evalBase n bit) s).lower,
        (reingoldEvalStep base baseEquiv (evalBase n bit) s).frames) := by
  obtain ⟨v, _ | ⟨b, l⟩, _ | ⟨⟨pc, a⟩, rest⟩⟩ := s
  all_goals try rfl
  cases pc <;> by_cases hl : l = [] <;> simp [evalStepT, reingoldEvalStep, isHStep, isCall, nextPc,
    evalBase, hl]

theorem hVert : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.2.1) encStepIn
    (encPair encNat encNat) stepBudget :=
  fst' (snd' (snd' (snd' hTup)))

/-- The head label below the frames. -/
theorem hHeadLab : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.2.2.1.headD 0)
    encStepIn encLab stepBudget :=
  headDS 0 hLower

/-- The top frame. -/
theorem hTop : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.2.2.2.headD (.zig₀, 0))
    encStepIn encFrame stepBudget :=
  headDS _ hFrames

/-- **The step of the slot graph** on the slot, the head label and the bit read. -/
theorem baseRotN_inSpace : ComputableTidilyInSpace
    (fun y : Tuple × Bool => baseRotN y.1.2.1.1.1 y.1.2.2.2.1 (y.1.2.2.2.2.1.headD 0) y.2)
    encStepIn (encPair (encPair encNat encNat) encLab) stepBudget := by
  have ht (d : SlotLabel) := budget_finite (encC := encBool)
    (fun b : Label ↦ decide (b = slotLabel d)) hHeadLab
  have hc (d : SlotLabel) := budget_const (encB := encLab) (encIn := encStepIn) (Bs := stepBudget)
    (slotLabel d) (.refl _)
  have h := budget_ite (ht (.inl ()))
    (budget_prod (budget_ite hBit (budget_prod hV₂ hV₁) hVert) hHeadLab)
    (budget_ite (ht (.inr ((), (), false)))
      (budget_prod (budget_prod hV₁ (budget_ite (eqS (succS hV₂) hN)
        (budget_const (encB := encNat) 0 (.refl _)) (succS hV₂))) (hc (.inr ((), (), true))))
      (budget_ite (ht (.inr ((), (), true)))
        (budget_prod (budget_prod hV₁ (budget_ite (isZeroS hV₂) (predS hN) (predS hV₂)))
          (hc (.inr ((), (), false))))
        (budget_prod hVert hHeadLab)))
  exact h.of_enc_eq fun y ↦ by simp only [baseRotN, decide_eq_true_eq]

/-- **The step of the evaluation** within the budget. -/
theorem evalStepT_inSpace : ComputableTidilyInSpace
    (fun y : Tuple × Bool => evalStepT y.1.2.1.1.1 y.2 y.1.2.2.2.1 y.1.2.2.2.2.1 y.1.2.2.2.2.2)
    encStepIn encEval stepBudget := by
  have hl := tailS hLower
  have hrest := tailS hFrames
  have hH := budget_finite (encC := encPair encLab encLab)
    (fun p : (ReingoldPc × Label) × Label ↦ reingoldHStep base baseEquiv p.1.1 (p.2, p.1.2))
    (budget_prod hTop hHeadLab)
  have hnew := budget_finite (encC := encFrame)
    (fun p : (ReingoldPc × Label) × (Label × Label) ↦ (nextPc p.1.1, p.2.2)) (budget_prod hTop hH)
  have hnext := budget_finite (encC := encFrame)
    (fun p : ReingoldPc × Label ↦ (nextPc p.1, p.2)) hTop
  have hpush := budget_finite (encC := encFrame) (fun b : Label ↦ (ReingoldPc.zig₀, b)) hHeadLab
  have hfin := budget_finite (encC := encLab) (fun p : ReingoldPc × Label ↦
    reingoldFinish baseEquiv p.2) hTop
  have hempty := budget_finite (encC := encBool) (fun q : Bool × Bool ↦ q.1 || q.2)
    (budget_prod (isEmptyS hLower) (isEmptyS hFrames))
  have h := budget_ite hempty (budget_prod hVert (budget_prod hLower hFrames))
    (budget_ite (budget_finite (encC := encBool) (fun p : ReingoldPc × Label ↦ isHStep p.1) hTop)
      (budget_prod hVert (budget_prod (consS (fst' hH) hl) (consS hnew hrest)))
      (budget_ite (budget_finite (encC := encBool) (fun p : ReingoldPc × Label ↦ isCall p.1) hTop)
        (budget_ite (isEmptyS hl)
          (budget_prod (fst' baseRotN_inSpace)
            (budget_prod (consS (snd' baseRotN_inSpace) hl) (consS hnext hrest)))
          (budget_prod hVert (budget_prod hl (consS hpush (consS hnext hrest)))))
        (budget_prod hVert (budget_prod (consS hfin hLower) hrest))))
  exact h.of_enc_eq fun y ↦ rfl

/-! ### The step -/

/-- The step on tuples. -/
noncomputable def stepT (y : Tuple × Bool) : Tuple × List Bool :=
  ((step (State.ofTuple y.1) y.2).1.toTuple, (step (State.ofTuple y.1) y.2).2)

/-- The length of a list of labels. -/
theorem lengthS {β : Type} {encIn : β ↪ List Bool} {Bs : β → ℕ} {l : β → List Label}
    (hl : ComputableTidilyInSpace l encIn (encList encLab) Bs) :
    ComputableTidilyInSpace (fun x => (l x).length) encIn encNat Bs :=
  budget_comp_lin (length (enc := encLab)) (linear_mul 8) hl

/-- **The step on tuples** within the budget. -/
theorem stepT_inSpace : ComputableTidilyInSpace stepT encStepIn (encPair encTuple encBits)
    stepBudget := by
  have hc (k : Ctl) := hCtlFinite (encB := encBool) fun k' ↦ decide (k' = k)
  have cctl (k : Ctl) := budget_const (encB := encCtl) (encIn := encStepIn) (Bs := stepBudget) k
    (.refl _)
  have cnat (a : ℕ) := budget_const (encB := encNat) (encIn := encStepIn) (Bs := stepBudget) a
    (.refl _)
  have nil := budget_const (encB := encBits) (encIn := encStepIn) (Bs := stepBudget) [] (.refl _)
  have T₁ := mkT hCtl (succS hCnt) hN hS hT hDepth hLen hC hW hJ hV₁ hV₂ hLower hFrames
  have keep (k : Ctl) := mkT (cctl k) hCnt hN hS hT hDepth hLen hC hW hJ hV₁ hV₂ hLower hFrames
  have hdrN := budget_ite hBit (budget_prod T₁ nil) (budget_prod (mkT (cctl .hdrS) (cnat 0) hCnt
    hS hT hDepth hLen hC hW hJ hV₁ hV₂ hLower hFrames) nil)
  have hdrS := budget_ite hBit (budget_prod T₁ nil) (budget_prod (mkT (cctl .hdrT) (cnat 0) hN
    hCnt hT hDepth hLen hC hW hJ hV₁ hV₂ hLower hFrames) nil)
  have hdrT := budget_ite hBit (budget_prod T₁ nil) (budget_prod (mkT (cctl .size) hN hN hS hCnt
    (cnat 524) (cnat 136240) hC hW hJ hV₁ hV₂ hLower hFrames) nil)
  have size := budget_ite (isZeroS hCnt)
    (budget_prod (mkT (cctl .start) hCnt hN hS hT hDepth hLen (cnat 0) hW hJ hV₁ hV₂ hLower
      hFrames) nil)
    (budget_prod (mkT hCtl (divS hCnt (cnat 2)) hN hS hT (addS hDepth (cnat 16))
      (addS hLen (cnat 4168)) hC hW hJ hV₁ hV₂ hLower hFrames) nil)
  have start := budget_prod (mkT (cctl .fill) hCnt hN hS hT hDepth hLen hC hC hLen hS hS
    (budget_const (encB := encList encLab) [] (.refl _))
    (budget_const (encB := encList encFrame) [] (.refl _))) nil
  have fill := budget_ite (eqS (lengthS hLower) hDepth) (budget_prod (keep .next) nil)
    (budget_prod (mkT hCtl hCnt hN hS hT hDepth hLen hC hW hJ hV₁ hV₂
      (consS (budget_const (encB := encLab) (0 : Label) (.refl _)) hLower) hFrames) nil)
  have hlab := budget_comp_lin labelOfNat_inSpace (.refl _) hW
  have next := budget_ite (isZeroS hJ) (budget_prod (keep .check) nil)
    (budget_prod (mkT (cctl .eval) hCnt hN hS hT hDepth hLen hC (divS hW (cnat numLabels))
      (predS hJ) hV₁ hV₂ hLower (consS (budget_finite (encC := encFrame)
        (fun l : Label ↦ (ReingoldPc.zig₀, l)) hlab)
        (budget_const (encB := encList encFrame) [] (.refl _)))) nil)
  have eval := budget_ite (isEmptyS hFrames)
    (budget_prod (mkT (cctl .next) hCnt hN hS hT hDepth hLen hC hW hJ hV₁ hV₂ (tailS hLower)
      hFrames) nil)
    (budget_prod (mkT hCtl hCnt hN hS hT hDepth hLen hC hW hJ
      (fst' (fst' evalStepT_inSpace)) (snd' (fst' evalStepT_inSpace))
      (fst' (snd' evalStepT_inSpace)) (snd' (snd' evalStepT_inSpace))) nil)
  have check := budget_ite (budget_finite (encC := encBool) not (isZeroS hW))
    (budget_prod (keep .done) (budget_const (encB := encBits) [false] (.refl _)))
    (budget_ite (eqS hV₁ hT)
      (budget_prod (keep .done) (budget_const (encB := encBits) [true] (.refl _)))
      (budget_prod (mkT (cctl .start) hCnt hN hS hT hDepth hLen (succS hC) hW hJ hV₁ hV₂ hLower
        hFrames) nil))
  have done := budget_prod hTup nil
  have h := budget_ite (hc .hdrN) hdrN (budget_ite (hc .hdrS) hdrS (budget_ite (hc .hdrT) hdrT
    (budget_ite (hc .size) size (budget_ite (hc .start) start (budget_ite (hc .fill) fill
      (budget_ite (hc .next) next (budget_ite (hc .eval) eval (budget_ite (hc .check) check
        done))))))))
  refine h.of_enc_eq fun y ↦ ?_
  obtain ⟨⟨⟨ctl, cnt⟩, ⟨⟨n, s, t⟩, d, l⟩, ⟨c, w, j⟩, v, low, fr⟩, b⟩ := y
  congr 1
  cases ctl
  case eval =>
    by_cases hfr : fr = []
    · simp [stepT, step, State.ofTuple, State.toTuple, hfr]
    · have he := evalStepT_eq n b ⟨v, low, fr⟩
      simp only at he
      simp [stepT, step, State.ofTuple, State.toTuple, hfr, he]
  case size => by_cases h : cnt = 0 <;> simp [stepT, step, State.ofTuple, State.toTuple, h]
  case fill => by_cases h : low.length = d <;> simp [stepT, step, State.ofTuple, State.toTuple, h]
  case next => by_cases h : j = 0 <;> simp [stepT, step, State.ofTuple, State.toTuple, h]
  case check =>
    obtain ⟨v₁, v₂⟩ := v
    by_cases hw : w = 0
    · by_cases hv : v₁ = t
      · subst hv
        simp [stepT, step, State.ofTuple, State.toTuple, hw]
      · simp [stepT, step, State.ofTuple, State.toTuple, hw, hv]
    · simp [stepT, step, State.ofTuple, State.toTuple, hw]
  all_goals cases b <;> simp [stepT, step, State.ofTuple, State.toTuple]

/-! ### On states -/

/-- **The space budget of a state**: the length of its encoded tuple with a bit. -/
noncomputable def stateBudget (q : State) : ℕ :=
  stepBudget (q.toTuple, false)

theorem stepBudget_bool (x : Tuple) (b : Bool) : stepBudget (x, b) = stepBudget (x, false) := by
  cases b <;> simp [stepBudget, encBool_apply]

theorem halt_inSpace : ComputableTidilyInSpace machine.halt encState encBool stateBudget :=
  (haltT_inSpace.of_encIn_eq State.toTuple fun _ ↦ rfl).of_enc_eq fun _ ↦ rfl

theorem addr_inSpace : ComputableTidilyInSpace machine.addr encState (encOption encNat)
    stateBudget :=
  (addrT_inSpace.of_encIn_eq State.toTuple fun _ ↦ rfl).of_enc_eq fun _ ↦ rfl

theorem step_inSpace :
    ComputableTidilyInSpace (fun p : State × Bool => machine.step p.1 p.2)
      (encPair encState encBool) (encPair encState encBits) fun p => stateBudget p.1 := by
  have h := stepT_inSpace.of_encIn_eq (α' := State × Bool) (encIn' := encPair encState encBool)
    (fun p ↦ (p.1.toTuple, p.2)) fun _ ↦ rfl
  refine (h.mono_le fun p ↦ ?_).of_enc_eq fun _ ↦ rfl
  rw [stateBudget, stepBudget_bool]

/-- **The step machine simulating the read machine is tidy**, within the space of its states
together with the position of its head. -/
theorem tidy_machine : ∃ T, machine.toStepMachine.Tidy (encPair encState encNat)
    (ReadMachine.stateT encState T stateBudget) (ReadMachine.stateS encState stateBudget) := by
  obtain ⟨T₁, h₁⟩ := halt_inSpace
  obtain ⟨T₂, h₂⟩ := addr_inSpace
  obtain ⟨T₃, h₃⟩ := step_inSpace
  let T : State → ℕ := fun s => T₁ s + T₂ s + T₃ (s, false) + T₃ (s, true)
  exact ⟨T, ReadMachine.tidy_toStepMachine (h₁.mono_le (fun s => by simp only [T]; omega)
    fun _ => le_rfl) (h₂.mono_le (fun s => by simp only [T]; omega) fun _ => le_rfl)
    (h₃.mono_le (fun p => by rcases p with ⟨s, _ | _⟩ <;> simp only [T] <;> omega)
      fun _ => le_rfl)⟩

end Cslib.USTCON.Reader
