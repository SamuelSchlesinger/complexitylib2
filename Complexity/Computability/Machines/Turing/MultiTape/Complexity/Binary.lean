/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Binary counters

Natural numbers in binary (`Turing.MultiTapeTM.encNat`) can be incremented, decremented and tested
for zero within time quadratic and space linear in the number of digits. The decrement subtracts
the borrow digit by digit and then drops a leading zero. A binary counter, counted down to zero,
iterates a function within the space of a round, plus the length of the counter.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInO.natSucc`, `.natPred`, `.natIsZero`: the successor, the
  predecessor and the zero test in binary.
* `Turing.MultiTapeTM.ComputableTidilyInO.iterate`: iterating a function a number of times given in
  binary, within the space of a round and logarithmic space for the counter.
-/

namespace Turing.MultiTapeTM

namespace NatPred

/-- Subtracts a borrow from the binary digits `l`, least significant first, keeping a leading
zero. -/
@[expose] public def decr : List Bool → List Bool
  | [] => []
  | true :: l => false :: l
  | false :: l => true :: decr l

/-- Drops a leading zero, the last digit. -/
@[expose] public def norm (l : List Bool) : List Bool :=
  if l.getLast? = some false then l.dropLast else l

lemma norm_cons {l : List Bool} (hl : l ≠ []) (b : Bool) : norm (b :: l) = b :: norm l := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr hl)
  simp only [norm, List.getLast?_cons, hx, Option.getD_some, List.dropLast_cons_of_ne_nil hl]
  split_ifs <;> rfl

lemma bits_ne_nil {m : ℕ} (hm : m ≠ 0) : m.bits ≠ [] := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · rw [Nat.bit0_bits k (by omega)]; simp
  · rw [Nat.bit1_bits]; simp

lemma decr_ne_nil {l : List Bool} (hl : l ≠ []) : decr l ≠ [] := by
  rcases l with _ | ⟨_ | _, l⟩ <;> simp_all [decr]

lemma norm_bits (n : ℕ) : norm n.bits = n.bits := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · rfl
      · rw [Nat.bit0_bits m (by omega), norm_cons (bits_ne_nil (by omega)), ih m (by omega)]
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · rfl
      · rw [Nat.bit1_bits, norm_cons (bits_ne_nil (by omega)), ih m (by omega)]

public lemma bits_pred (n : ℕ) : (n - 1).bits = norm (decr n.bits) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · rfl
      · rw [Nat.bit0_bits m (by omega), decr, show 2 * m - 1 = 2 * (m - 1) + 1 by omega,
          Nat.bit1_bits, ih m (by omega), norm_cons (decr_ne_nil (bits_ne_nil (by omega)))]
    · rw [Nat.bit1_bits, decr, Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rfl
      · rw [Nat.bit0_bits m (by omega), norm_cons (bits_ne_nil (by omega)), norm_bits]

/-- One round of the decrement: subtract the borrow from the digit `b`, append the result and keep
the borrow. -/
@[expose] public def decrStep (p : Bool × List Bool) (b : Bool) : Bool × List Bool :=
  (p.1 && !b, p.2 ++ [p.1 ^^ b])

lemma length_decr (l : List Bool) : (decr l).length = l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [decr, ih]

lemma foldl_decrStep (l : List Bool) (c : Bool) (out : List Bool) :
    (l.foldl decrStep (c, out)).2 = out ++ if c then decr l else l := by
  induction l generalizing c out with
  | nil => cases c <;> simp [decr]
  | cons b l ih => cases c <;> cases b <;> simp [decrStep, ih, decr]

/-- One round of dropping a leading zero: append the pending digit and keep the new one. -/
@[expose] public def normStep (p : Option Bool × List Bool) (b : Bool) :
    Option Bool × List Bool :=
  (some b, p.2 ++ p.1.toList)

/-- Appends the pending digit unless it is a zero. -/
@[expose] public def normFinish (p : Option Bool × List Bool) : List Bool :=
  if p.1 = some true then p.2 ++ [true] else p.2

lemma length_foldl_normStep (l : List Bool) (p : Option Bool) (acc : List Bool) :
    (l.foldl normStep (p, acc)).2.length ≤ acc.length + p.toList.length + l.length := by
  induction l generalizing p acc with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, normStep]
    have := ih (some b) (acc ++ p.toList)
    simp only [Option.toList_some, List.length_append, List.length_cons, List.length_nil]
      at this ⊢
    omega

lemma normFinish_foldl (l : List Bool) (p : Option Bool) (acc : List Bool) :
    normFinish (l.foldl normStep (p, acc)) = acc ++ norm (p.toList ++ l) := by
  induction l generalizing p acc with
  | nil => rcases p with _ | _ | _ <;> simp [normFinish, norm]
  | cons b l ih =>
    rw [List.foldl_cons, normStep, ih]
    rcases p with _ | p
    · simp
    · simp [norm_cons]

end NatPred

/-! ### The rounds, in linear time -/

section Rounds

open ComputableTidilyInDegree NatPred

lemma decrStep_deg :
    ComputableTidilyInDegree (fun p : (Bool × List Bool) × Bool => decrStep p.1 p.2)
    (encPair (encPair encBool encBits) encBool) (encPair encBool encBits) 1 1 := by
  have hacc := fst (encPair encBool encBits) encBool
  have hb := snd (encPair encBool encBits) encBool
  have hc := hacc.fst'
  have hbor := (of_finite (encIn := encPair encBool encBool) (encMid := encBool)
    fun q : Bool × Bool => q.1 && !q.2).comp (hc.prod hb)
  have hdig := (of_finite (encIn := encPair encBool encBool) (encMid := encBool)
    fun q : Bool × Bool => q.1 ^^ q.2).comp (hc.prod hb)
  exact (hbor.prod (hacc.snd'.append hdig (encOut := encBits) fun _ => rfl)).mono

lemma normStep_deg :
    ComputableTidilyInDegree (fun p : (Option Bool × List Bool) × Bool => normStep p.1 p.2)
      (encPair (encPair (encOption encBool) encBits) encBool)
      (encPair (encOption encBool) encBits) 1 1 := by
  have hacc := fst (encPair (encOption encBool) encBits) encBool
  have hb := snd (encPair (encOption encBool) encBits) encBool
  have hpend := (of_linear (.of_tail (encIn := encOption encBool) (encOut := encBits)
    (f := fun o : Option Bool => o.toList) fun o => by cases o <;> rfl)).comp hacc.fst'
  exact (((optionSome (enc₁ := encBool)).comp hb).prod
    (hacc.snd'.append hpend (encOut := encBits) fun _ => rfl)).mono

lemma normFinish_deg :
    ComputableTidilyInDegree normFinish (encPair (encOption encBool) encBits) encBits 1 1 := by
  have hp := fst (encOption encBool) encBits
  have hds := snd (encOption encBool) encBits
  have htest := (of_finite (encIn := encOption encBool) (encMid := encBool)
    fun o : Option Bool => decide (o = some true)).comp hp
  have happ := hds.append (const (encMid := encBool) true) (encOut := encBits)
    (g := fun p : Option Bool × List Bool => p.2 ++ [true]) fun _ => rfl
  convert (htest.ite (happ.restrict _) (hds.restrict _)).mono (d' := 1) (e' := 1) using 1
  funext p
  simp [normFinish]

end Rounds

namespace ComputableTidilyInO

open NatPred

variable {α : Type} {encIn : α ↪ List Bool}

/-- A fold over binary digits, with rounds in linear time, is within time quadratic and space
linear in the number of digits. -/
lemma foldl_bits {β : Type} {encB : β ↪ List Bool} {init : β} {step : β → Bool → β}
    {e : ℕ}
    (hstep : ComputableTidilyInDegree (fun p : β × Bool => step p.1 p.2)
      (encPair encB encBool) encB 1 e) (b : ℕ)
    (hb : ∀ (l : List Bool) i, (encB ((l.take i).foldl step init)).length ≤ l.length + b) :
    ComputableTidilyInO (fun l : List Bool => l.foldl step init) encBits encB
      (fun l => (l.length + 1) ^ 2) fun l => l.length + 1 := by
  refine (foldl (encA := encBool) (encL := encBits) (of_linear (.of_eq fun _ => rfl)) (const init)
    hstep.inO_one (R := fun l => 2 * l.length + 2 * b + 4)
    (Q := fun l => 2 * l.length + 2 * b + 4) (B := fun l => l.length + b)
    (fun l i _ => by have := hb l i; simp; omega) (fun l i _ => by have := hb l i; simp; omega)
    fun l i _ => hb l i).mono (4 * b + 8) (fun l => ?_) fun l => ?_
  · simp only [encBits_apply]
    nlinarith [Nat.zero_le (b * l.length)]
  · simp only [encBits_apply]
    nlinarith

lemma length_incr_le (c : Bool) (l : List Bool) : (NatSucc.incr c l).length ≤ l.length + 1 := by
  induction l generalizing c with
  | nil => cases c <;> simp [NatSucc.incr]
  | cons b l ih => cases c <;> cases b <;> simp [NatSucc.incr, ih]

/-- The successor in binary. -/
public theorem natSucc :
    ComputableTidilyInO (· + 1) encNat encNat (fun n => ((encNat n).length + 1) ^ 2)
      fun n => (encNat n).length + 1 := by
  obtain ⟨c, h⟩ := computableTidilyInTimeAndSpace_succ
  refine of_bounds h (c + 2) (fun n => by nlinarith) (fun n => by nlinarith) fun n => ?_
  have := length_incr_le true n.bits
  simp only [encNat_apply, NatSucc.bits_succ] at this ⊢
  nlinarith

/-- The predecessor in binary, `0 - 1 = 0`. -/
public theorem natPred :
    ComputableTidilyInO (· - 1) encNat encNat (fun n => ((encNat n).length + 1) ^ 2)
      fun n => (encNat n).length + 1 := by
  have hbits : ComputableTidilyInO (fun n : ℕ => n.bits) encNat encBits
      (fun n => (encNat n).length) fun n => (encNat n).length :=
    of_linear (.of_eq fun _ => rfl)
  have hlen (l : List Bool) : ((l.foldl decrStep (true, [])).2).length = l.length := by
    rw [foldl_decrStep]
    simp [length_decr]
  have hdecr := foldl_bits (init := (true, [])) decrStep_deg 3 fun l i => by
    have := hlen (l.take i)
    have := List.length_take_le' i l
    simp only [length_encPair, encBool_apply, List.length_singleton, encBits_apply]
    omega
  have hnorm := foldl_bits (init := (none, [])) normStep_deg 5 fun l i => by
    have h₁ := length_foldl_normStep (l.take i) none []
    have h₂ := List.length_take_le' i l
    have h₃ : (encOption encBool ((l.take i).foldl normStep (none, [])).1).length ≤ 2 := by
      cases ((l.take i).foldl normStep (none, [])).1 <;> simp
    simp only [length_encPair, encBits_apply] at h₁ ⊢
    simp at h₁
    omega
  refine ((normFinish_deg.inO_one.comp_linear (hnorm.comp (hdecr.comp hbits).snd')).mono 4
    (fun n => ?_) fun n => ?_).of_enc_eq fun n => ?_
  · simp only [Function.comp_apply, hlen, encNat_apply]
    nlinarith
  · simp only [Function.comp_apply, hlen, encNat_apply]
    omega
  · simp [NatPred.bits_pred, normFinish_foldl, foldl_decrStep]

/-- The zero test in binary. -/
public theorem natIsZero :
    ComputableTidilyInO (fun n => decide (n = 0)) encNat encBool (fun n => (encNat n).length)
      fun n => (encNat n).length :=
  of_linear (.of_isEmpty fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rfl
    · simp [bits_ne_nil (Nat.pos_iff_ne_zero.mp hn), hn.ne'])

/-! ### Iterating with a binary counter -/

section Iterate

variable {γ β : Type} [Inhabited β] {encIn : γ ↪ List Bool} {encB : β ↪ List Bool}

/-- A round of the counted iteration: stop at zero, otherwise count down and apply `step`. -/
@[expose] public def countStep (step : β → β) : Option (ℕ × β) → Option (ℕ × β)
  | some (i + 1, b) => some (i, step b)
  | _ => none

lemma countStep_eq (step : β → β) (o : Option (ℕ × β)) : countStep step o =
    if o.isSome && !decide ((o.getD default).1 = 0) then
      some ((o.getD default).1 - 1, step (o.getD default).2) else none := by
  rcases o with _ | ⟨_ | i, b⟩ <;> rfl

omit [Inhabited β] in
lemma iterate_countStep (step : β → β) (t : ℕ) (b : β) {k : ℕ} (hk : k ≤ t) :
    (countStep step)^[k] (some (t, b)) = some (t - k, step^[k] b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (by omega), show t - k = t - (k + 1) + 1 by omega,
      countStep, Function.iterate_succ_apply']

/-- The length of `encNat` is monotone. -/
public lemma length_encNat_mono {m n : ℕ} (h : m ≤ n) : (encNat m).length ≤ (encNat n).length := by
  simpa [Nat.size_eq_bits_len] using Nat.size_le_size h

/-- A round of the counted iteration. -/
lemma countStep_inO {step : β → β} {Ts Ss : β → ℕ}
    (hstep : ComputableTidilyInO step encB encB Ts Ss) :
    ComputableTidilyInO (countStep step) (encOption (encPair encNat encB))
      (encOption (encPair encNat encB))
      (fun o => (encOption (encPair encNat encB) o).length +
        ((encNat (o.getD default).1).length + 1) ^ 2 + Ts (o.getD default).2)
      fun o => (encOption (encPair encNat encB) o).length + Ss (o.getD default).2 := by
  have hget := (ComputableTidilyInDegree.getD (enc₁ := encPair encNat encB)
    (enc := encOption (encPair encNat encB)) default).inO_one
  have hcond := (ComputableTidilyInDegree.of_finite (encIn := encPair encBool encBool)
    (encMid := encBool) fun q : Bool × Bool => q.1 && !q.2).inO_one.comp_linear
    ((ComputableTidilyInDegree.isSome (encPair encNat encB)).inO_one.prod
      (natIsZero.comp_linear hget.fst'))
  have hnext := (ComputableTidilyInDegree.optionSome (enc₁ := encPair encNat encB)
    (enc := encOption (encPair encNat encB))).inO_one.comp_linear
    ((natPred.comp hget.fst').prod (hstep.comp hget.snd'))
  refine ((hcond.ite hnext (const none)).mono 8 (fun o => ?_) fun o => ?_).of_enc_eq
    fun o => by rw [countStep_eq]; rfl
  all_goals
    have h₁ : (encNat (o.getD default).1).length + 1 ≤
        (encOption (encPair encNat encB) o).length + 1 := by
      rcases o with _ | ⟨i, b⟩
      · simp only [Option.getD_none, encOption_none]
        exact Nat.le_of_eq (congrArg (·.length + 1) Nat.zero_bits)
      · simp only [Option.getD_some, encOption_some, List.length_cons, length_encPair]; omega
    simp only [Function.comp_apply]
    split_ifs <;> omega

lemma sum_le {c₀ c₁ k k' A M X Y : ℕ} (hX : X ≤ k * (M + 1)) (hY : Y ≤ c₀ * (A + 1)) :
    c₀ * (A + 1) + X + c₁ * (Y + 1) ≤ (c₀ + c₁ * (c₀ + 1) + k + k') * (A + M + 1) := by
  have h₁ : c₁ * (Y + 1) ≤ c₁ * (c₀ + 1) * (A + M + 1) :=
    calc c₁ * (Y + 1) ≤ c₁ * (c₀ * (A + 1) + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ c₁ * ((c₀ + 1) * (A + M + 1)) := Nat.mul_le_mul_left _ (by nlinarith)
      _ = _ := by ring
  have h₂ : X ≤ k * (A + M + 1) := hX.trans (Nat.mul_le_mul_left _ (by omega))
  have h₃ : c₀ * (A + 1) ≤ c₀ * (A + M + 1) := Nat.mul_le_mul_left _ (by omega)
  have : (c₀ + c₁ * (c₀ + 1) + k + k') * (A + M + 1) = c₀ * (A + M + 1) +
      c₁ * (c₀ + 1) * (A + M + 1) + k * (A + M + 1) + k' * (A + M + 1) := by ring
  omega

/-- **Iterating `n x` times, with `n x` in binary.** If the rounds are within the time `R x` and
the space `Q x`, and the iterates have length at most `B x`, the iteration takes the time of the
counter and of the start, plus `R x`, `B x` and the square of the length of the counter for every
round, and the space of the counter and of the start, plus `Q x`, `B x` and the length of the
counter. -/
public theorem iterate {n : γ → ℕ} {init : γ → β} {step : β → β}
    {Tn Ti Sn Si R Q B : γ → ℕ} {Ts Ss : β → ℕ}
    (hn : ComputableTidilyInO n encIn encNat Tn Sn)
    (hinit : ComputableTidilyInO init encIn encB Ti Si)
    (hstep : ComputableTidilyInO step encB encB Ts Ss)
    (hround : ∀ x, ∀ k ≤ n x, Ts (step^[k] (init x)) ≤ R x)
    (hspace : ∀ x, ∀ k ≤ n x, Ss (step^[k] (init x)) ≤ Q x)
    (hstate : ∀ x, ∀ k ≤ n x, (encB (step^[k] (init x))).length ≤ B x) :
    ComputableTidilyInO (fun x => step^[n x] (init x)) encIn encB
      (fun x => Tn x + Ti x + (n x + 1) * (R x + B x + ((encNat (n x)).length + 1) ^ 2))
      fun x => Sn x + Si x + Q x + B x + (encNat (n x)).length := by
  -- the iteration on `Option (ℕ × β)`, until the counter is exhausted
  obtain ⟨c, hf, -⟩ := countStep_inO (Ts := Ts) (Ss := Ss) hstep
  have hr (o : Option (ℕ × β)) :
      IsLeast {m | encOption (encPair encNat encB) ((countStep step)^[m + 1] o) = []}
        ((o.map Prod.fst).getD 0) := by
    rcases o with _ | ⟨t, b⟩
    · refine ⟨rfl, fun _ _ => Nat.zero_le _⟩
    · refine ⟨?_, fun m hm => ?_⟩
      · simp only [Set.mem_ofPred_eq, Option.map_some, Option.getD_some]
        rw [Function.iterate_succ_apply', iterate_countStep step t b le_rfl, Nat.sub_self]
        rfl
      · by_contra hlt
        simp only [Set.mem_ofPred_eq, Option.map_some, Option.getD_some, not_le] at hm hlt
        rw [iterate_countStep step t b hlt] at hm
        simp at hm
  obtain ⟨d, hit⟩ := hf.iterateWhile hr
  -- the start, and its iterates
  have hstart := (ComputableTidilyInDegree.optionSome (enc₁ := encPair encNat encB)
    (enc := encOption (encPair encNat encB))).inO_one.comp_linear (hn.prod hinit)
  obtain ⟨c₀, h₀, l₀⟩ := hstart
  -- vendored: crei's `comp` is `comp_linear` here, as cslib #1111 restates `comp`
  obtain ⟨c₁, h⟩ := hit.comp_linear h₀
  have hiter (x : γ) {k : ℕ} (hk : k ≤ n x) :
      (countStep step)^[k] (some (n x, init x)) = some (n x - k, step^[k] (init x)) :=
    iterate_countStep step _ _ hk
  have hlen (x : γ) {k : ℕ} (hk : k ≤ n x) :
      ((encOption (encPair encNat encB)) ((countStep step)^[k] (some (n x, init x)))).length ≤
        2 * (encNat (n x)).length + B x + 2 := by
    rw [hiter x hk]
    have := length_encNat_mono (Nat.sub_le (n x) k)
    have := hstate x k hk
    simp only [encOption_some, List.length_cons, length_encPair]
    omega
  have hcount (x : γ) {k : ℕ} (hk : k ≤ n x) :
      (encNat (((countStep step)^[k] (some (n x, init x))).getD default).1).length ≤
        (encNat (n x)).length := by
    rw [hiter x hk]
    exact length_encNat_mono (Nat.sub_le (n x) k)
  -- the bounds of the rounds and of the iterates
  have hrx (x : γ) : ((some (n x, init x)).map Prod.fst).getD 0 = n x := rfl
  have hT (x : γ) : (Finset.Iic (n x)).sup (fun k => c *
      ((encOption (encPair encNat encB) ((countStep step)^[k] (some (n x, init x)))).length +
      ((encNat (((countStep step)^[k] (some (n x, init x))).getD default).1).length + 1) ^ 2 +
      Ts (((countStep step)^[k] (some (n x, init x))).getD default).2 + 1)) ≤
      c * (2 * (encNat (n x)).length + B x + 2 + ((encNat (n x)).length + 1) ^ 2 + R x + 1) :=
    Finset.sup_le fun k hk => by
      have hk := Finset.mem_Iic.mp hk
      have h₁ := hlen x hk
      have h₂ := Nat.pow_le_pow_left (Nat.add_le_add_right (hcount x hk) 1) 2
      have h₃ := hround x k hk
      rw [hiter x hk] at h₂ ⊢
      rw [hiter x hk] at h₁
      simp only [Option.getD_some] at h₂ ⊢
      exact Nat.mul_le_mul_left c (by omega)
  have hS (x : γ) : (Finset.Iic (n x)).sup (fun k => c *
      ((encOption (encPair encNat encB) ((countStep step)^[k] (some (n x, init x)))).length +
      Ss (((countStep step)^[k] (some (n x, init x))).getD default).2 + 1)) ≤
      c * (2 * (encNat (n x)).length + B x + 2 + Q x + 1) :=
    Finset.sup_le fun k hk => by
      have hk := Finset.mem_Iic.mp hk
      have h₁ := hlen x hk
      have h₂ := hspace x k hk
      rw [hiter x hk] at h₁ ⊢
      simp only [Option.getD_some]
      exact Nat.mul_le_mul_left c (by omega)
  have hL (x : γ) : (Finset.Iic (n x)).sup (fun k =>
      (encOption (encPair encNat encB) ((countStep step)^[k] (some (n x, init x)))).length) ≤
      2 * (encNat (n x)).length + B x + 2 :=
    Finset.sup_le fun k hk => hlen x (Finset.mem_Iic.mp hk)
  have hO : ComputableTidilyInO (fun x => (countStep step)^[n x] (some (n x, init x))) encIn
      (encOption (encPair encNat encB))
      (fun x => Tn x + Ti x + (n x + 1) * (R x + B x + ((encNat (n x)).length + 1) ^ 2))
      fun x => Sn x + Si x + Q x + B x + (encNat (n x)).length := by
    refine of_bounds h (c₀ + c₁ * (c₀ + 1) + 8 * (c + d + 1) + 4 * d * (c + 1)) (fun x => ?_)
      (fun x => ?_)
      (fun x => ?_)
    · simp only [Function.comp_apply, Option.map_some, Option.getD_some]
      set P := R x + B x + ((encNat (n x)).length + 1) ^ 2
      have h₁ := hT x
      have h₂ := hL x
      have h₃ := h₀.length_le x
      have h₄ : (encNat (n x)).length + 1 ≤ ((encNat (n x)).length + 1) ^ 2 :=
        Nat.le_self_pow two_ne_zero _
      have e₁ : c * (2 * (encNat (n x)).length + B x + 2 + ((encNat (n x)).length + 1) ^ 2 +
          R x + 1) ≤ c * (4 * P) := Nat.mul_le_mul_left c (by omega)
      have e₀ := (Nat.add_le_add_right h₂ 1).trans
        (show 2 * (encNat (n x)).length + B x + 2 + 1 ≤ 3 * P by omega)
      have e₂ := Nat.mul_le_mul_left (n x + 1) (Nat.add_le_add (h₁.trans e₁)
        (Nat.mul_le_mul_left d e₀))
      have e₃ : (n x + 1) * (c * (4 * P) + d * (3 * P)) ≤
          8 * (c + d + 1) * ((n x + 1) * P) := by
        ring_nf; nlinarith [Nat.zero_le (n x * P), Nat.zero_le P]
      simp only [Function.comp_apply] at h₃
      exact sum_le (k' := 4 * d * (c + 1))
        ((e₂.trans e₃).trans (Nat.mul_le_mul_left _ (by omega))) h₃
    · simp only [Function.comp_apply, Option.map_some, Option.getD_some]
      set W := Q x + B x + (encNat (n x)).length
      have h₁ := (hS x).trans (Nat.mul_le_mul_left c
        (show 2 * (encNat (n x)).length + B x + 2 + Q x + 1 ≤ 3 * (W + 1) by omega))
      have h₂ := (Nat.add_le_add_right (hL x) 1).trans
        (show 2 * (encNat (n x)).length + B x + 2 + 1 ≤ 3 * (W + 1) by omega)
      have e₁ := Nat.mul_le_mul_left d (Nat.add_le_add h₁ h₂)
      have e₂ : d * (c * (3 * (W + 1)) + 3 * (W + 1)) ≤ 4 * d * (c + 1) * (W + 1) := by
        ring_nf; omega
      have h₃ := l₀ x
      simp only [Function.comp_apply] at h₃
      have := sum_le (k := 4 * d * (c + 1)) (k' := 8 * (c + d + 1)) (c₁ := c₁)
        (e₁.trans e₂) h₃
      rw [show c₀ + c₁ * (c₀ + 1) + 4 * d * (c + 1) + 8 * (c + d + 1) =
        c₀ + c₁ * (c₀ + 1) + 8 * (c + d + 1) + 4 * d * (c + 1) by ring] at this
      simp only [W] at this
      linarith
    · refine (hlen x le_rfl).trans ((show 2 * (encNat (n x)).length + B x + 2 ≤
        2 * (Sn x + Si x + Q x + B x + (encNat (n x)).length + 1) by omega).trans
        (Nat.mul_le_mul_right _ (by omega)))
  refine (((ComputableTidilyInDegree.getD (enc₁ := encPair encNat encB)
    (enc := encOption (encPair encNat encB))
    default).inO_one.comp_linear hO).snd').of_enc_eq fun x => ?_
  simp only [Function.comp_apply, hiter x le_rfl, Option.getD_some]

end Iterate

end ComputableTidilyInO

end Turing.MultiTapeTM
