/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import Mathlib.Tactic.Linarith

/-!
# Quantitative streaming folds

Ordinary `List.foldl` expressions over raw bit strings use Christian Reitwiessner's streaming
backend. A round holds the accumulator and one bit, and does not copy the input list. Time, work
space and encoded accumulator size remain separate in the contract. Space counts visited work-tape
cells, excluding the read-only input and write-only output; retained accumulators are charged.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream_sum`: cumulative
  computation and copying costs, with peak workspace bounds.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream_sum_spec`: an invariant
  supplies the cumulative cost and postcondition.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream`: the uniform-round
  specialization.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.foldl_bits_stream_spec`: an invariant
  supplies the bounds and a postcondition.
* `Turing.MultiTapeTM.ComputableTidilyInO.foldl_bits_finite`: a fixed finite-state fold takes
  linear time and constant work space, including a bound on its encoded final state.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.map_bits`: a bitwise map emits its output
  as it scans, in linear time and zero work space.

## References

Uses Christian Reitwiessner's `ComputableTidilyInTimeAndSpace.streamFold` from the
`crei/tidy-universal` branch; see the source marker in `Encodings/StreamFold.lean`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

private lemma streamEmit_nil {σ : Type} (next : σ × Bool → σ) (init : σ) (l : List Bool) :
    streamEmit next (fun _ => []) init l = [] := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => exact ih _

/-- Stream a bit list with cumulative round costs. `R l i` includes the step, the current and next
encoded state lengths, and control. `Q` and `B` bound peak step workspace and encoded state size.
The input is scanned without copying; final output and tape restoration are charged too.
The constant is independent of the input, and the bounds need not be computable. -/
theorem ComputableTidilyInTimeAndSpace.foldl_bits_stream_sum {σ : Type}
    {enc : σ ↪ List Bool} {step : σ → Bool → σ} (init : σ) {t s : σ × Bool → ℕ}
    (hstep : ComputableTidilyInTimeAndSpace (fun p => step p.1 p.2)
      (encPair enc encBool) enc t s)
    {R : List Bool → ℕ → ℕ} {Q B : List Bool → ℕ}
    (hcost : ∀ l i (hi : i < l.length), t ((l.take i).foldl step init, l[i]) +
      (enc ((l.take i).foldl step init)).length +
      (enc ((l.take (i + 1)).foldl step init)).length + 1 ≤ R l i)
    (hspace : ∀ l i (hi : i < l.length), s ((l.take i).foldl step init, l[i]) ≤ Q l)
    (hstate : ∀ l i, i ≤ l.length → (enc ((l.take i).foldl step init)).length ≤ B l) :
    ∃ c, ComputableTidilyInTimeAndSpace (fun l => l.foldl step init) encBits enc
      (fun l => c * ((∑ i ∈ Finset.range l.length, R l i) + B l + 1))
      (fun l => c * (Q l + B l + 1)) := by
  obtain ⟨ci, hi⟩ := computableInTimeAndSpace_of_const (encIn := encBits) (encOut := enc) init
  obtain ⟨ce, he⟩ := computableInTimeAndSpace_of_const
    (encIn := encPair enc encBool) (encOut := encBits) []
  let reader : InputReader Bool Unit := ⟨(), fun _ b => (none, some b)⟩
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.streamFold_sum
    (g := fun l => l.foldl step init) (encOut := enc)
    reader (fun b => [b]) (fun _ => List.cons_ne_nil _ _)
    (fun a rest => by simp [reader, InputReader.read])
    id (fun l => by simp) hi.computableTidilyInTimeAndSpace hstep
    he.computableTidilyInTimeAndSpace computableTidilyInTimeAndSpace_id
    (fun l => by simp [streamEmit_nil, streamState])
    (roundCost := fun l i => (2 * ce + 4) * R l i) (sMax := Q)
    (lMax := fun l => B l + 1)
    (fun l i hi => by
      have hr := hcost l i hi
      have hR : 1 ≤ R l i := by lia
      have hm := Nat.mul_le_mul_left (2 * ce + 3) hR
      simp only [streamState, Function.const_apply, encBool_apply, List.length_singleton, id_eq]
      nlinarith)
    (fun l i hi => hspace l i hi)
    (fun l i hi => (hstate l i hi).trans (Nat.le_succ _))
    (fun _ _ _ => by simp)
  have hn (l : List Bool) : l.length ≤ ∑ i ∈ Finset.range l.length, R l i := by
    calc
      l.length = ∑ _i ∈ Finset.range l.length, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => by
        have hr := hcost l i (Finset.mem_range.mp hi)
        lia
  refine ⟨c * (2 * ci + 2 * ce + 20), h.mono (fun l => ?_) (fun l => ?_)⟩
  · have hf := hstate l l.length le_rfl
    simp only [List.take_length] at hf
    simp only [id_eq, encBits_apply, streamState, List.take_length, Function.const_apply]
    rw [Nat.mul_assoc, ← Finset.mul_sum]
    apply Nat.mul_le_mul_left c
    change 2 * ci + 2 + (2 * (enc (l.foldl step init)).length + 4) + l.length +
      (2 * ce + 4) * (∑ i ∈ Finset.range l.length, R l i) + (B l + 1) + 1 ≤ _
    have hr := hn l
    nlinarith
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith


/-- Stream a bit list through a tidy step computation. Each round charges the step and the stored
state, without copying the input list. `R`, `Q` and `B` bound the time of a round, its work space
and the encoded state size, respectively. The final output and tape restoration are charged too.
The constant is independent of the input; the three bounds need not be computable. -/
theorem ComputableTidilyInTimeAndSpace.foldl_bits_stream {σ : Type}
    {enc : σ ↪ List Bool} {step : σ → Bool → σ} (init : σ) {t s : σ × Bool → ℕ}
    (hstep : ComputableTidilyInTimeAndSpace (fun p => step p.1 p.2)
      (encPair enc encBool) enc t s)
    {R Q B : List Bool → ℕ}
    (htime : ∀ l i (hi : i < l.length), t ((l.take i).foldl step init, l[i]) ≤ R l)
    (hspace : ∀ l i (hi : i < l.length), s ((l.take i).foldl step init, l[i]) ≤ Q l)
    (hstate : ∀ l i, i ≤ l.length → (enc ((l.take i).foldl step init)).length ≤ B l) :
    ∃ c, ComputableTidilyInTimeAndSpace (fun l => l.foldl step init) encBits enc
      (fun l => c * (l.length * (R l + B l + 1) + B l + 1))
      (fun l => c * (Q l + B l + 1)) := by
  obtain ⟨c, h⟩ := hstep.foldl_bits_stream_sum init
    (R := fun l _ => R l + 2 * B l + 1) (Q := Q) (B := B)
    (fun l i hi => by
      have ht := htime l i hi
      have h₀ := hstate l i hi.le
      have h₁ := hstate l (i + 1) hi
      lia) hspace hstate
  refine ⟨c * 2, h.mono (fun l => ?_) (fun l => ?_)⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    lia


/-- An invariant supplies cumulative computation and copying costs, peak workspace and a
postcondition. Each round's bound includes both the old and the new encoded state. -/
theorem ComputableTidilyInTimeAndSpace.foldl_bits_stream_sum_spec {σ : Type}
    {enc : σ ↪ List Bool} {step : σ → Bool → σ} (init : σ) {t s : σ × Bool → ℕ}
    (hstep : ComputableTidilyInTimeAndSpace (fun p => step p.1 p.2)
      (encPair enc encBool) enc t s)
    (invariant : List Bool → ℕ → σ → Prop)
    (hbase : ∀ l, invariant l 0 init)
    (hpreserve : ∀ l i (hi : i < l.length) state, invariant l i state →
      invariant l (i + 1) (step state l[i]))
    {R : List Bool → ℕ → ℕ} {Q B : List Bool → ℕ}
    (hcost : ∀ l i (hi : i < l.length) state, invariant l i state →
      t (state, l[i]) + (enc state).length + (enc (step state l[i])).length + 1 ≤ R l i ∧
        s (state, l[i]) ≤ Q l)
    (hsize : ∀ l i, i ≤ l.length → ∀ state, invariant l i state → (enc state).length ≤ B l) :
    (∃ c, ComputableTidilyInTimeAndSpace (fun l => l.foldl step init) encBits enc
      (fun l => c * ((∑ i ∈ Finset.range l.length, R l i) + B l + 1))
      (fun l => c * (Q l + B l + 1))) ∧
      ∀ l, invariant l l.length (l.foldl step init) := by
  have htrace (l : List Bool) (i : ℕ) (hi : i ≤ l.length) :
      invariant l i ((l.take i).foldl step init) := by
    induction i with
    | zero => exact hbase l
    | succ i ih =>
      have hlt : i < l.length := by lia
      simpa only [List.take_succ_eq_append_getElem hlt, List.foldl_append,
        List.foldl_cons, List.foldl_nil] using hpreserve l i hlt _ (ih (by lia))
  exact ⟨hstep.foldl_bits_stream_sum init
    (fun l i hi => by
      simpa only [List.take_succ_eq_append_getElem hi, List.foldl_append,
        List.foldl_cons, List.foldl_nil] using (hcost l i hi _ (htrace l i hi.le)).1)
    (fun l i hi => (hcost l i hi _ (htrace l i hi.le)).2)
    (fun l i hi => hsize l i hi _ (htrace l i hi)),
    fun l => by simpa using htrace l l.length le_rfl⟩

/-- An invariant supplies the streaming fold's resource bounds and postcondition. -/
theorem ComputableTidilyInTimeAndSpace.foldl_bits_stream_spec {σ : Type}
    {enc : σ ↪ List Bool} {step : σ → Bool → σ} (init : σ) {t s : σ × Bool → ℕ}
    (hstep : ComputableTidilyInTimeAndSpace (fun p => step p.1 p.2)
      (encPair enc encBool) enc t s)
    (invariant : List Bool → ℕ → σ → Prop)
    (hbase : ∀ l, invariant l 0 init)
    (hpreserve : ∀ l i (hi : i < l.length) state, invariant l i state →
      invariant l (i + 1) (step state l[i]))
    {R Q B : List Bool → ℕ}
    (hcost : ∀ l i (hi : i < l.length) state, invariant l i state →
      t (state, l[i]) ≤ R l ∧ s (state, l[i]) ≤ Q l)
    (hsize : ∀ l i, i ≤ l.length → ∀ state, invariant l i state → (enc state).length ≤ B l) :
    (∃ c, ComputableTidilyInTimeAndSpace (fun l => l.foldl step init) encBits enc
      (fun l => c * (l.length * (R l + B l + 1) + B l + 1))
      (fun l => c * (Q l + B l + 1))) ∧
      ∀ l, invariant l l.length (l.foldl step init) := by
  obtain ⟨⟨c, h⟩, hpost⟩ := hstep.foldl_bits_stream_sum_spec init invariant hbase hpreserve
    (R := fun l _ => R l + 2 * B l + 1) (Q := Q) (B := B)
    (fun l i hi state hs => by
      have hc := hcost l i hi state hs
      have h₀ := hsize l i hi.le state hs
      have h₁ := hsize l (i + 1) hi _ (hpreserve l i hi state hs)
      exact ⟨by lia, hc.2⟩) hsize
  refine ⟨⟨c * 2, h.mono (fun l => ?_) (fun l => ?_)⟩, hpost⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    lia

/-- A fold with a fixed finite state type takes linear time and constant work space. The constant
may depend on the state type, its encoding and the transition function; this is not a uniform bound
for a family of growing state types. The encoded final state is bounded as well. -/
theorem ComputableTidilyInO.foldl_bits_finite {σ : Type} [Finite σ]
    (enc : σ ↪ List Bool) (step : σ → Bool → σ) (init : σ) :
    ComputableTidilyInO (fun l => l.foldl step init) encBits enc List.length (fun _ => 0) := by
  classical
  let := Fintype.ofFinite σ
  let b := Finset.univ.sup (fun s => (enc s).length)
  have hb (s : σ) : (enc s).length ≤ b :=
    Finset.le_sup (f := fun s => (enc s).length) (Finset.mem_univ s)
  obtain ⟨k, hk⟩ := computableInTimeAndSpace_of_finite
    (encIn := encPair enc encBool) (encOut := enc) (fun p : σ × Bool => step p.1 p.2)
  obtain ⟨c, h⟩ := hk.computableTidilyInTimeAndSpace.foldl_bits_stream init
    (R := fun _ => 2 * k + 2) (Q := fun _ => 0) (B := fun _ => b)
    (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) (fun _ _ _ => hb _)
  refine ComputableTidilyInO.of_bounds h (c * (2 * k + 2 * b + 4) + b) ?_ ?_ ?_
  · intro l
    have hr : l.length * (2 * k + 2 + b + 1) + b + 1 ≤
        (2 * k + 2 * b + 4) * (l.length + 1) := by nlinarith
    exact (Nat.mul_le_mul_left c hr).trans (by nlinarith)
  · intro l
    nlinarith
  · intro l
    exact (hb _).trans (by simp)

/-- Emit a bitwise map directly, without a growing accumulator on a work tape. Unlike `InO`,
this numerical certificate does not include the emitted output in its space bound. -/
theorem ComputableTidilyInTimeAndSpace.map_bits (f : Bool → Bool) :
    ComputableTidilyInTimeAndSpace (List.map f) encBits encBits
      (fun l => 4 * l.length + 8) (fun _ => 0) := by
  let transducer : Transducer Bool Unit :=
    ⟨(), fun _ b => ((), [f b]), fun _ => [], by simp, by simp⟩
  refine transducer.computableTidilyInTimeAndSpace ?_
  intro l
  induction l with
  | nil => rfl
  | cons b l ih => simpa [transducer, Transducer.run] using congrArg (List.cons (f b)) ih

end Turing.MultiTapeTM
