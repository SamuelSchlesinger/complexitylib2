/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Hierarchy.SpaceUniversal
public import Complexity.Computability.Complexity.Classes.Hierarchy.Time
public import Complexity.Computability.Complexity.Classes.LogSpace
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Deterministic space classes and the space hierarchy theorem

TODO
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- **A computation within space `s n` halts within a time bound of `n`.** A function computable
within space `s n` on encoded inputs of length `n`, within any time bound, is computable within the
same space and the time `(n + 2) * storageBound Bool State k (s n)` of the configuration count of
its machine (`Turing.MultiTapeTM.haltsAt_le_card`), a function of `n` alone. -/
theorem ComputableInTimeAndSpace.exists_time_of_length {f : α → β} {t : α → ℕ} {s : ℕ → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t fun a => s (encIn a).length) :
    ∃ t' : ℕ → ℕ, ComputableInTimeAndSpaceOfLength f encIn encOut t' s := by
  obtain ⟨k, State, hfin, tm, htm⟩ := h
  let := Fintype.ofFinite State
  exact ⟨fun n => (n + 2) * storageBound Bool State k (s n), k, State, hfin, tm,
    fun a => (htm a).of_card⟩

/-- **The configuration-counting bound**: a function computable within space `s n` on encoded
inputs of length `n` is computable within the same space and time `(n + 2) * c * 2 ^ (c * s n)`,
for a constant `c` of the machine. -/
theorem ComputableInTimeAndSpace.exists_time_two_pow {f : α → β} {t : α → ℕ} {s : ℕ → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t fun a => s (encIn a).length) :
    ∃ c, ComputableInTimeAndSpaceOfLength f encIn encOut (fun n => (n + 2) * c * 2 ^ (c * s n))
      s := by
  obtain ⟨k, State, hfin, tm, htm⟩ := h
  let := Fintype.ofFinite State
  set c := storageBoundBase Bool State k + storageBoundExp Bool k
  have h' : tm.ComputesFunInTimeAndSpace encIn encOut f
      (fun a => ((encIn a).length + 2) * storageBound Bool State k (s (encIn a).length))
      fun a => s (encIn a).length := fun a => (htm a).of_card
  refine ⟨c, k, State, hfin, tm, h'.mono (fun a => ?_) fun _ => le_rfl⟩
  dsimp only
  rw [mul_assoc]
  refine Nat.mul_le_mul_left _ ((storageBound_le_base_mul_pow _).trans
    (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))))

/-- **From binary to unary**, by counting down: within time `O((n + 1) ^ 3)` and space `O(n)`. -/
theorem ComputableTidilyInO.natToUnary : ComputableTidilyInO (fun n : ℕ => n) encNat encUnary
    (fun n => (n + 1) ^ 3) fun n => n := by
  have hiter (n : ℕ) : (· + 1)^[n] 0 = n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]
  have h := ComputableTidilyInO.iterate (n := fun n : ℕ => n) (init := fun _ => 0)
    (step := (· + 1)) (encIn := encNat) (encB := encUnary)
    (ComputableTidilyInO.of_linear (.of_eq fun _ => rfl)) (ComputableTidilyInO.const 0)
    ComputableTidilyInDegree.unary_succ.inO_one (R := fun n => n) (Q := fun n => n)
    (B := fun n => n)
    (fun n k hk => by simp only [hiter, encUnary_apply, List.length_replicate]; exact hk)
    (fun n k hk => by simp only [hiter, encUnary_apply, List.length_replicate]; exact hk)
    (fun n k hk => by simp only [hiter, encUnary_apply, List.length_replicate]; exact hk)
  refine (h.of_enc_eq fun n => by rw [hiter]).mono 8 (fun n => ?_) fun n => ?_
  all_goals
    have := Universal.length_encNat_le n
    have h₁ : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have h₂ : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h₃ := Nat.pow_le_pow_left (show (encNat n).length + 1 ≤ n + 1 by omega) 2
  · nlinarith
  · omega

end Turing.MultiTapeTM

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Filter

variable {α : Type*} {enc : α ↪ List Bool} {A : Set α}

/-! ### Space classes -/

/-- The problems decidable within space `O(s n)`, that is `c₁ * s n + c₂` for constants `c₁` and
`c₂`, on instances whose encoding under `enc` has length `n`, by a machine with a binary alphabet
and finitely many states, within some time bound of `n`. -/
def DSPACE (enc : α ↪ List Bool) (s : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ c₁ c₂ : ℕ, ∃ t : ℕ → ℕ,
    DecidableInTimeAndSpace A enc (fun a => t (enc a).length) fun a => c₁ * s (enc a).length + c₂}

/-- **Membership in `DSPACE`** asks for no particular time bound: a machine that halts within the
space bound halts within the number of its configurations, a function of the length of the
encoded instance (`Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_time_of_length`). -/
theorem mem_DSPACE_iff {s : ℕ → ℕ} : A ∈ DSPACE enc s ↔
    ∃ c₁ c₂ : ℕ, ∃ t : α → ℕ,
      DecidableInTimeAndSpace A enc t fun a => c₁ * s (enc a).length + c₂ := by
  refine ⟨fun ⟨c₁, c₂, t, h⟩ => ⟨c₁, c₂, _, h⟩, fun ⟨c₁, c₂, t, h⟩ => ?_⟩
  obtain ⟨t', h'⟩ := ComputableInTimeAndSpace.exists_time_of_length (s := fun n => c₁ * s n + c₂) h
  exact ⟨c₁, c₂, t', h'⟩

/-- `DSPACE` is monotone in the space bound. -/
theorem DSPACE_mono {s₁ s₂ : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₂ n) : DSPACE enc s₁ ⊆ DSPACE enc s₂ := by
  rintro A ⟨c₁, c₂, t, hA⟩
  exact ⟨c₁, c₂, t, ComputableInTimeAndSpace.mono hA (fun _ => le_rfl)
    fun a => Nat.add_le_add_right (Nat.mul_le_mul_left _ (h _)) _⟩

/-- `DSPACE` only depends on the space bound eventually: the finitely many other values are
absorbed by the additive constant. -/
theorem DSPACE_mono_of_eventually_le {s₁ s₂ : ℕ → ℕ} (h : ∀ᶠ n in atTop, s₁ n ≤ s₂ n) :
    DSPACE enc s₁ ⊆ DSPACE enc s₂ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  rintro A ⟨c₁, c₂, t, hA⟩
  refine ⟨c₁, c₁ * ∑ n ∈ Finset.range N, s₁ n + c₂, t,
    ComputableInTimeAndSpace.mono hA (fun _ => le_rfl) fun a => ?_⟩
  have : s₁ (enc a).length ≤ s₂ (enc a).length + ∑ n ∈ Finset.range N, s₁ n := by
    rcases le_or_gt N (enc a).length with h | h
    · have := hN _ h
      omega
    · have := Finset.single_le_sum (f := s₁) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr h)
      omega
  have := Nat.mul_le_mul_left c₁ this
  rw [Nat.mul_add] at this
  omega

/-- **Time bounds space**: a machine visits at most one new cell per work tape and step, so
`DTIME t ⊆ DSPACE t`. -/
theorem DTIME_subset_DSPACE {t : ℕ → ℕ} : DTIME enc t ⊆ DSPACE enc t := by
  rintro A ⟨c₁, c₂, s, hA⟩
  obtain ⟨c, h⟩ := ComputableInTimeAndSpace.exists_space_linear hA
  refine mem_DSPACE_iff.mpr ⟨c * c₁, c * c₂ + c, _, ComputableInTimeAndSpace.mono h
    (fun _ => le_rfl) fun a => ?_⟩
  rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- **Space bounds time exponentially** (the inclusion `DSPACE s ⊆ DTIME (2 ^ O(s))` of cslib pull
request #767, for encoded instances): a decider within space `O(s n)` halts within its number of
configurations, `O((n + 2) * 2 ^ (c * s n))` for a constant `c` of the decider. -/
theorem exists_mem_DTIME_of_mem_DSPACE {s : ℕ → ℕ} (h : A ∈ DSPACE enc s) :
    ∃ c, A ∈ DTIME enc fun n => (n + 2) * 2 ^ (c * s n) := by
  obtain ⟨c₁, c₂, t, hA⟩ := h
  obtain ⟨c, h⟩ := ComputableInTimeAndSpace.exists_time_two_pow (s := fun n => c₁ * s n + c₂) hA
  refine ⟨c * c₁, c * 2 ^ (c * c₂), 0, fun n => c₁ * s n + c₂, ComputableInTimeAndSpace.mono h
    (fun a => ?_) fun _ => le_rfl⟩
  dsimp only
  rw [Nat.mul_add, pow_add, ← Nat.mul_assoc c c₁]
  apply le_of_eq
  ring

/-- **`L` is `DSPACE (log₂)`**, the definition of `L` in cslib pull request #767. -/
theorem mem_L_iff_mem_DSPACE {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ L enc ↔ A ∈ DSPACE enc Nat.log2 :=
  mem_L_iff.trans mem_DSPACE_iff.symm

/-- A space class of a polynomially bounded bound is within `PSPACE`. -/
theorem DSPACE_subset_PSPACE {α : Type} {enc : α ↪ List Bool} {s : ℕ → ℕ}
    (hs : PolynomiallyBounded s) : DSPACE enc s ⊆ PSPACE enc := by
  rintro A ⟨c₁, c₂, t, hA⟩
  have : PolynomiallyBounded fun n => c₁ * s n + c₂ := by fun_prop
  exact mem_PSPACE_iff.mpr ⟨_, _, .of_polynomiallyBounded (fun a => (enc a).length) this, hA⟩

private theorem succ_pow_le (n d : ℕ) : (n + 1) ^ d ≤ 2 ^ d * n ^ d + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · simp [Nat.zero_pow hd]
  · calc (n + 1) ^ d ≤ (2 * n) ^ d := Nat.pow_le_pow_left (by omega) d
      _ = 2 ^ d * n ^ d := mul_pow ..
      _ ≤ _ := Nat.le_succ _

/-- **`PSPACE` is the union of the classes `DSPACE (n ^ k)`**, the definition of `PSPACE` in cslib
pull request #767. -/
theorem mem_PSPACE_iff_exists_mem_DSPACE {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ PSPACE enc ↔ ∃ k, A ∈ DSPACE enc (· ^ k) := by
  refine ⟨fun h => ?_, fun ⟨k, h⟩ => DSPACE_subset_PSPACE (by fun_prop) h⟩
  obtain ⟨t, s, hs, hA⟩ := mem_PSPACE_iff.mp h
  obtain ⟨C, d, hC⟩ := hs.exists_le
  refine ⟨d, mem_DSPACE_iff.mpr ⟨C * 2 ^ d, C, t, ComputableInTimeAndSpace.mono hA
    (fun _ => le_rfl) fun a => (hC a).trans ?_⟩⟩
  have := Nat.mul_le_mul_left C (succ_pow_le (enc a).length d)
  rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc] at this
  exact this

/-! ### Space-constructible bounds -/

/-- A bound `s` is space-constructible when some machine with a binary alphabet and finitely many
states computes `s n` in binary from any word of length `n` within space `O(s n)`, halting
[Sipser, Definition 9.1][Sipser2013]. Unlike [Sipser, Definition 9.1][Sipser2013], `s n ≥ log n`
is not required here; the space hierarchy theorem below asks for `n ≤ s n`. -/
def SpaceConstructible (s : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∃ t : ℕ → ℕ, ComputableInTimeAndSpaceOfLength (fun x : List Bool => s x.length) encBits
    encNat t fun n => c * s n + c

/-- A space-constructible bound is computed tidily within space `O(s n)`, within some time. -/
theorem SpaceConstructible.computableTidilyInO {s : ℕ → ℕ} (hs : SpaceConstructible s) :
    ∃ T, ComputableTidilyInO (fun x : List Bool => s x.length) encBits encNat T
      fun x => s x.length := by
  obtain ⟨c, t, h⟩ := hs
  obtain ⟨d, h⟩ := ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace h
  refine ⟨_, .of_bounds h (d * (c + 1) + 1) (T := fun x => 2 * t x.length +
    3 * (c * s x.length + c) + d) (fun x => ?_) (fun x => ?_) fun x => ?_⟩
  · exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (by omega))
  · dsimp only [encBits_apply]
    nlinarith
  · exact (Universal.length_encNat_le _).trans
      ((Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (by omega)))

/-- A time-constructible bound is space-constructible, since space is at most time. -/
theorem TimeConstructible.spaceConstructible {t : ℕ → ℕ} (ht : TimeConstructible t) :
    SpaceConstructible t := by
  obtain ⟨c, s, h⟩ := ht
  obtain ⟨k, h⟩ := ComputableInTimeAndSpace.exists_space_linear h
  exact ⟨k * c + k, fun n => c * t n + c, ComputableInTimeAndSpace.mono h (fun _ => le_rfl)
    fun x => by dsimp only; nlinarith⟩

/-- `n` is space-constructible: count the length of the word in binary. -/
theorem spaceConstructible_id : SpaceConstructible fun n => n := by
  obtain ⟨c, h, -⟩ := ComputableTidilyInO.lengthNat
  exact ⟨2 * c, fun n => c * ((n + 1) ^ 2 + 1), h.computableInTimeAndSpace.mono
    (fun _ => le_rfl) fun x => by simp only [encBits_apply]; nlinarith⟩

/-- `(n + 1) ^ k` is space-constructible for `k ≥ 2`. -/
theorem spaceConstructible_succ_pow {k : ℕ} (hk : 2 ≤ k) :
    SpaceConstructible fun n => (n + 1) ^ k :=
  (timeConstructible_succ_pow hk).spaceConstructible

/-- `2 ^ n` is space-constructible. -/
theorem spaceConstructible_two_pow : SpaceConstructible (2 ^ ·) :=
  timeConstructible_two_pow.spaceConstructible

end Cslib.Complexity
