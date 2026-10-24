/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Kolmogorov.MINKT
import Complexity.Computability.Kolmogorov.TimeBounded

/-!
Regression clients for time-bounded Kolmogorov complexity (`K^t`), Levin's `Kt`, the universal
multi-tape description method `universalTM`, `MINKT ∈ NP`, `MINKTAt ∈ NP`, and `GapMINKT`
(#798 M1a).
-/

namespace ComplexityTests.KolmogorovTimeBounded

open Cslib Cslib.Kolmogorov Cslib.Kolmogorov.DescriptionMethod Cslib.Complexity
open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal

/-! ### Clock-preserving simulation of binary multi-tape machines -/

example {k : ℕ} {State : Type} [Finite State] (tm : MultiTapeTM k Bool State) :
    ∃ c : ℕ, Nonempty (Simulation (ofMultiTapeTM tm) universalTM c fun _ t => t) :=
  simulation_ofMultiTapeTM tm

example {k : ℕ} {State : Type} [Finite State] (tm : MultiTapeTM k Bool State) :
    ∃ c : ℕ, ∀ (t : ℕ) (x : List Bool),
      universalTM.etimeBoundedComplexity t x ≤
        (ofMultiTapeTM tm).etimeBoundedComplexity t x + c :=
  exists_etimeBoundedComplexity_universalTM_le_ofMultiTapeTM tm

/-! ### Basic properties of `K^t` and `Kt` -/

-- Monotonicity in the time bound `t`.
example {t₁ t₂ : ℕ → ℕ} (h : t₁ ≤ t₂) (x : List Bool) :
    timeBounded t₂ x ≤ timeBounded t₁ x :=
  timeBounded_anti h x

-- Trivial upper bound `K^t(x) ≤ |x| + copyOverhead` for `t(n) ≥ n + 1` (LP20 Fact 2.1).
example (x : List Bool) :
    timeBounded (fun n => n + 1) x ≤ (x.length + copyOverhead : ℕ) :=
  timeBounded_le (fun _ => le_rfl) x

-- `K(x) ≤ K^t(x)` for plain complexity under `universalTM` and `Partrec.universal`.
example (t : ℕ → ℕ) (x : List Bool) : plain x ≤ timeBounded t x :=
  plain_le_timeBounded t x

example : ∃ c : ℕ, ∀ (t : ℕ → ℕ) (n : ℕ),
    universal.ecomplexity n ≤ timeBounded t n.bits + c :=
  exists_ecomplexity_universal_le_timeBounded_bits

-- Decision D3 bridge between `ℕ∞` and the `ℕ` infimum when a witness exists.
example (x : List Bool) :
    timeBoundedNat (fun n => n + 1) x =
      sInf {k : ℕ | ∃ p : List Bool, p.length = k ∧
        x ∈ (universalTM.run p).runFor (x.length + 1)} :=
  timeBoundedNat_eq_sInf (timeBounded_ne_top (t := fun n => n + 1) le_rfl)

-- Counting and incompressibility for `K^t`.
example (t : ℕ → ℕ) (n : ℕ) :
    ∃ x : List Bool, x.length = n ∧ (n : ℕ∞) ≤ timeBounded t x :=
  exists_length_eq_le_timeBounded t n

example (t : ℕ → ℕ) (n c : ℕ) :
    2 ^ n < {x : List Bool | x.length = n ∧ (n - c : ℕ) ≤ timeBounded t x}.ncard +
      2 ^ (n - c) :=
  two_pow_lt_ncard_setOf_length_eq_le_timeBounded_add t n c

-- Levin's `Kt` properties and threshold bridge.
example (x : List Bool) : plain x ≤ levinKt x :=
  plain_le_levinKt x

example (x : List Bool) (k : ℕ) :
    levinKtNat x ≤ k ↔
      ∃ (p : List Bool) (s : ℕ),
        x ∈ (universalTM.run p).runFor s ∧ p.length + Nat.clog 2 s ≤ k :=
  levinKtNat_le_iff.trans levinKt_le_natCast_iff

/-! ### `MINKT`, `MINKTAt`, and `GapMINKT` -/

example : MINKT ∈ NP MINKT.enc :=
  MINKT.mem_NP

example (p q : Polynomial ℕ) : MINKTAt p.eval q.eval ∈ NP encBits :=
  MINKTAt.mem_NP_polynomial₂ p q

example : GapMINKT (fun _ s => s) (fun _ t => t) = PromiseProblem.ofSet MINKT :=
  GapMINKT.id_eq

/-! ### Axiom guards -/

/--
info: 'Cslib.Kolmogorov.simulation_ofMultiTapeTM' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms simulation_ofMultiTapeTM

/--
info: 'Cslib.Kolmogorov.timeBounded_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms timeBounded_le

/--
info: 'Cslib.Kolmogorov.exists_ecomplexity_universal_le_timeBounded' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_ecomplexity_universal_le_timeBounded

/--
info: 'Cslib.Kolmogorov.MINKT.mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MINKT.mem_NP

/--
info: 'Cslib.Kolmogorov.MINKTAt.mem_NP_polynomial₂' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MINKTAt.mem_NP_polynomial₂

end ComplexityTests.KolmogorovTimeBounded
