/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Kolmogorov.Incompressibility
public import Complexity.Computability.Kolmogorov.SingleTape
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Mathlib.Data.Nat.Log

/-!
# Time-bounded Kolmogorov complexity (`K^t`) and Levin's `Kt`

This module defines the universal multi-tape Turing machine description method
`Cslib.Kolmogorov.DescriptionMethod.universalTM` for binary strings, the corresponding plain and
time-bounded Kolmogorov complexities `Cslib.Kolmogorov.plain` (`K`) and
`Cslib.Kolmogorov.timeBounded` (`K^t`), and Levin's time-bounded Kolmogorov complexity
`Cslib.Kolmogorov.levinKt` (`Kt`).

## Modeling conventions (#798 Decisions D1–D3)

* **D1 (clock counts steps of the described machine):**
  A binary program `p : List Bool` is parsed into a multi-tape Turing machine description
  `decodeDesc (unframe p)` (`Turing.MultiTapeTM.Universal.decodeDesc`) and an input bit string
  `dropFrame p` (`Turing.MultiTapeTM.dropFrame`). At step bound `t`, `universalTM` runs the
  described machine on `(dropFrame p).map eBit` for `t` steps (`Universal.Desc.runFor`).
  In [Liu and Pass, Section 2.2][LiuPass2020], $U(\Pi, 1^t)$ denotes the output of $M(w)$ when
  emulated for $t$ steps (whose proof of Theorem 5.2 requires counting steps of the described
  machine $M$, or a constant-overhead universal simulator). Counting the steps of the described
  multi-tape machine directly in `universalTM` makes $K^t$ exact at linear time scales while the
  polynomial overhead of the universal simulator `Universal.universal` appears only in algorithmic
  membership results such as `MINKT ∈ NP`.
* **D2 (global output):**
  When the described machine halts within `t` steps, the entire output tape contents are mapped back
  to `List Bool` via `(· != 0)`, matching the global "print $x$" convention of
  [Ko][Ko1986], [Liu and Pass, Section 2.2][LiuPass2020], and [Hirahara][Hirahara2018], as well as
  `Turing.MultiTapeTM.runFor_eq_simulate`.
* **D3 (values in `ℕ∞` with finite-form bridges):**
  `plain`, `timeBounded`, and `levinKt` take values in `ℕ∞` via
  `DescriptionMethod.ecomplexity` and `DescriptionMethod.etimeBoundedComplexity`, accompanied by
  `ℕ`-valued wrappers (`plainNat`, `timeBoundedNat`, `levinKtNat`) and proved equivalence bridges
  (`timeBounded_le_natCast_iff`, `timeBoundedNat_le_iff`, `timeBoundedNat_eq_sInf`,
  `levinKt_le_natCast_iff`) showing agreement with the literature's `min` over `ℕ` whenever a
  witness exists.

## Main definitions

* `Cslib.Kolmogorov.DescriptionMethod.universalTMRunFor`: clocked evaluation of a binary program
  `p` for `t` steps of the described multi-tape machine.
* `Cslib.Kolmogorov.DescriptionMethod.universalTM`: the universal multi-tape description method on
  `List Bool`.
* `Cslib.Kolmogorov.plain`, `Cslib.Kolmogorov.plainNat`: plain Kolmogorov complexity $K(x)$ under
  `universalTM` in `ℕ∞` and `ℕ`.
* `Cslib.Kolmogorov.timeBounded`, `Cslib.Kolmogorov.timeBoundedNat`: time-bounded Kolmogorov
  complexity $K^t(x)$ for a time bound $t : \mathbb{N} \to \mathbb{N}$, in `ℕ∞` and `ℕ`.
* `Cslib.Kolmogorov.levinKt`, `Cslib.Kolmogorov.levinKtNat`: Levin's time-bounded complexity
  $\mathrm{Kt}(x) = \inf_{s \ge 1} (K^s(x) + \lceil \log_2 s \rceil)$, in `ℕ∞` and `ℕ`.

## Main results

* `Cslib.Kolmogorov.DescriptionMethod.universalTMSimulation`,
  `Cslib.Kolmogorov.simulation_ofMultiTapeTM`: every finite-state binary `MultiTapeTM` is simulated
  by `universalTM` with constant program overhead and zero time overhead.
* `Cslib.Kolmogorov.timeBounded_anti`, `Cslib.Kolmogorov.timeBounded_mono_of_le`: monotonicity in
  the time bound $t$.
* `Cslib.Kolmogorov.timeBounded_le`, `Cslib.Kolmogorov.exists_timeBounded_le`:
  $K^t(x) \le |x| + c$ whenever $t(|x|) \ge |x| + 1$ ([Liu and Pass, Fact 2.1][LiuPass2020] under
  the multi-tape output convention).
* `Cslib.Kolmogorov.plain_le_timeBounded`,
  `Cslib.Kolmogorov.exists_ecomplexity_universal_le_timeBounded`: the direct comparison
  `plain x ≤ timeBounded t x` (`universalTM.ecomplexity`), and for any computable decoder
  `dec : List Bool → ℕ`, the Partrec comparison
  `DescriptionMethod.universal.ecomplexity (dec x) ≤ timeBounded t x + c`.
* `Cslib.Kolmogorov.encard_setOf_timeBounded_lt`,
  `Cslib.Kolmogorov.exists_length_eq_le_timeBounded`,
  `Cslib.Kolmogorov.two_pow_lt_ncard_setOf_length_eq_le_timeBounded_add`: counting and
  incompressibility bounds for $K^t$.
* `Turing.MultiTapeTM.Universal.computableInPolyTime_decodeDesc`,
  `Turing.MultiTapeTM.Universal.computableInPolyTime_map_eBit`,
  `Turing.MultiTapeTM.Universal.computableInPolyTime_eBit`,
  `Turing.MultiTapeTM.Universal.computableInPolyTime_universal`,
  `Cslib.Kolmogorov.DescriptionMethod.computableInPolyTime_universalTMRunFor`: plain
  `ComputableInPolyTime` wrappers for the universal machine and `universalTMRunFor`.

## References

* [Y. Liu, R. Pass, *On One-way Functions and Kolmogorov Complexity*][LiuPass2020]
* [Y. Liu, R. Pass, *On the Possibility of Basing Cryptography on EXP ≠ BPP*][LiuPass2021Crypto]
* [L. A. Levin, *Universal Sequential Search Problems*][Levin1973]
* [K.-I. Ko, *On the Notion of Infinite Pseudorandom Sequences*][Ko1986]
* [E. Allender, H. Buhrman, M. Koucký, D. van Melkebeek, D. Ronneburger,
  *Power from Random Strings*][AllenderBuhrmanKouckyVanMelkebeekRonneburger2006]
* [M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its
  Applications*][LiVitanyi2019]
-/

@[expose] public section

namespace Turing.MultiTapeTM.Universal

/-! ### Plain `ComputableInPolyTime` wrappers for the universal simulator -/

/-- Plain polynomial-time certificate for `decodeDesc`. -/
@[fun_prop]
theorem computableInPolyTime_decodeDesc :
    ComputableInPolyTime decodeDesc encBits eDesc :=
  .of_tidy computableTidilyInPolyTime_decodeDesc

/-- Plain polynomial-time certificate for coding a bit string as unary symbol numbers. -/
@[fun_prop]
theorem computableInPolyTime_map_eBit :
    ComputableInPolyTime (fun w : List Bool => w.map eBit) encBits (encList encUnary) :=
  .of_tidy computableTidilyInPolyTime_map_eBit

/-- Plain polynomial-time certificate for coding a single bit as a unary symbol number. -/
@[fun_prop]
theorem computableInPolyTime_eBit :
    ComputableInPolyTime (fun b : Bool => eBit b) encBool encUnary :=
  .of_tidy computableTidilyInPolyTime_eBit

/-- Plain polynomial-time certificate for the universal simulator with a unary step budget. -/
@[fun_prop]
theorem computableInPolyTime_universal :
    ComputableInPolyTime universal
      (encPair eDesc (encPair (encList encUnary) encUnary)) eOut :=
  .of_tidy computableTidilyInPolyTime_universal

end Turing.MultiTapeTM.Universal

namespace Cslib.Kolmogorov

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal Cslib.Turing

namespace DescriptionMethod

/-! ### The universal multi-tape description method (`universalTM`) -/

/-- Clocked evaluation of a binary program `p` for `t` steps of the described multi-tape machine:
parses `p` into the machine description `decodeDesc (unframe p)` and the input string `dropFrame p`,
simulates the described machine for `t` steps, and maps the output symbol numbers to bits via
`(· != 0)`. -/
def universalTMRunFor (p : List Bool) (t : ℕ) : Option (List Bool) :=
  ((decodeDesc (unframe p)).runFor ((dropFrame p).map eBit) t).map (List.map (· != 0))

theorem universalTMRunFor_eq_ite (p : List Bool) (t : ℕ) :
    universalTMRunFor p t =
      let r := simulate (decodeDesc (unframe p)) ((dropFrame p).map eBit) t
      if r.2 then some (r.1.map (· != 0)) else none := by
  unfold universalTMRunFor Desc.runFor
  dsimp only
  cases (simulate (decodeDesc (unframe p)) ((dropFrame p).map eBit) t).2 <;> rfl

theorem mem_universalTMRunFor_iff {p x : List Bool} {t : ℕ} :
    x ∈ universalTMRunFor p t ↔
      ∃ out : List ℕ,
        simulate (decodeDesc (unframe p)) ((dropFrame p).map eBit) t = (out, true) ∧
          out.map (· != 0) = x := by
  rw [universalTMRunFor, Option.mem_def, Option.map_eq_some_iff]
  simp only [← Option.mem_def, Desc.mem_runFor_iff]

theorem mem_universalTMRunFor_iff_simulate {p x : List Bool} {t : ℕ} :
    x ∈ universalTMRunFor p t ↔
      (simulate (decodeDesc (unframe p)) ((dropFrame p).map eBit) t).2 = true ∧
        (simulate (decodeDesc (unframe p)) ((dropFrame p).map eBit) t).1.map (· != 0) = x := by
  rw [universalTMRunFor_eq_ite]
  dsimp only
  rcases simulate (decodeDesc (unframe p)) ((dropFrame p).map eBit) t with ⟨out, _ | _⟩ <;>
    simp [eq_comm]

theorem universalTMRunFor_mono (p : List Bool) {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) {x : List Bool}
    (h : x ∈ universalTMRunFor p t₁) :
    x ∈ universalTMRunFor p t₂ := by
  obtain ⟨out, hout, rfl⟩ := mem_universalTMRunFor_iff.mp h
  exact mem_universalTMRunFor_iff.mpr ⟨out, simulate_eq_of_halted ht hout, rfl⟩

@[simp]
theorem universalTMRunFor_zero (p : List Bool) : universalTMRunFor p 0 = none := by
  rw [universalTMRunFor_eq_ite]
  rfl

/-- The universal multi-tape Turing machine description method for binary strings
([Liu and Pass, Section 2.2][LiuPass2020]; Decisions D1–D2). A binary program `p` encodes the
machine description `decodeDesc (unframe p)` and the input string `dropFrame p`. The clock counts
steps of the described multi-tape machine (D1), and the output is the global output tape contents
upon halting (D2). -/
def universalTM : DescriptionMethod (List Bool) where
  run p := ⟨universalTMRunFor p, fun t _ hx => universalTMRunFor_mono p t.le_succ hx⟩

@[simp]
theorem universalTM_runFor (p : List Bool) (t : ℕ) :
    (universalTM.run p).runFor t = universalTMRunFor p t :=
  rfl

theorem mem_universalTM_runFor_iff {p x : List Bool} {t : ℕ} :
    x ∈ (universalTM.run p).runFor t ↔
      ∃ out : List ℕ,
        simulate (decodeDesc (unframe p)) ((dropFrame p).map eBit) t = (out, true) ∧
          out.map (· != 0) = x :=
  mem_universalTMRunFor_iff

theorem mem_universalTM_runFor_iff_simulate {p x : List Bool} {t : ℕ} :
    x ∈ (universalTM.run p).runFor t ↔
      (simulate (decodeDesc (unframe p)) ((dropFrame p).map eBit) t).2 = true ∧
        (simulate (decodeDesc (unframe p)) ((dropFrame p).map eBit) t).1.map (· != 0) = x :=
  mem_universalTMRunFor_iff_simulate

@[simp]
theorem etimeBoundedComplexity_universalTM_zero (x : List Bool) :
    universalTM.etimeBoundedComplexity 0 x = ⊤ := by
  rw [etimeBoundedComplexity_eq_top_iff]
  intro p
  simp

/-! ### Polynomial-time and partial-recursive evaluation of `universalTM` -/

/-- Decoding a list of unary symbol numbers to bits via `(· != 0)` is computable in polynomial
time. -/
theorem computableInPolyTime_map_ne_zero :
    ComputableInPolyTime (fun l : List ℕ => l.map (· != 0)) (encList encUnary) encBits := by
  open ComputableTidilyInPolyTime in
  have hbit : ComputableTidilyInPolyTime (fun n : ℕ => n != 0) encUnary encBool := by
    convert bool_not.comp ComputableTidilyInDegree.unary_isZero.computableTidilyInPolyTime using 1
    funext n
    cases n <;> rfl
  exact .of_tidy (listToBits.comp (ComputableTidilyInPolyTime.map hbit))

/-- Evaluating `universalTMRunFor` on a program and a unary step budget is computable in
polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_universalTMRunFor :
    ComputableInPolyTime (fun pt : List Bool × ℕ => universalTMRunFor pt.1 pt.2)
      (encPair encBits encUnary) (encOption encBits) := by
  open ComputableTidilyInPolyTime in
  have hp := fst encBits encUnary
  have ht := snd encBits encUnary
  have hd := computableTidilyInPolyTime_decodeDesc.comp (unframe.comp hp)
  have hw := computableTidilyInPolyTime_map_eBit.comp (dropFrame.comp hp)
  have hsim := computableTidilyInPolyTime_universal.comp (hd.prod (hw.prod ht))
  have hout := (optionSome encBits).comp (computableInPolyTime_map_ne_zero.tidy.comp hsim.fst')
  have hite := hsim.snd'.cond hout (const (encMid := encOption encBits) none)
  refine .of_tidy ?_
  convert hite using 1
  funext ⟨p, t⟩
  rw [universalTMRunFor_eq_ite]
  rfl

/-- `universalTMRunFor` is computable in Mathlib's sense (`Computable₂`). -/
theorem computable_universalTMRunFor : Computable₂ universalTMRunFor := by
  open ComputableTidilyInPolyTime in
  have hframe : Computable frame :=
    (bitsFrame encBits).isComputable.computable_bits
  have hrep : Primrec fun n : ℕ => List.replicate n true :=
    (Primrec.list_map (Primrec.list_range.comp Primrec.id)
      (Primrec.const true).to₂).of_eq fun n => by simp
  have hIn : Computable (encPair encBits encUnary) :=
    (Primrec.list_append.to_comp.comp (hframe.comp Computable.fst)
      (hrep.to_comp.comp Computable.snd)).of_eq fun ⟨p, t⟩ => rfl
  have hOut : Primrec (fun w : List Bool => bif decide (w = []) then none else some w.tail) :=
    Primrec.cond ((Primrec.eq.comp Primrec.id (Primrec.const [])).decide)
      (Primrec.const none) (Primrec.option_some.comp Primrec.list_tail)
  exact computableInPolyTime_universalTMRunFor.tidy.isComputable.computable hIn hOut.to_comp
    fun b => by cases b <;> rfl

/-- Unbounded partial evaluation of a program under `universalTM`. -/
def universalTMEval (p : List Bool) : Part (List Bool) :=
  Nat.rfindOpt (universalTMRunFor p)

@[simp]
theorem mem_universalTMEval_iff {p x : List Bool} :
    x ∈ universalTMEval p ↔ universalTM.Produces p x := by
  rw [universalTMEval, Nat.rfindOpt_mono (fun ht h => universalTMRunFor_mono p ht h),
    produces_iff_exists_mem_runFor]
  rfl

/-- Evaluating programs under `universalTM` is partial recursive (`Partrec`). -/
theorem partrec_universalTMEval : Partrec universalTMEval :=
  Partrec.rfindOpt computable_universalTMRunFor

/-- Mapping any computable decoder `dec : List Bool → ℕ` over `universalTM` yields a partial
recursive description method. -/
theorem isPartrec_universalTM_map {dec : List Bool → ℕ} (hdec : Computable dec) :
    (universalTM.map dec).IsPartrec :=
  IsPartrec.of_partrec_eval partrec_universalTMEval (fun _ _ => mem_universalTMEval_iff.symm) hdec

/-- `Partrec`'s universal description method `universal` is at most an additive constant worse than
`universalTM` under any computable decoder `dec : List Bool → ℕ`. -/
theorem exists_ecomplexity_universal_le_universalTM {dec : List Bool → ℕ} (hdec : Computable dec) :
    ∃ c : ℕ, ∀ x : List Bool,
      universal.ecomplexity (dec x) ≤ universalTM.ecomplexity x + c :=
  exists_ecomplexity_universal_le_of_partrec_eval partrec_universalTMEval
    (fun _ _ => mem_universalTMEval_iff.symm) hdec

/-! ### Clock-preserving simulation of every binary `MultiTapeTM` -/

/-- The program header announcing the machine `tm` (with state numbering `eS`) to `universalTM`. -/
noncomputable def machineHeader {k : ℕ} {State : Type} [Fintype State]
    (eS : State ↪ ℕ) (tm : MultiTapeTM k Bool State) : List Bool :=
  frame (eDesc (desc eS eBit tm))

theorem universalTM_runFor_machineHeader_append {k : ℕ} {State : Type} [Fintype State]
    (eS : State ↪ ℕ) (tm : MultiTapeTM k Bool State) (w : List Bool) (t : ℕ) :
    (universalTM.run (machineHeader eS tm ++ w)).runFor t =
      ((ofMultiTapeTM tm).run w).runFor t := by
  rw [machineHeader, universalTM_runFor, universalTMRunFor_eq_ite, unframe_frame_append,
    decodeDesc_eDesc, dropFrame_frame_append, ← tm.runFor_eq_simulate eS w t]
  rfl

@[simp]
theorem universalTM_run_machineHeader_append {k : ℕ} {State : Type} [Fintype State]
    (eS : State ↪ ℕ) (tm : MultiTapeTM k Bool State) (w : List Bool) :
    universalTM.run (machineHeader eS tm ++ w) = (ofMultiTapeTM tm).run w := by
  change (⟨universalTMRunFor (machineHeader eS tm ++ w), _⟩ : Computation (List Bool)) =
    ⟨tm.runFor w, _⟩
  congr 1
  funext t
  exact universalTM_runFor_machineHeader_append eS tm w t

/-- **`universalTM` simulates every finite-state binary `MultiTapeTM` with constant program overhead
and zero time overhead.** -/
noncomputable def universalTMSimulation {k : ℕ} {State : Type} [Fintype State]
    (eS : State ↪ ℕ) (tm : MultiTapeTM k Bool State) :
    Simulation (ofMultiTapeTM tm) universalTM (machineHeader eS tm).length fun _ t => t where
  compile w := machineHeader eS tm ++ w
  length_compile_le w := by rw [List.length_append, Nat.add_comm]
  mem_runFor_compile h := by rwa [universalTM_runFor_machineHeader_append]

/-- Every finite-state binary `MultiTapeTM` is simulated by `universalTM` with constant program
overhead and zero time overhead. -/
theorem exists_simulation_ofMultiTapeTM {k : ℕ} {State : Type} [Finite State]
    (tm : MultiTapeTM k Bool State) :
    ∃ c : ℕ, Nonempty (Simulation (ofMultiTapeTM tm) universalTM c fun _ t => t) := by
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  exact ⟨(machineHeader eS tm).length, ⟨universalTMSimulation eS tm⟩⟩

/-- Plain Kolmogorov complexity under `universalTM` is at most an additive constant worse than
under any finite-state binary `MultiTapeTM`. -/
theorem exists_ecomplexity_universalTM_le_ofMultiTapeTM {k : ℕ} {State : Type} [Finite State]
    (tm : MultiTapeTM k Bool State) :
    ∃ c : ℕ, ∀ x : List Bool,
      universalTM.ecomplexity x ≤ (ofMultiTapeTM tm).ecomplexity x + c := by
  obtain ⟨c, ⟨S⟩⟩ := exists_simulation_ofMultiTapeTM tm
  exact ⟨c, S.ecomplexity_le⟩

/-- **Clock-preserving time-bounded optimality of `universalTM` over `MultiTapeTM`**: for every
finite-state binary `MultiTapeTM`, `universalTM` is at most an additive constant worse at the exact
same step count `t`. -/
theorem exists_etimeBoundedComplexity_universalTM_le_ofMultiTapeTM {k : ℕ} {State : Type}
    [Finite State] (tm : MultiTapeTM k Bool State) :
    ∃ c : ℕ, ∀ (t : ℕ) (x : List Bool),
      universalTM.etimeBoundedComplexity t x ≤
        (ofMultiTapeTM tm).etimeBoundedComplexity t x + c := by
  obtain ⟨c, ⟨S⟩⟩ := exists_simulation_ofMultiTapeTM tm
  exact ⟨c, fun t x => S.etimeBoundedComplexity_le (σ := id) t x⟩

/-- Time-bounded complexity transfer from a single-tape Turing machine `SingleTapeTM Bool` to
`universalTM`. -/
theorem exists_etimeBoundedComplexity_universalTM_le_ofSingleTapeTM (tm : SingleTapeTM Bool) :
    ∃ c : ℕ, ∀ {t k : ℕ} {x : List Bool},
      (ofSingleTapeTM tm).etimeBoundedComplexity t x ≤ k →
        universalTM.etimeBoundedComplexity (3 * k + 2 * t + 6) x ≤ (k + c : ℕ) := by
  obtain ⟨c, ⟨S⟩⟩ := exists_simulation_ofMultiTapeTM (MultiTapeTM.ofSingleTapeTM tm)
  refine ⟨c, fun {t k x} h => ?_⟩
  have h1 := etimeBoundedComplexity_ofMultiTapeTM_ofSingleTapeTM_le tm h
  have h2 := S.etimeBoundedComplexity_le (σ := id) (3 * k + 2 * t + 6) x
  rw [Nat.cast_add]
  exact h2.trans (add_le_add_left h1 _)

/-- `universalTM` simulates the `literal` description method with constant program overhead and
one extra step (`t + 1`). -/
theorem exists_simulation_literal_universalTM :
    ∃ c : ℕ, Nonempty (Simulation literal universalTM c fun _ t => t + 1) := by
  obtain ⟨k, State, hfin, tm, ⟨Slit⟩⟩ := exists_simulation_literal
  obtain ⟨c, ⟨Stm⟩⟩ := exists_simulation_ofMultiTapeTM tm
  exact ⟨0 + c, ⟨Slit.trans Stm fun _ _ _ _ => le_rfl⟩⟩

end DescriptionMethod

open DescriptionMethod

/-- Alias of `DescriptionMethod.exists_simulation_ofMultiTapeTM` matching the #798 M1 statement
shape: every finite-state binary `MultiTapeTM` is simulated by `universalTM` with constant program
overhead and no time overhead. -/
theorem simulation_ofMultiTapeTM {k : ℕ} {State : Type} [Finite State]
    (tm : MultiTapeTM k Bool State) :
    ∃ c : ℕ, Nonempty (Simulation (ofMultiTapeTM tm) universalTM c fun _ t => t) :=
  exists_simulation_ofMultiTapeTM tm

/-! ### Plain and time-bounded Kolmogorov complexity (`plain`, `timeBounded`) -/

/-- Plain Kolmogorov complexity $K(x)$ of a binary string $x$ under `universalTM`, in `ℕ∞`
(Decision D3). -/
noncomputable def plain (x : List Bool) : ℕ∞ :=
  universalTM.ecomplexity x

/-- Plain Kolmogorov complexity $K(x)$ of a binary string $x$ under `universalTM`, as a natural
number (Decision D3). Since every string has a finite description (`plain_ne_top`),
`(plainNat x : ℕ∞) = plain x` (`natCast_plainNat`). -/
noncomputable def plainNat (x : List Bool) : ℕ :=
  universalTM.complexity x

/-- Time-bounded Kolmogorov complexity $K^t(x)$ of a binary string $x$ with respect to the time
bound $t : \mathbb{N} \to \mathbb{N}$ ([Liu and Pass, Section 2.2][LiuPass2020]; Decisions D1–D3):
the length of a shortest binary program that outputs $x$ within $t(|x|)$ steps of the described
multi-tape machine, in `ℕ∞`. -/
noncomputable def timeBounded (t : ℕ → ℕ) (x : List Bool) : ℕ∞ :=
  universalTM.etimeBoundedComplexity (t x.length) x

/-- Time-bounded Kolmogorov complexity $K^t(x)$ as a natural number (Decision D3). Whenever a
program outputs $x$ within $t(|x|)$ steps (`timeBounded t x ≠ ⊤`),
`(timeBoundedNat t x : ℕ∞) = timeBounded t x` (`natCast_timeBoundedNat`). -/
noncomputable def timeBoundedNat (t : ℕ → ℕ) (x : List Bool) : ℕ :=
  (timeBounded t x).toNat

/-! ### Equivalence bridges between `ℕ∞` and finite (`ℕ`) formulations (Decision D3) -/

theorem timeBounded_le_natCast_iff {t : ℕ → ℕ} {x : List Bool} {k : ℕ} :
    timeBounded t x ≤ k ↔
      ∃ p : List Bool, p.length ≤ k ∧ x ∈ (universalTM.run p).runFor (t x.length) :=
  etimeBoundedComplexity_le_natCast_iff

theorem timeBounded_lt_natCast_iff {t : ℕ → ℕ} {x : List Bool} {k : ℕ} :
    timeBounded t x < k ↔
      ∃ p : List Bool, p.length < k ∧ x ∈ (universalTM.run p).runFor (t x.length) :=
  etimeBoundedComplexity_lt_natCast_iff

theorem timeBounded_eq_top_iff {t : ℕ → ℕ} {x : List Bool} :
    timeBounded t x = ⊤ ↔ ∀ p : List Bool, x ∉ (universalTM.run p).runFor (t x.length) :=
  etimeBoundedComplexity_eq_top_iff

theorem timeBounded_ne_top_iff {t : ℕ → ℕ} {x : List Bool} :
    timeBounded t x ≠ ⊤ ↔ ∃ p : List Bool, x ∈ (universalTM.run p).runFor (t x.length) := by
  simp [timeBounded_eq_top_iff]

/-- **Decision D3 bridge (`toNat` cast).** Whenever `timeBounded t x ≠ ⊤`, the natural-number
wrapper `timeBoundedNat t x` casts back to `timeBounded t x`. -/
theorem natCast_timeBoundedNat {t : ℕ → ℕ} {x : List Bool} (h : timeBounded t x ≠ ⊤) :
    (timeBoundedNat t x : ℕ∞) = timeBounded t x :=
  ENat.natCast_toNat h

/-- **Decision D3 bridge (threshold equivalence).** Whenever `timeBounded t x ≠ ⊤`, the `ℕ`-valued
inequality `timeBoundedNat t x ≤ k` is equivalent to `timeBounded t x ≤ k`. -/
theorem timeBoundedNat_le_iff {t : ℕ → ℕ} {x : List Bool} {k : ℕ} (h : timeBounded t x ≠ ⊤) :
    timeBoundedNat t x ≤ k ↔ timeBounded t x ≤ k := by
  rw [← ENat.natCast_le_natCast, natCast_timeBoundedNat h]

/-- **Decision D3 bridge (attainment).** Whenever `timeBounded t x ≠ ⊤`, `timeBoundedNat t x` is
the exact length of a shortest program outputting `x` within `t |x|` steps. -/
theorem exists_length_eq_timeBoundedNat {t : ℕ → ℕ} {x : List Bool} (h : timeBounded t x ≠ ⊤) :
    ∃ p : List Bool,
      x ∈ (universalTM.run p).runFor (t x.length) ∧ p.length = timeBoundedNat t x := by
  obtain ⟨p, hp, hlen⟩ := exists_length_eq_etimeBoundedComplexity h
  refine ⟨p, hp, ?_⟩
  have hcast : (p.length : ℕ∞) = (timeBoundedNat t x : ℕ∞) :=
    hlen.trans (natCast_timeBoundedNat h).symm
  exact ENat.natCast_inj.mp hcast

/-- **Decision D3 bridge (`sInf` in `ℕ` vs `ℕ∞`).** Whenever a witness program exists
(`timeBounded t x ≠ ⊤`), `timeBoundedNat t x` equals the `ℕ`-infimum
`sInf {p.length | x ∈ (universalTM.run p).runFor (t x.length)}`, matching the source definition
$K^t(x) = \min\{|\Pi| : U(\Pi, 1^{t(|x|)}) = x\}$ in [Liu and Pass, Section 2.2][LiuPass2020]. -/
theorem timeBoundedNat_eq_sInf {t : ℕ → ℕ} {x : List Bool} (h : timeBounded t x ≠ ⊤) :
    timeBoundedNat t x =
      sInf {k : ℕ | ∃ p : List Bool, p.length = k ∧
        x ∈ (universalTM.run p).runFor (t x.length)} := by
  obtain ⟨p₀, hp₀, hlen₀⟩ := exists_length_eq_timeBoundedNat h
  refine le_antisymm ?_ ?_
  · refine le_csInf ⟨p₀.length, p₀, rfl, hp₀⟩ ?_
    rintro k ⟨p, rfl, hp⟩
    rw [← ENat.natCast_le_natCast, natCast_timeBoundedNat h]
    exact etimeBoundedComplexity_le_length hp
  · exact Nat.sInf_le ⟨p₀, hlen₀, hp₀⟩

/-! ### Basic properties of `K^t`: monotonicity, upper bound, and relation to plain `K` -/

/-- **Monotonicity in the time bound.** Giving more time at input length `|x|` cannot increase
`K^t(x)`. -/
theorem timeBounded_mono_of_le {t₁ t₂ : ℕ → ℕ} {x : List Bool} (h : t₁ x.length ≤ t₂ x.length) :
    timeBounded t₂ x ≤ timeBounded t₁ x :=
  universalTM.etimeBoundedComplexity_mono h

/-- **Monotonicity in the time function.** If `t₁ ≤ t₂` pointwise, then `K^{t₂}(x) ≤ K^{t₁}(x)`. -/
theorem timeBounded_anti {t₁ t₂ : ℕ → ℕ} (h : t₁ ≤ t₂) (x : List Bool) :
    timeBounded t₂ x ≤ timeBounded t₁ x :=
  timeBounded_mono_of_le (h x.length)

/-- The fixed program overhead of the identity machine simulating `literal` in `universalTM`. -/
noncomputable def copyOverhead : ℕ :=
  Exists.choose exists_simulation_literal_universalTM

/-- Under `universalTM`, every string `x` can be printed by a program of length at most
`|x| + copyOverhead` within `|x| + 1` steps. -/
theorem etimeBoundedComplexity_universalTM_le_length_add {t : ℕ} {x : List Bool}
    (ht : x.length + 1 ≤ t) :
    universalTM.etimeBoundedComplexity t x ≤ (x.length + copyOverhead : ℕ) := by
  obtain ⟨S⟩ := Exists.choose_spec exists_simulation_literal_universalTM
  have h1 := (universalTM.etimeBoundedComplexity_mono ht).trans
    (S.etimeBoundedComplexity_le (σ := fun s => s + 1) x.length x)
  rwa [etimeBoundedComplexity_literal le_rfl, ← Nat.cast_add] at h1

/-- **Trivial upper bound** ([Liu and Pass, Fact 2.1][LiuPass2020] under multi-tape global output):
if $t(|x|) \ge |x| + 1$, then $K^t(x) \le |x| + \mathrm{copyOverhead}$. -/
theorem timeBounded_le_length_add {t : ℕ → ℕ} {x : List Bool}
    (ht : x.length + 1 ≤ t x.length) :
    timeBounded t x ≤ (x.length + copyOverhead : ℕ) :=
  etimeBoundedComplexity_universalTM_le_length_add ht

/-- **Trivial upper bound for all inputs** ([Liu and Pass, Fact 2.1][LiuPass2020]): if
$t(n) \ge n + 1$ for all $n$, then $K^t(x) \le |x| + \mathrm{copyOverhead}$ for all $x$. -/
theorem timeBounded_le {t : ℕ → ℕ} (ht : ∀ n, n + 1 ≤ t n) (x : List Bool) :
    timeBounded t x ≤ (x.length + copyOverhead : ℕ) :=
  timeBounded_le_length_add (ht x.length)

/-- Existential form of the trivial upper bound $K^t(x) \le |x| + O(1)$ for $t(n) \ge n + 1$. -/
theorem exists_timeBounded_le :
    ∃ c : ℕ, ∀ {t : ℕ → ℕ}, (∀ n, n + 1 ≤ t n) → ∀ x : List Bool,
      timeBounded t x ≤ (x.length + c : ℕ) :=
  ⟨copyOverhead, fun ht x => timeBounded_le ht x⟩

theorem timeBounded_ne_top {t : ℕ → ℕ} {x : List Bool} (ht : x.length + 1 ≤ t x.length) :
    timeBounded t x ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.natCast_ne_top _) (timeBounded_le_length_add ht)

theorem timeBoundedNat_le_length_add {t : ℕ → ℕ} {x : List Bool}
    (ht : x.length + 1 ≤ t x.length) :
    timeBoundedNat t x ≤ x.length + copyOverhead :=
  (timeBoundedNat_le_iff (timeBounded_ne_top ht)).mpr (timeBounded_le_length_add ht)

/-- **Relation to plain complexity (`K(x) ≤ K^t(x)`).** Dropping the time bound cannot increase
Kolmogorov complexity under `universalTM`. -/
theorem plain_le_timeBounded (t : ℕ → ℕ) (x : List Bool) :
    plain x ≤ timeBounded t x :=
  universalTM.ecomplexity_le_etimeBoundedComplexity (t x.length) x

theorem plain_le_length_add (x : List Bool) :
    plain x ≤ (x.length + copyOverhead : ℕ) :=
  (universalTM.ecomplexity_le_etimeBoundedComplexity (x.length + 1) x).trans
    (etimeBoundedComplexity_universalTM_le_length_add le_rfl)

theorem plain_ne_top (x : List Bool) : plain x ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.natCast_ne_top _) (plain_le_length_add x)

@[simp]
theorem natCast_plainNat (x : List Bool) : (plainNat x : ℕ∞) = plain x :=
  natCast_complexity (plain_ne_top x)

theorem plainNat_le_timeBoundedNat {t : ℕ → ℕ} {x : List Bool} (h : timeBounded t x ≠ ⊤) :
    plainNat x ≤ timeBoundedNat t x := by
  rw [← ENat.natCast_le_natCast, natCast_plainNat, natCast_timeBoundedNat h]
  exact plain_le_timeBounded t x

/-- Plain complexity `plain x` is the infimum of `universalTM.etimeBoundedComplexity t x` over all
step bounds `t : ℕ`. -/
theorem iInf_etimeBoundedComplexity_universalTM (x : List Bool) :
    (⨅ t : ℕ, universalTM.etimeBoundedComplexity t x) = plain x :=
  universalTM.iInf_etimeBoundedComplexity x

/-- **Relation to `Partrec.universal` (`K_U(dec x) ≤ K^t(x) + O(1)`).** For any computable decoder
`dec : List Bool → ℕ`, the plain complexity of `dec x` under `DescriptionMethod.universal`
(`Partrec.lean`) is at most `timeBounded t x + c`. -/
theorem exists_ecomplexity_universal_le_timeBounded {dec : List Bool → ℕ} (hdec : Computable dec) :
    ∃ c : ℕ, ∀ (t : ℕ → ℕ) (x : List Bool),
      universal.ecomplexity (dec x) ≤ timeBounded t x + c := by
  obtain ⟨c, hc⟩ := exists_ecomplexity_universal_le_universalTM hdec
  exact ⟨c, fun t x => (hc x).trans (add_le_add_left (plain_le_timeBounded t x) c)⟩

/-- Using `Nat.bits` and `List.foldr Nat.bit 0`,
`universal.ecomplexity n ≤ timeBounded t n.bits + c` for all `t` and `n`. -/
theorem exists_ecomplexity_universal_le_timeBounded_bits :
    ∃ c : ℕ, ∀ (t : ℕ → ℕ) (n : ℕ),
      universal.ecomplexity n ≤ timeBounded t n.bits + c := by
  obtain ⟨c, hc⟩ := exists_ecomplexity_universal_le_timeBounded Primrec.list_foldr_nat_bit.to_comp
  refine ⟨c, fun t n => ?_⟩
  simpa [Nat.foldr_bit_bits] using hc t n.bits

/-! ### Counting and incompressibility facts for `K^t` -/

/-- Fewer than $2^r$ strings of length $n$ have $K^t(x) < r$. -/
theorem encard_setOf_timeBounded_lt (t : ℕ → ℕ) (n r : ℕ) :
    {x : List Bool | x.length = n ∧ timeBounded t x < r}.encard < 2 ^ r := by
  refine (Set.encard_le_encard ?_).trans_lt
    (universalTM.encard_setOf_etimeBoundedComplexity_lt (t n) r)
  rintro x ⟨rfl, hx⟩
  exact hx

/-- Fewer than $2^{n - c}$ strings of length $n$ have $K^t(x) < n - c$. -/
theorem encard_setOf_length_eq_timeBounded_lt (t : ℕ → ℕ) (n c : ℕ) :
    {x : List Bool | x.length = n ∧ timeBounded t x < (n - c : ℕ)}.encard < 2 ^ (n - c) :=
  encard_setOf_timeBounded_lt t n (n - c)

/-- **Existence of $K^t$-incompressible strings.** For every $n$ and every time bound $t$, some
string $x \in \{0, 1\}^n$ has $K^t(x) \ge n$ (in fact, a single string works for all $t$
simultaneously). -/
theorem exists_length_eq_forall_le_timeBounded (n : ℕ) :
    ∃ x : List Bool, x.length = n ∧ ∀ t : ℕ → ℕ, (n : ℕ∞) ≤ timeBounded t x := by
  obtain ⟨x, hx, hall⟩ := universalTM.exists_length_eq_forall_le_etimeBoundedComplexity n
  exact ⟨x, hx, fun t => hall (t x.length)⟩

theorem exists_length_eq_le_timeBounded (t : ℕ → ℕ) (n : ℕ) :
    ∃ x : List Bool, x.length = n ∧ (n : ℕ∞) ≤ timeBounded t x := by
  obtain ⟨x, hx, hall⟩ := exists_length_eq_forall_le_timeBounded n
  exact ⟨x, hx, hall t⟩

/-- **Counting nearly $K^t$-incompressible strings.** All but fewer than $2^{n - c}$ of the $2^n$
strings of length $n$ satisfy $K^t(x) \ge n - c$. -/
theorem two_pow_lt_ncard_setOf_length_eq_le_timeBounded_add (t : ℕ → ℕ) (n c : ℕ) :
    2 ^ n < {x : List Bool | x.length = n ∧ (n - c : ℕ) ≤ timeBounded t x}.ncard +
      2 ^ (n - c) := by
  have h := universalTM.two_pow_lt_ncard_setOf_length_eq_le_ecomplexity_add n c
  refine h.trans_le (Nat.add_le_add_right (Set.ncard_le_ncard ?_ ?_) _)
  · rintro x ⟨hx, hplain⟩
    exact ⟨hx, hplain.trans (plain_le_timeBounded t x)⟩
  · exact (Set.finite_of_encard_eq_coe (BitString.encard_setOf_length_eq n)).subset fun _ hx => hx.1

/-! ### Levin's time-bounded Kolmogorov complexity (`Kt`) -/

/-- **Levin's time-bounded Kolmogorov complexity** $\mathrm{Kt}(x)$
([Levin][Levin1973]; [Liu and Pass, Section 2.2][LiuPass2021Crypto]):
$$\mathrm{Kt}(x) = \inf_{s \in \mathbb{N}} \bigl(K^s(x) + \lceil \log_2 s \rceil\bigr).$$
Because `universalTM.etimeBoundedComplexity 0 x = ⊤` (`etimeBoundedComplexity_universalTM_zero`),
the $s = 0$ term is $\top$ and the infimum over $s : \mathbb{N}$ coincides with the infimum over
$s \ge 1$. -/
noncomputable def levinKt (x : List Bool) : ℕ∞ :=
  ⨅ s : ℕ, universalTM.etimeBoundedComplexity s x + Nat.clog 2 s

/-- Levin's $\mathrm{Kt}(x)$ as a natural number (Decision D3). -/
noncomputable def levinKtNat (x : List Bool) : ℕ :=
  (levinKt x).toNat

/-- Restricting the infimum in `levinKt` to positive step counts $s > 0$ gives the exact same
value, since no program halts in $0$ steps (`etimeBoundedComplexity_universalTM_zero`). -/
theorem levinKt_eq_iInf_pos (x : List Bool) :
    levinKt x = ⨅ (s : ℕ) (_ : 0 < s), universalTM.etimeBoundedComplexity s x + Nat.clog 2 s := by
  refine le_antisymm (le_iInf₂ fun s _ => iInf_le _ s) (le_iInf fun s => ?_)
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  · exact iInf₂_le s hs

theorem levinKt_le_etimeBoundedComplexity_add (s : ℕ) (x : List Bool) :
    levinKt x ≤ universalTM.etimeBoundedComplexity s x + Nat.clog 2 s :=
  iInf_le _ s

theorem levinKt_le_timeBounded_add (t : ℕ → ℕ) (x : List Bool) :
    levinKt x ≤ timeBounded t x + Nat.clog 2 (t x.length) :=
  levinKt_le_etimeBoundedComplexity_add (t x.length) x

/-- Plain complexity bounds Levin's `Kt` from below (`K(x) ≤ Kt(x)`). -/
theorem plain_le_levinKt (x : List Bool) : plain x ≤ levinKt x :=
  le_iInf fun s => (universalTM.ecomplexity_le_etimeBoundedComplexity s x).trans le_self_add

/-- Trivial upper bound for Levin's `Kt`:
$\mathrm{Kt}(x) \le |x| + \mathrm{copyOverhead} + \lceil \log_2(|x| + 1) \rceil$. -/
theorem levinKt_le_length_add (x : List Bool) :
    levinKt x ≤ (x.length + copyOverhead + Nat.clog 2 (x.length + 1) : ℕ) := by
  refine (levinKt_le_etimeBoundedComplexity_add (x.length + 1) x).trans ?_
  rw [Nat.cast_add]
  exact add_le_add_left (etimeBoundedComplexity_universalTM_le_length_add le_rfl) _

theorem levinKt_ne_top (x : List Bool) : levinKt x ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.natCast_ne_top _) (levinKt_le_length_add x)

@[simp]
theorem natCast_levinKtNat (x : List Bool) : (levinKtNat x : ℕ∞) = levinKt x :=
  ENat.natCast_toNat (levinKt_ne_top x)

/-- **Threshold characterization of `levinKt` (Decision D3 bridge).** $\mathrm{Kt}(x) \le k$ iff
some program $p$ outputs $x$ within $s$ steps with $|p| + \lceil \log_2 s \rceil \le k$. -/
theorem levinKt_le_natCast_iff {x : List Bool} {k : ℕ} :
    levinKt x ≤ k ↔
      ∃ (p : List Bool) (s : ℕ),
        x ∈ (universalTM.run p).runFor s ∧ p.length + Nat.clog 2 s ≤ k := by
  rw [← ENat.lt_add_one_iff (ENat.natCast_ne_top k), levinKt, iInf_lt_iff]
  constructor
  · rintro ⟨s, hs⟩
    have hne : universalTM.etimeBoundedComplexity s x ≠ ⊤ := by
      intro htop
      rw [htop, top_add] at hs
      exact not_top_lt hs
    obtain ⟨p, hp, hlen⟩ := exists_length_eq_etimeBoundedComplexity hne
    rw [← hlen, ← Nat.cast_add, ← Nat.cast_add_one, ENat.natCast_lt_natCast,
      Nat.lt_add_one_iff] at hs
    exact ⟨p, s, hp, hs⟩
  · rintro ⟨p, s, hp, hle⟩
    refine ⟨s, ?_⟩
    have h1 : universalTM.etimeBoundedComplexity s x + Nat.clog 2 s ≤
        (p.length + Nat.clog 2 s : ℕ) := by
      rw [Nat.cast_add]
      exact add_le_add_left (etimeBoundedComplexity_le_length hp) _
    exact h1.trans_lt (by exact_mod_cast Nat.lt_add_one_of_le hle)

theorem levinKtNat_le_iff {x : List Bool} {k : ℕ} :
    levinKtNat x ≤ k ↔ levinKt x ≤ k := by
  rw [← ENat.natCast_le_natCast, natCast_levinKtNat]

end Cslib.Kolmogorov
