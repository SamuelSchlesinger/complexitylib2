/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.IP.GraphNonIsomorphism
import Complexity.Computability.Complexity.Classes.IP.Shamir
import Complexity.Computability.Complexity.Classes.MIP

/-! Multiprover interactive proofs (`MIP₂` and `MIP`), non-communicating provers, deterministic
prover optimality, transcript consistency, and the upper bound `MIP ⊆ NEXP`. -/

namespace ComplexityTests.MIP

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

/-! ### Non-communicating provers and transcript consistency -/

-- Querying channel `0` leaves channel `1`'s state untouched.
example (P : Fin 2 → Prover Unit) (word : List Bool) (s s' : ∀ i : Fin 2, (P i).State)
    (reply : List Bool)
    (hout : (reply, s') ∈ (((Prover.independent P).respond ((0 : Fin 2), word)).run s).support) :
    s' 1 = s 1 :=
  Prover.independent_state_eq_of_ne P ((0 : Fin 2), word) s s' reply (by decide : (1 : Fin 2) ≠ 0)
    hout

-- `projHistory` filters and extracts the `(query, reply)` pairs of a single prover channel.
example : MIP.projHistory 0
    [(0, ([true], [false])), (1, ([false], [true])), (0, ([true, false], [true]))] =
    [([true], [false]), ([true, false], [true])] := rfl

example : MIP.projHistory 1
    [(0, ([true], [false])), (1, ([false], [true])), (0, ([true, false], [true]))] =
    [([false], [true])] := rfl

-- Two histories that agree on their common prefix and then diverge in query are `consistentHist`.
example : MIP.consistentHist
    [([true], [false]), ([false], [true])]
    [([true], [false]), ([true], [false])] = true := rfl

-- Two histories that give different replies to the first common query are inconsistent.
example : MIP.consistentHist
    [([true], [false])]
    [([true], [true])] = false := rfl

/-! ### Non-vacuity: concrete `IsMultiproverProof` instance -/

-- Every single-prover interactive proof embeds into a two-prover interactive proof via channel 0.
example : IsMultiproverProof
    (fun x : Graph × Graph =>
      WordOracleComp.singleOracle (0 : Fin 2) (GraphNonIsomorphism.verifier x))
    GraphNonIsomorphism 1 ((17 / 32) ^ 2) :=
  GraphNonIsomorphism.isInteractiveProof_verifier.isMultiproverProof_singleOracle (0 : Fin 2)

-- GraphNonIsomorphism and TQBF belong to `MIP₂`, `MIP`, and `NEXP`.
example : GraphNonIsomorphism ∈ MIP₂ (encPair encGraph encGraph) :=
  IP_subset_MIP₂ _ GraphNonIsomorphism.mem_IP

example : GraphNonIsomorphism ∈ MIP (encPair encGraph encGraph) :=
  MIP₂_subset_MIP _ (IP_subset_MIP₂ _ GraphNonIsomorphism.mem_IP)

example : GraphNonIsomorphism ∈ NEXP (encPair encGraph encGraph) :=
  MIP₂_subset_NEXP _ (IP_subset_MIP₂ _ GraphNonIsomorphism.mem_IP)

example : TQBF ∈ MIP₂ encQBF :=
  IP_subset_MIP₂ _ (PSPACE_subset_IP _ TQBF_pspaceComplete.1)

example : TQBF ∈ NEXP encQBF :=
  MIP₂_subset_NEXP _ (IP_subset_MIP₂ _ (PSPACE_subset_IP _ TQBF_pspaceComplete.1))

/-! ### Axiom audit of the headline results -/

/-- info: 'Cslib.Complexity.Prover.independent_state_eq_of_ne' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Prover.independent_state_eq_of_ne

/--
info: 'Cslib.Complexity.IsInteractiveProof.isMultiproverProof_singleOracle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms IsInteractiveProof.isMultiproverProof_singleOracle

/-- info: 'Cslib.Complexity.MIP₂_subset_MIP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIP₂_subset_MIP

/-- info: 'Cslib.Complexity.IP_subset_MIP₂' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IP_subset_MIP₂

/-- info: 'Cslib.Complexity.PolyTimeReducible.mem_MIP₂' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolyTimeReducible.mem_MIP₂

/-- info: 'Cslib.Complexity.PolyTimeReducible.mem_MIP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PolyTimeReducible.mem_MIP

/-- info: 'Cslib.Complexity.MIP.acceptProb_eq_sum' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIP.acceptProb_eq_sum

/-- info: 'Cslib.Complexity.MIP.exists_deterministic_prover_family' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIP.exists_deterministic_prover_family

/-- info: 'Cslib.Complexity.MIP.DetProver.ValidFrom.consistentHist' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIP.DetProver.ValidFrom.consistentHist

/-- info: 'Cslib.Complexity.MIP.validFrom_candidateProver' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIP.validFrom_candidateProver

/-- info: 'Cslib.Complexity.MIP.paddedMIP_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIP.paddedMIP_mem_NP

/-- info: 'Cslib.Complexity.MIP.exists_detProver_of_checkCert' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIP.exists_detProver_of_checkCert

/-- info: 'Cslib.Complexity.MIP.exists_checkCert_of_detProver' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIP.exists_checkCert_of_detProver

/-- info: 'Cslib.Complexity.preimage_mem_NTIME_of_mem_NP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms preimage_mem_NTIME_of_mem_NP

/-- info: 'Cslib.Complexity.preimage_pad_mem_NEXP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms preimage_pad_mem_NEXP

/-- info: 'Cslib.Complexity.MIP_subset_NEXP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIP_subset_NEXP

/-- info: 'Cslib.Complexity.MIP₂_subset_NEXP' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MIP₂_subset_NEXP

end ComplexityTests.MIP
