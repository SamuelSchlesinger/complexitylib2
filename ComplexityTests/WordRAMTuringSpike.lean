module

import Complexity.Computability.WordRAM.Turing
import Complexity.Computability.Complexity.Problems.ElementDistinctness

/-! Axiom audit for the #739 spike (local-only). -/

#print axioms Cslib.WordRAM.Program.ComputesInTime.computableInPolyTime
#print axioms Cslib.WordRAM.Basis.polyTimeOps_additive
#print axioms Cslib.WordRAM.Basis.polyTimeOps_arithmetic
#print axioms Cslib.WordRAM.Basis.polyTimeOps_standard
#print axioms Cslib.WordRAM.Program.DecidesInTime.mem_P
#print axioms Cslib.Algorithms.WordRAM.ElementDistinctness.nodup_mem_P
