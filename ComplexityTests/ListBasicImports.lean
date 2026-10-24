/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (list import regression tests)

import Complexity.Foundations.Data.List.Basic

/-! # The combined list import

Every original theorem remains usable from the old `Basic` import alone. The anonymous clients
check elaborated references, so dropping a topic from the re-export fails without another topic
import masking it. Actual library consumers use the narrow topic modules.
-/

example := @List.zip_tail_append_cons
example := @List.foldl_take_invariant
example := @List.foldr_ite_eq_of_mem
example := @List.length_flatMap_le
example := @List.decide_mem_eq_any
example := @List.getD_set_self
example := @List.getD_set_ne
example := @List.forall_mem_set_of_forall_mem
example := @List.getD_le_of_forall_le
example := @List.getD_mem_or
example := @List.getD_idxOf
example := @List.getD_map_range
example := @List.map_range_eq_ofFn
example := @List.countP_and_not_add_countP_and
example := @List.replicate_not_append_cons_inj
example := @List.replicate_true_append_false_inj
