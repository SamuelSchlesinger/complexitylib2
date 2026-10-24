/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
open Turing.MultiTapeTM
example : ComputableInPolyTime (fun p : List ℕ × ℕ =>
    (p.1.map (fun n => n + p.2)).filter (fun n => decide (n ≤ p.2)))
    (encPair (encList encUnary) encUnary) (encList encUnary) := by fun_prop
example {α : Type} {enc : α ↪ List Bool} :
    ComputableInPolyTime (fun p : List α × ℕ => p.1[p.2]?)
      (encPair (encList enc) encUnary) (encOption enc) := by fun_prop
example (value : Bool → Option Empty) :
    ComputableInPolyTime (fun b => (value b).elim false (fun e => Empty.elim e))
      encBool encBool := by
  let encE : Empty ↪ List Bool := ⟨Empty.elim, fun e => e.elim⟩
  exact ComputableInPolyTime.optionElimWithInput (encB := encE)
    (.of_finite value) (.of_finite _) (.of_finite _)
example : ComputableInPolyTime (fun n : ℕ => n * n + 1) encUnary encUnary := by fun_prop
run_meta do
  let env ← Lean.getEnv
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl' then
    throwError "retired original remains: foldl'"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.foldl' do
    throwError "plain counterpart missing: foldl'"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldlWith then
    throwError "retired original remains: foldlWith"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.foldlWith do
    throwError "plain counterpart missing: foldlWith"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldlWith_spec then
    throwError "retired original remains: foldlWith_spec"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.foldlWith_spec do
    throwError "plain counterpart missing: foldlWith_spec"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl_spec then
    throwError "retired original remains: foldl_spec"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.foldl_spec do
    throwError "plain counterpart missing: foldl_spec"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldlWith_of_bounded_growth then
    throwError "retired original remains: foldlWith_of_bounded_growth"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.foldlWith_of_bounded_growth do
    throwError "plain counterpart missing: foldlWith_of_bounded_growth"
  if env.contains
    `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldlWithInput_of_bounded_growth then
    throwError "retired original remains: foldlWithInput_of_bounded_growth"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.foldlWithInput_of_bounded_growth do
    throwError "plain counterpart missing: foldlWithInput_of_bounded_growth"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.foldl_of_bounded_growth then
    throwError "retired original remains: foldl_of_bounded_growth"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.foldl_of_bounded_growth do
    throwError "plain counterpart missing: foldl_of_bounded_growth"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionSome then
    throwError "retired original remains: optionSome"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.optionSome do
    throwError "plain counterpart missing: optionSome"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionIsSome then
    throwError "retired original remains: optionIsSome"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.optionIsSome do
    throwError "plain counterpart missing: optionIsSome"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionGetD then
    throwError "retired original remains: optionGetD"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.optionGetD do
    throwError "plain counterpart missing: optionGetD"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionGetDWithInput then
    throwError "retired original remains: optionGetDWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.optionGetDWithInput do
    throwError "plain counterpart missing: optionGetDWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.optionElimWithInput then
    throwError "retired original remains: optionElimWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.optionElimWithInput do
    throwError "plain counterpart missing: optionElimWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bool_toUnary then
    throwError "retired original remains: bool_toUnary"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.bool_toUnary do
    throwError "plain counterpart missing: bool_toUnary"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.polynomiallyBounded then
    throwError "retired original remains: polynomiallyBounded"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.polynomiallyBounded do
    throwError "plain counterpart missing: polynomiallyBounded"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.indexed_polynomial_bound then
    throwError "retired original remains: indexed_polynomial_bound"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.indexed_polynomial_bound do
    throwError "plain counterpart missing: indexed_polynomial_bound"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_add then
    throwError "retired original remains: unary_add"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.unary_add do
    throwError "plain counterpart missing: unary_add"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_sub then
    throwError "retired original remains: unary_sub"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.unary_sub do
    throwError "plain counterpart missing: unary_sub"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_mul then
    throwError "retired original remains: unary_mul"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.unary_mul do
    throwError "plain counterpart missing: unary_mul"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_min then
    throwError "retired original remains: unary_min"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.unary_min do
    throwError "plain counterpart missing: unary_min"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_max then
    throwError "retired original remains: unary_max"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.unary_max do
    throwError "plain counterpart missing: unary_max"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_le then
    throwError "retired original remains: unary_le"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.unary_le do
    throwError "plain counterpart missing: unary_le"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_lt then
    throwError "retired original remains: unary_lt"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.unary_lt do
    throwError "plain counterpart missing: unary_lt"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_le' then
    throwError "retired original remains: unary_le'"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.unary_le' do
    throwError "plain counterpart missing: unary_le'"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_lt' then
    throwError "retired original remains: unary_lt'"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.unary_lt' do
    throwError "plain counterpart missing: unary_lt'"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_beq then
    throwError "retired original remains: unary_beq"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.unary_beq do
    throwError "plain counterpart missing: unary_beq"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pair then
    throwError "retired original remains: unary_pair"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.unary_pair do
    throwError "plain counterpart missing: unary_pair"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pow then
    throwError "retired original remains: unary_pow"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.unary_pow do
    throwError "plain counterpart missing: unary_pow"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_eval then
    throwError "retired original remains: unary_eval"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.unary_eval do
    throwError "plain counterpart missing: unary_eval"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary then
    throwError "retired original remains: unary_to_binary"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.unary_to_binary do
    throwError "plain counterpart missing: unary_to_binary"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsAppend then
    throwError "retired original remains: bitsAppend"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.bitsAppend do
    throwError "plain counterpart missing: bitsAppend"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsCons then
    throwError "retired original remains: bitsCons"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.bitsCons do
    throwError "plain counterpart missing: bitsCons"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.headD then
    throwError "retired original remains: headD"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.headD do
    throwError "plain counterpart missing: headD"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listHeadDWithInput then
    throwError "retired original remains: listHeadDWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.listHeadDWithInput do
    throwError "plain counterpart missing: listHeadDWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.tail then
    throwError "retired original remains: tail"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.tail do
    throwError "plain counterpart missing: tail"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listIsEmpty then
    throwError "retired original remains: listIsEmpty"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.listIsEmpty do
    throwError "plain counterpart missing: listIsEmpty"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listIsEmpty' then
    throwError "retired original remains: listIsEmpty'"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.listIsEmpty' do
    throwError "plain counterpart missing: listIsEmpty'"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsIsEmpty then
    throwError "retired original remains: bitsIsEmpty"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.bitsIsEmpty do
    throwError "plain counterpart missing: bitsIsEmpty"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listTail then
    throwError "retired original remains: listTail"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.listTail do
    throwError "plain counterpart missing: listTail"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsTail then
    throwError "retired original remains: bitsTail"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.bitsTail do
    throwError "plain counterpart missing: bitsTail"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsReverse then
    throwError "retired original remains: bitsReverse"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.bitsReverse do
    throwError "plain counterpart missing: bitsReverse"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsReverseWithInput then
    throwError "retired original remains: bitsReverseWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.bitsReverseWithInput do
    throwError "plain counterpart missing: bitsReverseWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.cons then
    throwError "retired original remains: cons"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.cons do
    throwError "plain counterpart missing: cons"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listAppend then
    throwError "retired original remains: listAppend"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.listAppend do
    throwError "plain counterpart missing: listAppend"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.cons' then
    throwError "retired original remains: cons'"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.cons' do
    throwError "plain counterpart missing: cons'"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listAppend' then
    throwError "retired original remains: listAppend'"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.listAppend' do
    throwError "plain counterpart missing: listAppend'"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listReverse then
    throwError "retired original remains: listReverse"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.listReverse do
    throwError "plain counterpart missing: listReverse"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listReverseWithInput then
    throwError "retired original remains: listReverseWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.listReverseWithInput do
    throwError "plain counterpart missing: listReverseWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.findWith then
    throwError "retired original remains: findWith"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.findWith do
    throwError "plain counterpart missing: findWith"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.findWithInput then
    throwError "retired original remains: findWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.findWithInput do
    throwError "plain counterpart missing: findWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.filterWith then
    throwError "retired original remains: filterWith"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.filterWith do
    throwError "plain counterpart missing: filterWith"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.filterWithInput then
    throwError "retired original remains: filterWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.filterWithInput do
    throwError "plain counterpart missing: filterWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.filter then
    throwError "retired original remains: filter"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.filter do
    throwError "plain counterpart missing: filter"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapWith then
    throwError "retired original remains: mapWith"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.mapWith do
    throwError "plain counterpart missing: mapWith"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapWithInput then
    throwError "retired original remains: mapWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.mapWithInput do
    throwError "plain counterpart missing: mapWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.map then
    throwError "retired original remains: map"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.map do
    throwError "plain counterpart missing: map"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.head? then
    throwError "retired original remains: head?"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.head? do
    throwError "plain counterpart missing: head?"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapConst then
    throwError "retired original remains: mapConst"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.mapConst do
    throwError "plain counterpart missing: mapConst"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatten then
    throwError "retired original remains: flatten"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.flatten do
    throwError "plain counterpart missing: flatten"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapWith then
    throwError "retired original remains: flatMapWith"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.flatMapWith do
    throwError "plain counterpart missing: flatMapWith"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapWithInput then
    throwError "retired original remains: flatMapWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.flatMapWithInput do
    throwError "plain counterpart missing: flatMapWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.flatMapConst then
    throwError "retired original remains: flatMapConst"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.flatMapConst do
    throwError "plain counterpart missing: flatMapConst"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.mapFilterConst then
    throwError "retired original remains: mapFilterConst"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.mapFilterConst do
    throwError "plain counterpart missing: mapFilterConst"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.length then
    throwError "retired original remains: length"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.length do
    throwError "plain counterpart missing: length"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.length_list then
    throwError "retired original remains: length_list"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.length_list do
    throwError "plain counterpart missing: length_list"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.length_bits then
    throwError "retired original remains: length_bits"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.length_bits do
    throwError "plain counterpart missing: length_bits"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.encoding_length then
    throwError "retired original remains: encoding_length"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.encoding_length do
    throwError "plain counterpart missing: encoding_length"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.length_bits_comp then
    throwError "retired original remains: length_bits_comp"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.length_bits_comp do
    throwError "plain counterpart missing: length_bits_comp"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.countPWith then
    throwError "retired original remains: countPWith"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.countPWith do
    throwError "plain counterpart missing: countPWith"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.countPWithInput then
    throwError "retired original remains: countPWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.countPWithInput do
    throwError "plain counterpart missing: countPWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.countWithInput then
    throwError "retired original remains: countWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.countWithInput do
    throwError "plain counterpart missing: countWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.range then
    throwError "retired original remains: range"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.range do
    throwError "plain counterpart missing: range"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.replicate then
    throwError "retired original remains: replicate"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.replicate do
    throwError "plain counterpart missing: replicate"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.anyWithEncoding then
    throwError "retired original remains: anyWithEncoding"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.anyWithEncoding do
    throwError "plain counterpart missing: anyWithEncoding"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.allWithEncoding then
    throwError "retired original remains: allWithEncoding"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.allWithEncoding do
    throwError "plain counterpart missing: allWithEncoding"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.anyWith then
    throwError "retired original remains: anyWith"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.anyWith do
    throwError "plain counterpart missing: anyWith"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.allWith then
    throwError "retired original remains: allWith"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.allWith do
    throwError "plain counterpart missing: allWith"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.anyWithInput then
    throwError "retired original remains: anyWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.anyWithInput do
    throwError "plain counterpart missing: anyWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.allWithInput then
    throwError "retired original remains: allWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.allWithInput do
    throwError "plain counterpart missing: allWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.allConst then
    throwError "retired original remains: allConst"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.allConst do
    throwError "plain counterpart missing: allConst"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.anyConst then
    throwError "retired original remains: anyConst"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.anyConst do
    throwError "plain counterpart missing: anyConst"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.idxOf then
    throwError "retired original remains: idxOf"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.idxOf do
    throwError "plain counterpart missing: idxOf"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.idxOfWithInput then
    throwError "retired original remains: idxOfWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.idxOfWithInput do
    throwError "plain counterpart missing: idxOfWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.dropUnary then
    throwError "retired original remains: dropUnary"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.dropUnary do
    throwError "plain counterpart missing: dropUnary"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listDropWithInput then
    throwError "retired original remains: listDropWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.listDropWithInput do
    throwError "plain counterpart missing: listDropWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.takeUnary then
    throwError "retired original remains: takeUnary"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.takeUnary do
    throwError "plain counterpart missing: takeUnary"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listTakeWithInput then
    throwError "retired original remains: listTakeWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.listTakeWithInput do
    throwError "plain counterpart missing: listTakeWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.getElem? then
    throwError "retired original remains: getElem?"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.getElem? do
    throwError "plain counterpart missing: getElem?"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsDropWithInput then
    throwError "retired original remains: bitsDropWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.bitsDropWithInput do
    throwError "plain counterpart missing: bitsDropWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsTake then
    throwError "retired original remains: bitsTake"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.bitsTake do
    throwError "plain counterpart missing: bitsTake"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsTakeWithInput then
    throwError "retired original remains: bitsTakeWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.bitsTakeWithInput do
    throwError "plain counterpart missing: bitsTakeWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listGetD then
    throwError "retired original remains: listGetD"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.listGetD do
    throwError "plain counterpart missing: listGetD"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsGetD then
    throwError "retired original remains: bitsGetD"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.bitsGetD do
    throwError "plain counterpart missing: bitsGetD"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.bitsGetDWithInput then
    throwError "retired original remains: bitsGetDWithInput"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.bitsGetDWithInput do
    throwError "plain counterpart missing: bitsGetDWithInput"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.listGetD_binary then
    throwError "retired original remains: listGetD_binary"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.listGetD_binary do
    throwError "plain counterpart missing: listGetD_binary"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.zip then
    throwError "retired original remains: zip"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.zip do
    throwError "plain counterpart missing: zip"
  if env.contains `Turing.MultiTapeTM.ComputableTidilyInPolyTime.zipIdx then
    throwError "retired original remains: zipIdx"
  unless env.contains `Turing.MultiTapeTM.ComputableInPolyTime.zipIdx do
    throwError "plain counterpart missing: zipIdx"
