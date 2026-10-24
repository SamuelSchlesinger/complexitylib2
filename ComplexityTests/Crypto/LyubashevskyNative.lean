/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky.NativeExtract

/-! Runtime dimensions, signed challenge differences and total malformed-input behavior. -/

open Turing.MultiTapeTM Cslib.Crypto.Protocols.SigmaProtocol

example : lyubashevskyExtractList
    ((2, 1), (([false], some [0, 1]), ([true], some [1, 0]))) = [-1, 1, 1] := by
  decide +kernel

example : lyubashevskyExtractList
    ((1, 1), (([true], some [-2]), ([false], some [3]))) = [-5, -1] := by
  decide +kernel

-- Missing coordinates default to zero/false, while extra coordinates are ignored.
example : lyubashevskyExtractList
    ((3, 2), (([true, false, true], none), ([], some [7]))) = [-7, 0, 0, -1, 0] := by
  decide +kernel

example : lyubashevskyExtractList ((0, 0), (([true], some [7]), ([], none))) = [] := by
  decide +kernel

example : lyubashevskyExtractList ((0, 2), (([], none), ([true], none))) = [1, 0] := by
  decide +kernel

example : lyubashevskyExtractList ((2, 0), (([], none), ([], none))) = [0, 0] := by
  decide +kernel

example : lyubashevskyExtractWord [] = encList encIntBin [] := by decide +kernel

example (input : LyubashevskyExtractInput) :
    lyubashevskyExtractWord (encLyubashevskyExtractInput input) =
      encList encIntBin (lyubashevskyExtractList input) := lyubashevskyExtractWord_enc input

-- This is one word function for all dimensions and magnitudes, rather than fixed-size machines.
example : ComputableInPolyTime lyubashevskyExtractWord encBits encBits :=
  computableInPolyTime_lyubashevskyExtractWord

/-- info: 'Cslib.Crypto.Protocols.SigmaProtocol.computableInPolyTime_lyubashevskyExtractWord'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms computableInPolyTime_lyubashevskyExtractWord
