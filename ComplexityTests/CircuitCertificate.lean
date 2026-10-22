/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Encoding.Certificate

/-! Certificate-length monotonicity needs only the certificate module. -/

open Cslib.Circuits.Boolean

example {m n : ℕ} (h : m ≤ n) (s : ℕ) : certLength m s ≤ certLength n s :=
  certLength_mono_left h s

example (n : ℕ) : certLength 0 0 ≤ certLength n 0 :=
  certLength_mono_left (Nat.zero_le n) 0
