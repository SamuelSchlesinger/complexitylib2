/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Multiword.Mul
import Complexity.Computability.WordRAM.Multiword.Sub

/-! Old qualified names retain their original register parameter and reduce to the shared API. -/

namespace WordRAMDigitCompatibilityTests

open Cslib.WordRAM Cslib.WordRAM.Multiword

-- Compatibility tests deliberately exercise deprecated declarations.
set_option linter.deprecated false in
example {r : ℕ} (β : ℕ) (x : Data (r + 4)) (ds : List (Fin (r + 4))) :
    @Schoolbook.value r β x ds = value β x ds ∧
    (@Schoolbook.Bounded r β x ds ↔ Bounded β x ds) ∧
    @Difference.value r β x ds = value β x ds ∧
    (@Difference.Bounded r β x ds ↔ Bounded β x ds) :=
  ⟨rfl, Iff.rfl, rfl, Iff.rfl⟩

set_option linter.deprecated false in
example {r : ℕ} : @Schoolbook.setup r = @Workspace.setup r := rfl

set_option linter.deprecated false in
example {r : ℕ} (w : ℕ) (x : Data (r + 4)) :
    Schoolbook.setupResult w x = Workspace.setupResult w x := rfl

set_option linter.deprecated false in
example {r w : ℕ} (hw : 2 ≤ w) (x : Data (r + 4)) :
    Exec w Schoolbook.setup x (Schoolbook.setupResult w x) 6 :=
  Schoolbook.exec_setup hw x

set_option linter.deprecated false in
example {r : ℕ} (x y : Data (r + 4)) (ds : List (Fin (r + 4))) :
    Schoolbook.Frame x y ds ↔ Workspace.Frame x y ds := Iff.rfl

end WordRAMDigitCompatibilityTests
