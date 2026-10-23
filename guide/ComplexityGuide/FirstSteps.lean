/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import VersoManual
import Complexity.Computability.Complexity.CookLevin.Completeness

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "First Steps" =>
%%%
tag := "first-steps"
%%%

The package is named `complexitylib` and its modules begin with `Complexity.`; `import Complexity`
imports the whole library. Declarations use CSLib's namespaces: most begin with `Cslib`, and
Turing-machine declarations begin with `Turing`. This chapter imports one module,
`Complexity.Computability.Complexity.CookLevin.Completeness`, which proves the Cook–Levin theorem.

A decision problem is a set of instances, together with an encoding of instances as bit strings.
{name}`Cslib.Complexity.NPComplete` takes both:

```lean (name := npComplete)
#check Cslib.Complexity.NPComplete
```
```leanOutput npComplete
Cslib.Complexity.NPComplete {β : Type} (encB : β ↪ List Bool) (B : Set β) : Prop
```

The Cook–Levin theorem states that satisfiability of CNF formulas, under the library's encoding of
formulas, is NP-complete:

```lean (name := cookLevin)
open Cslib.Complexity CookLevin in
#check (SAT_npComplete : NPComplete encCNF SAT)
```
```leanOutput cookLevin
SAT_npComplete : NPComplete encCNF SAT
```

Hovering over a name shows its type and docstring, and clicking it opens its entry in the API
documentation.
