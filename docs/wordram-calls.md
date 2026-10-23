# Running a typed WordRAM operation

A `DynamicProgram D r` serves every operation of a stateful specification with one fixed
program. Call `P.eval w fuel o x` to deliver operation `o`'s arguments into the input registers,
run that program from persistent data `x`, and decode its typed observation. A successful result
is `some (y, answer, cost)`: use `y` for the next call. The type of `answer` is `D.Result o`,
which can depend on the operation.

The [checked stack examples](../ComplexityTests/WordRAMDynamic.lean) show a push returning
unit, a size query returning a natural number, and an empty pop returning `some none` after
mapping to its answer. The latter is a successful operation whose observation is `none`,
distinct from failure of the outer evaluator. For example, the push example checks:

```lean
example : ((Stack.implementation 4 2).eval 4 0 (.push 7) (Stack.initial 3)).map
    (fun (y, answer, cost) => (y.mem 3, y.regs Stack.len, answer, cost)) =
      some (7, 1, (), 8) := by decide
```

The cost already includes the final halt: this push executes seven body instructions and
charges eight. Argument delivery and decoding remain uncharged, as specified by
[`DynamicProgram`](../Complexity/Computability/WordRAM/Dynamic.lean). `fuel` bounds the number
of iterations of each structured loop per entry, rather than the total instruction count;
this loop-free push therefore succeeds with zero fuel. Fuel exhaustion, a machine fault, or
a decoder rejection returns outer `none`.

The [prefix-sums interpreter client](../ComplexityTests/WordRAMPrefixSums.lean) illustrates
repeated calls. It threads final data, accumulates the returned costs and collects typed
answers, without knowing the calling convention or output register. Its boundary queries
and overflow fault are checked on actual interpreter runs.

Evaluation does not establish admissibility or inspect every unused memory cell for word
bounds. With a certificate `C : DynamicCertificate P w`, a representation proof `hr`, an
admissibility proof `hv`, and a successful evaluation `he`, `C.execOp_of_eval hr hv he` supplies
an exact `ExecOp` trace with the returned cost. The stack tests check this use too. Existing
certificate realization theorems then connect that trace to the abstract operation and its
representation invariant; bounds on whole adaptive clients remain separate resource proofs.
