# PolkaVM semantics
This repository contains an executable small-step semantics based on the [Graypaper](https://github.com/gavofyork/graypaper/) 0.8.0 (commit `e537514`).

Supported ISA:
* [ReviveV1](./Pvm/Isa/Revive.lean)
* [Latest64](./Pvm/Isa/L64.lean)

> **Note**: It was created using an LLM from the [specification](https://github.com/gavofyork/graypaper/) to match the hand-written [common interfaces](./Pvm/Common). Not for production use.

## Scope
Deliberately simplified or omitted:

* **Gas** -- a naive per-instruction cycle sum, not the full model `𝔛`.
* **Program validation** -- none for Latest64: GP 0.8.0 defines no container or `v_blob` for it.
* **Program init** -- only the RAM/register layout of `Y`.
* **Host calls** -- `Ψ_H` without the JAM host context `X`.
* **Memory** -- a static total map, no dynamic paging.
* **Exit state** -- on `halt`/`panic`, `pc` stays at the exiting instruction instead of `0`.
* **Execution** -- fuel-bounded; `cont` means fuel ran out.
* **`memset`, `sbrk`** -- not modelled.

## Departures from the Graypaper
* The `ecalli` host id is truncated to 32 bits.
* The branch cost `𝔟` counts a target with no valid instruction as `trap`.
* An index below `2^16` always panics, as the prose says (see [graypaper#446](https://github.com/gavofyork/graypaper/issues/446)).
* `𝔏` returns `0` when no block start is at or below `pc`.

## Use-cases
To check the correctness of the implementation(s). For example:
* **Equivalence checking** with an independent model based on the actual implementation
* **Conformance testing** -- run the model against the official PVM test-vectors
* **Differential testing**

It was used to find implementation/specification mismatches in the real PolkaVM implementation:
* [Interpreter and recompiler disagree on the low-memory guard threshold](https://github.com/paritytech/polkavm/issues/390)
* [Recompiler miscompiles register nibbles 13–15 to the wrong register](https://github.com/paritytech/polkavm/issues/391)
* [Recompiler panics compiling a branch/jump whose target == `code_length+2` (off-by-one)](https://github.com/paritytech/polkavm/issues/392)

## License
MIT
