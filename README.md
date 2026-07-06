# PolkaVM semantics
This repository contains an executable small-step semantics based on the [Graypaper](https://github.com/gavofyork/graypaper/).

> **Note**: It was created using an LLM from the [specification](https://github.com/gavofyork/graypaper/) to match the hand-written [common interfaces](./Pvm/Common). Not for production use.

## Scope
A PVM model derived from the Graypaper; some things are deliberately simplified/omitted:

* **Gas** — `gasCost` is a naive per-instruction cycle-sum, not the full out-of-order model `𝔛` (no pipeline simulation, no `max(cycles − 3, 1)` block adjustment).
* **Program decoding & validation** — the model consumes an already-split `⟨code, bitmask, jumpTable⟩` and validates only the instruction at the current `pc`; the `deblob` blob-parse and the whole-program `v_blob` check (linear-stream validity, `|k| = |c|`, terminating final instruction) are skipped, so a blob the Graypaper rejects wholesale may still run.
* **Program init** — only the RAM/register output layout (`Y`) is modelled; the JAM-blob prefix decoding (`E₃/E₂/E₄`) and the `Ψ_M` invocation envelope (gas reconciliation, halt output-blob extraction) are out of scope.
* **Host calls** — the `Ψ_H` host-call loop is modelled, but the JAM host context `X` is not — PVM-core only.
* **Memory** — per-page permissions are the coarse `{inaccessible, r, w}` (the Graypaper's separate *readable*/*writable* sets are merged); RAM is a static total map, so there is no on-demand dynamic paging.
* **Exit state** — on `halt`/`panic` the Graypaper zeroes the returned instruction counter; the model leaves `pc` at the offending instruction.
* **Execution is fuel-bounded** — a `cont` result means fuel was exhausted, not a property of the machine.

Where the Graypaper is ambiguous the model makes an explicit judgment call (grep `SPEC-AMBIGUITY` in `Pvm/Spec`): `𝔏` (basic-block start) defaults to `0` for malformed programs, the host id `immed_X` is truncated to its low 32 bits, and the memory access tag collapses the two permission sets as noted above.

## Use-cases
To check the correctness of the implementation(s). For example:
* **Equivalence checking** with an independent model based on the actual implementation
* **Conformance testing** – run the model against the official PVM test-vectors
* **Differential testing**

It was used to find implementation/specification mismatches in the real PolkaVM implementation:
* [Interpreter and recompiler disagree on the low-memory guard threshold](https://github.com/paritytech/polkavm/issues/390)
* [Recompiler miscompiles register nibbles 13–15 to the wrong register](https://github.com/paritytech/polkavm/issues/391)
* [Recompiler panics compiling a branch/jump whose target == `code_length+2` (off-by-one)](https://github.com/paritytech/polkavm/issues/392)

## License
MIT
