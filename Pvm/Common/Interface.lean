/-
The shared interface both models implement, plus the Ψ₁ (single-step) / Ψ (run) skeleton.

Per the "interfaces only" rule: the *types* and the step/run *skeleton* (including real
per-basic-block gas charging and the charged-flag bookkeeping, GP Ψ₁) live here and are shared.
The *bodies* — `decode`, `basicBlockStart`, `gasCost`, `exec` — are supplied per model, so the
decoder and the semantics each stay independently equivalence-checkable.

`gasCost` is a simplified hook (cost-table sums), NOT the full out-of-order pipeline
simulation from GP §"Gas Cost Model".
-/
import Pvm.Common.Ast

namespace Pvm

/-- Does this exit keep the machine going (continue) or merely suspend it (host call)?
    Used for the charged-flag reset rule (GP eq. for `𝔤*`). -/
def Exit.keepsGoing : Exit → Bool
  | .cont | .host _ => true
  | _ => false

/-- The per-model interface. Bodies differ between the spec model and the impl model. -/
class PvmModel where
  /-- Decode the instruction whose opcode octet is at offset `pc`. `none` ⇒ invalid instruction. -/
  decode          : Program → Addr → Option Instr
  /-- Start of the basic block containing `pc` (GP `𝔏`). -/
  basicBlockStart : Program → Addr → Addr
  /-- Gas cost of the basic block starting at `pc` (GP `ζ^Δ`). Simplified; not the full OoO sim. -/
  gasCost         : Program → Addr → Nat
  /-- Execute one decoded instruction: produce the exit reason and posterior state.
      Responsible for control-flow validity, memory faults, and the pc update. -/
  exec            : Program → Instr → State → Exit × State

namespace PvmModel

variable [M : PvmModel]

/-- Basic-block gas charging on entry (GP Ψ₁, the `ε^ξ` equation).
    Returns `(cont, s')` having charged (or already charged); `(oog, s)` if insufficient,
    leaving gas unchanged and the block uncharged so a later retry with more gas recharges. -/
def chargeBlock (p : Program) (s : State) : Exit × State :=
  if s.charged then
    (.cont, s)
  else
    let cost : Int := Int.ofNat (M.gasCost p (M.basicBlockStart p s.pc))
    if s.gas ≥ cost then
      (.cont, { s with gas := s.gas - cost, charged := true })
    else
      (.oog, s)

/-- Single-step state transition Ψ₁. -/
def step (p : Program) (s : State) : Exit × State :=
  match chargeBlock p s with
  | (.oog, s') => (.oog, s')
  | (_,   s₁) =>
    match M.decode p s₁.pc with
    | none       => (.panic, s₁)        -- invalid instruction
    | some instr =>
      let (e, s₂) := M.exec p instr s₁
      -- charged-flag reset: drop it iff a block terminator continued / made a host call,
      -- so the next basic block is charged afresh (GP eq. for `𝔤*`).
      let reset := instr.isTerminator && e.keepsGoing
      (e, { s₂ with charged := !reset })

/-- Multi-step driver Ψ (fuel-bounded for totality). A `cont` result means fuel was exhausted. -/
def run (p : Program) : Nat → State → Exit × State
  | 0,      s => (.cont, s)
  | fuel+1, s =>
    match step p s with
    | (.cont, s') => run p fuel s'
    | (e,     s') => (e, s')

/-- Ψ_H (GP §752): the host-call state machine wrapping Ψ.  Run the inner machine to an exit; on a
    host-call `host h`, service it with `f` (`f h s' = (ε'', s'')`); if `ε''` continues, RESUME past
    the `ecalli` at `resume ı' = ı' + 1 + skip(ı')` (the GP `ı''`); otherwise propagate `ε''`.
    `callBudget` bounds the host-call count and `runFuel` each inner run (totality).  The JAM context
    `X` of the GP is omitted — out of PVM-core scope. -/
def runHost (p : Program) (runFuel : Nat) (resume : Addr → Addr)
    (f : BitVec 32 → State → Exit × State) : Nat → State → Exit × State
  | 0,            s => (.cont, s)
  | callBudget+1, s =>
    match run p runFuel s with
    | (.host h, s') =>
      match f h s' with
      | (.cont, s'') => runHost p runFuel resume f callBudget { s'' with pc := resume s'.pc }
      | (e'',   s'') => (e'', s'')
    | other => other

end PvmModel
end Pvm
