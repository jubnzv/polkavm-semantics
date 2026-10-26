/-
The model interface and the Ψ₁ / Ψ / Ψ_H skeleton (gas charging, charged-flag bookkeeping).
Models supply the ISA, `gasCost` and `exec`.

`gasCost` is a cost-table sum, NOT the GP §"Gas Cost Model" pipeline simulation.
-/
import Pvm.Common.Isa

namespace Pvm

/-- Does this exit keep the machine going (continue) or merely suspend it (host call)?
    Used for the charged-flag reset rule (GP eq. for `𝔤*`). -/
def Exit.keepsGoing : Exit → Bool
  | .cont | .host _ => true
  | _ => false

/-- The per-model interface. -/
class PvmModel where
  isa     : Isa
  /-- Gas cost of the basic block starting at `pc` (GP `ζ^Δ`). Simplified; not the full OoO sim. -/
  gasCost : Program → Addr → Nat
  /-- Execute one decoded instruction: produce the exit reason and posterior state.
      Responsible for control-flow validity, memory faults, and the pc update. -/
  exec    : Program → Instr → State → Exit × State

namespace PvmModel

variable [M : PvmModel]

/-- Basic-block gas charging on entry (GP Ψ₁, the `ε^ξ` equation).
    Returns `(cont, s')` having charged (or already charged); `(oog, s)` if insufficient,
    leaving gas unchanged and the block uncharged so a later retry with more gas recharges. -/
def chargeBlock (p : Program) (s : State) : Exit × State :=
  if s.charged then
    (.cont, s)
  else
    let cost : Int := Int.ofNat (M.gasCost p (M.isa.basicBlockStart p s.pc))
    if s.gas ≥ cost then
      (.cont, { s with gas := s.gas - cost, charged := true })
    else
      (.oog, s)

/-- Single-step state transition Ψ₁. -/
def step (p : Program) (s : State) : Exit × State :=
  match M.isa.decode p s.pc with
  | none       => (.panic, s)        -- GP Ψ (~36): deblob(p, ı) fails before Ψ₁, ξ unchanged
  | some instr =>
    match chargeBlock p s with
    | (.oog, s') => (.oog, s')
    | (_,   s₁) =>
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

/-- Ψ_H (GP §752). On `host h`, service it with `f`; if that continues, resume at
    ı'' = `nextPc` ı', else propagate. `callBudget`/`runFuel` bound it for totality. The JAM
    context `X` is omitted. -/
def runHost (p : Program) (runFuel : Nat)
    (f : BitVec 32 → State → Exit × State) : Nat → State → Exit × State
  | 0,            s => (.cont, s)
  | callBudget+1, s =>
    match run p runFuel s with
    | (.host h, s') =>
      match f h s' with
      | (.cont, s'') => runHost p runFuel f callBudget { s'' with pc := M.isa.nextPc p s'.pc }
      | (e'',   s'') => (e'', s'')
    | other => other

end PvmModel
end Pvm
