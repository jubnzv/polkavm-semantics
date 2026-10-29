/-
The model interface and the Ψ₁ / Ψ / Ψ_H skeleton (gas charging, charged-flag bookkeeping).
Models supply the ISA, `gasCost` and `exec`.
-/
import Pvm.Common.Isa

namespace Pvm

/-- Does this exit keep the machine going (continue) or merely suspend it (host call)?
    Used for the charged-flag reset rule (GP eq. for `𝔤*`). -/
def Exit.keepsGoing : Exit → Bool
  | .cont | .host _ => true
  | _ => false

/-- A host call's exit (GP ~782). -/
inductive HostExit | cont | panic | oog
  deriving DecidableEq, Repr, Inhabited

/-- 𝕏 (GP ~782): `f(h, ϱ, ω, μ, x) = (ε, ϱ', ω', μ', x')`. -/
abbrev HostFn (X : Type) :=
  Val → Int → (Reg → Val) → Mem → X → HostExit × Int × (Reg → Val) × Mem × X

/-- The per-model interface. -/
class PvmModel where
  isa     : Isa
  /-- Gas cost of the basic block starting at `pc` (GP `ϱ^Δ`, ~998). -/
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
  | none       => (.panic, s)        -- GP Ψ (~45): v_inst(c, k, ı) fails before Ψ₁, ξ unchanged
  | some instr =>
    match chargeBlock p s with
    | (.oog, s') => (.oog, s')
    | (_,   s₁) =>
      let (e, s₂) := M.exec p instr s₁
      -- charged-flag reset: drop it iff a block terminator continued / made a host call,
      -- so the next basic block is charged afresh (GP eq. for `𝔤*`).
      let reset := instr.isTerminator && e.keepsGoing
      (e, { s₂ with charged := !reset })

/-- Ψ (GP ~37) with fuel: `halt` and `panic` give ı = 0, other exits the prior ı, ω and μ. -/
def loop (p : Program) : Nat → State → Exit × State
  | 0,      s => (.cont, s)
  | fuel+1, s =>
    match step p s with
    | (.cont,  s') => loop p fuel s'
    | (.halt,  s') => (.halt, { s' with pc := 0 })
    | (.panic, s') => (.panic, { s' with pc := 0 })
    | (e,      s') => (e, { s' with pc := s.pc, regs := s.regs, mem := s.mem })

/-- Ψ; `cont` means the fuel ran out. v_blob (GP ~49) does not depend on ı, so it is tested once. -/
def run (p : Program) (fuel : Nat) (s : State) : Exit × State :=
  if fuel == 0 || M.isa.valid p then loop p fuel s else (.panic, { s with pc := 0 })

/-- Ψ on a program blob (GP ~45): a blob `deblob` rejects panics on the first step. -/
def runBlob (deblob : Array UInt8 → Option Program) (b : Array UInt8) (fuel : Nat)
    (s : State) : Exit × State :=
  match deblob b with
  | some p => run p fuel s
  | none   => if fuel == 0 then (.cont, s) else (.panic, { s with pc := 0 })

/-- What `run_ne_cont` needs of a model and a program. -/
structure Progress (p : Program) (K : Nat) : Prop where
  cost  : ∀ pc, 1 ≤ M.gasCost p pc
  gas   : ∀ i s, (M.exec p i s).2.gas = s.gas
  below : ∀ pc i, M.isa.decode p pc = some i → pc.toNat < K
  up    : ∀ i s s', M.isa.decode p s.pc = some i → i.isTerminator = false →
            M.exec p i s = (.cont, s') → s.pc.toNat < s'.pc.toNat

/-- An upper bound on the `cont` steps left from `s`. -/
def fuelBound (K : Nat) (s : State) : Nat :=
  s.gas.toNat * (K + 2) + if s.charged then K + 1 - s.pc.toNat else 0

theorem step_fuelBound {p : Program} {K : Nat} (h : Progress p K) {s s' : State}
    (hs : step p s = (.cont, s')) : fuelBound K s' < fuelBound K s := by
  unfold step at hs
  cases hi : M.isa.decode p s.pc with
  | none => simp [hi] at hs
  | some i =>
    simp only [hi] at hs
    have hk := h.below _ _ hi
    cases hc : s.charged
    · have h1 := h.cost (M.isa.basicBlockStart p s.pc)
      generalize hcost : M.gasCost p (M.isa.basicBlockStart p s.pc) = c at h1
      by_cases hge : (c : Int) ≤ s.gas
      · have hcb : chargeBlock p s = (.cont, { s with gas := s.gas - c, charged := true }) := by
          simp [chargeBlock, hc, hcost, hge]
        rw [hcb] at hs
        dsimp only at hs
        rcases hx : M.exec p i { s with gas := s.gas - c, charged := true } with ⟨e, s₂⟩
        have hg := h.gas i { s with gas := s.gas - c, charged := true }
        rw [hx] at hs hg
        simp only [Prod.mk.injEq] at hs
        obtain ⟨-, rfl⟩ := hs
        have hlt : s₂.gas.toNat + 1 ≤ s.gas.toNat := by simp at hg; omega
        have hle := Nat.mul_le_mul_right (K + 2) hlt
        rw [Nat.succ_mul] at hle
        simp only [fuelBound, hc]
        split <;> omega
      · have hcb : chargeBlock p s = (.oog, s) := by
          simp [chargeBlock, hc, hcost, Int.not_le.mp hge]
        rw [hcb] at hs
        simp at hs
    · have hcb : chargeBlock p s = (.cont, s) := by simp [chargeBlock, hc]
      rw [hcb] at hs
      dsimp only at hs
      rcases hx : M.exec p i s with ⟨e, s₂⟩
      have hg := h.gas i s
      rw [hx] at hs hg
      dsimp only at hg
      simp only [Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      cases ht : i.isTerminator
      · have hu := h.up i s s₂ hi ht hx
        simp only [fuelBound, hc, hg, Bool.false_and, Bool.not_false, if_true]
        omega
      · simp only [fuelBound, hc, hg, Exit.keepsGoing, Bool.and_self, Bool.not_true, if_true,
          Bool.false_eq_true, if_false]
        omega

theorem loop_le_fuelBound {p : Program} {K : Nat} (h : Progress p K) :
    ∀ fuel s, (loop p fuel s).1 = .cont → fuel ≤ fuelBound K s
  | 0, _, _ => Nat.zero_le _
  | fuel + 1, s, hc => by
    unfold loop at hc
    rcases hst : step p s with ⟨e, s'⟩
    rw [hst] at hc
    cases e with
    | cont =>
      have := loop_le_fuelBound h fuel s' hc
      have := step_fuelBound h hst
      omega
    | _ => simp at hc

/-- Ψ exits once its fuel exceeds `ξ·(K + 2) + K + 1`. -/
theorem run_ne_cont {p : Program} {K fuel : Nat} {s : State} (h : Progress p K)
    (hf : s.gas.toNat * (K + 2) + K + 1 < fuel) : (run p fuel s).1 ≠ .cont := by
  have hb : fuelBound K s ≤ s.gas.toNat * (K + 2) + K + 1 := by
    unfold fuelBound; split <;> omega
  unfold run
  split
  · intro hc
    have := loop_le_fuelBound h fuel s hc
    omega
  · simp

theorem run_halt_panic_pc {p : Program} {fuel : Nat} {s : State}
    (h : (run p fuel s).1 = .halt ∨ (run p fuel s).1 = .panic) : (run p fuel s).2.pc = 0 := by
  have : ∀ f s, (loop p f s).1 = .halt ∨ (loop p f s).1 = .panic → (loop p f s).2.pc = 0 := by
    intro f
    induction f with
    | zero => simp [loop]
    | succ f ih =>
      intro s h
      unfold loop at h ⊢
      rcases hst : step p s with ⟨e, s'⟩
      cases e <;> simp_all
  unfold run at h ⊢
  split <;> simp_all

/-- Ψ_H^* (GP ~756); `cont` means `calls` or `fuel` ran out. -/
def runHost {X : Type} (p : Program) (fuel : Nat) (f : HostFn X) :
    Nat → State → X → Exit × State × X
  | 0,         s, x => (.cont, s, x)
  | calls + 1, s, x =>
    match run p fuel s with
    | (.host h, s') =>
      match f h s'.gas s'.regs s'.mem x with
      | (.cont, g, r, m, x') =>
        runHost p fuel f calls
          { s' with pc := M.isa.nextPc p s'.pc, gas := g, regs := r, mem := m } x'
      | (.panic, g, r, m, x') => (.panic, { s' with gas := g, regs := r, mem := m }, x')
      | (.oog, g, r, m, x')   => (.oog, { s' with gas := g, regs := r, mem := m }, x')
    | (e, s') => (e, s', x)

/-- Ψ_H handles every host call itself (GP ~787). -/
theorem runHost_ne_host {X : Type} {p : Program} {fuel : Nat} {f : HostFn X} (h : Val) :
    ∀ n s x, (runHost p fuel f n s x).1 ≠ .host h
  | 0, _, _ => by simp [runHost]
  | n + 1, s, x => by
    unfold runHost
    rcases hr : run p fuel s with ⟨e, s'⟩
    cases e with
    | host h' =>
      simp only
      rcases f h' s'.gas s'.regs s'.mem x with ⟨_ | _ | _, g, r, m, x'⟩
      · exact runHost_ne_host h n _ _
      all_goals simp
    | _ => simp

end PvmModel
end Pvm
