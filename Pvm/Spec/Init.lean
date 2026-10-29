/-
Spec model — standard program initialization `Y` (Graypaper ~789, `sec:standardprograminit`).

`Y(𝐩, 𝐚)` splits the JAM blob into ro data `o`, rw data `w`, heap pages `z`, stack bytes `s` and the
PVM blob (eq:conditions ~802), then lays out RAM (eq:memlayout ~810) and registers
(eq:registers ~844).
-/
import Pvm.Spec.Serialization

namespace Pvm.Spec
open Pvm

/-- 2^32 — the address-space size (GP RAM is indexed mod 2^32). -/
def addrSpace : Nat := 4294967296

/-- GP `rnp` (~806): round up to the nearest `Z_P` (page) boundary. -/
def pageRound (x : Nat) : Nat := pageSize * ((x + pageSize - 1) / pageSize)
/-- GP `rnq` (~806): round up to the nearest `Z_Z` (zone) boundary. -/
def zoneRound (x : Nat) : Nat := zoneSize * ((x + zoneSize - 1) / zoneSize)

/-- The JAM blob's parts: ro data `o`, rw data `w`, heap pages `z`, stack bytes `s`, PVM blob. -/
structure Sections where
  ro    : Array UInt8 := #[]   -- 𝐨
  rw    : Array UInt8 := #[]   -- 𝐰
  heap  : Nat := 0             -- z  (extra heap pages)
  stack : Nat := 0             -- s  (stack size, bytes)
  code  : Array UInt8 := #[]   -- the PVM blob
  deriving Inhabited

/-- `E₃(|o|) ⌢ E₃(|w|) ⌢ E₂(z) ⌢ E₃(s) ⌢ o ⌢ w ⌢ E₄(|p|) ⌢ p` (GP ~802). The lengths are fixed-width,
    so a split that exists is the only one. -/
def sectionsAt (b : Array UInt8) : Option Sections := do
  let (lo, i) ← fixedAt b 0 3
  let (lw, i) ← fixedAt b i 3
  let (z, i) ← fixedAt b i 2
  let (s, i) ← fixedAt b i 3
  let (o, i) ← octetsAt b i lo
  let (w, i) ← octetsAt b i lw
  let (lp, i) ← fixedAt b i 4
  let (p, i) ← octetsAt b i lp
  guard (i = b.size)
  pure { ro := o, rw := w, heap := z, stack := s, code := p }

/-- `5Z_Z + rnq(|o|) + rnq(|w| + zZ_P) + rnq(s) + Z_I ≤ 2^32` (GP ~807). -/
def Sections.fits (sec : Sections) : Bool :=
  5 * zoneSize + zoneRound sec.ro.size + zoneRound (sec.rw.size + sec.heap * pageSize) +
    zoneRound sec.stack + inputSize ≤ addrSpace

/-! ## Region boundaries (GP eq:memlayout ~810) -/

def roBase    : Nat := zoneSize                                        -- Z_Z
def rwBase    (sec : Sections) : Nat := 2 * zoneSize + zoneRound sec.ro.size
def rwEnd     (sec : Sections) : Nat := rwBase sec + pageRound sec.rw.size + sec.heap * pageSize
def stackEnd  : Nat := addrSpace - 2 * zoneSize - inputSize            -- = SP (R1)
def stackBase (sec : Sections) : Nat := stackEnd - pageRound sec.stack
def argBase   : Nat := addrSpace - zoneSize - inputSize               -- = A0 (R7)

/-! ## Initial registers (GP eq:registers ~844) -/

def raInit : Nat := addrSpace - zoneSize                  -- 2^32 - 2^16 = 0xFFFF0000
def spInit : Nat := addrSpace - 2 * zoneSize - inputSize  -- 0xFEFE0000
def a0Init : Nat := addrSpace - zoneSize - inputSize      -- 0xFEFF0000

/-- GP `ω` at standard init: R0=RA, R1=SP, R7=A0, R8=A1=|a|, all others 0. -/
def stdInitRegs (argLen : Nat) : Reg → Val := fun r =>
  if r.val == 0 then BitVec.ofNat 64 raInit
  else if r.val == 1 then BitVec.ofNat 64 spInit
  else if r.val == 7 then BitVec.ofNat 64 a0Init
  else if r.val == 8 then BitVec.ofNat 64 argLen
  else 0

/-! ## Initial memory (GP eq:memlayout) — value per byte, access per page -/

/-- Per-byte initial RAM value: section bytes where present, else 0. -/
def stdInitValue (sec : Sections) (args : Array UInt8) (a : Addr) : UInt8 :=
  let i := a.toNat
  if roBase ≤ i ∧ i < roBase + sec.ro.size then (sec.ro[i - roBase]?).getD 0
  else if rwBase sec ≤ i ∧ i < rwBase sec + sec.rw.size then (sec.rw[i - rwBase sec]?).getD 0
  else if argBase ≤ i ∧ i < argBase + args.size then (args[i - argBase]?).getD 0
  else 0

/-- Per-page initial access (`pg` is the page key `addr >>> pageShift`; regions are page-aligned, so
    each page is uniformly one access).  ro/args ⇒ R (read-only); rw+heap/stack ⇒ W; else unmapped. -/
def stdInitAccess (sec : Sections) (args : Array UInt8) (pg : Addr) : Access :=
  let base := pg.toNat * pageSize
  if roBase ≤ base ∧ base < roBase + pageRound sec.ro.size then .r
  else if rwBase sec ≤ base ∧ base < rwEnd sec then .w
  else if stackBase sec ≤ base ∧ base < stackEnd then .w
  else if argBase ≤ base ∧ base < argBase + pageRound args.size then .r
  else .inaccessible

def stdInitMem (sec : Sections) (args : Array UInt8) : Mem :=
  { value := stdInitValue sec args, access := stdInitAccess sec args }

/-- `Y` (GP ~797): the PVM blob, `ω` and `μ`, or `∅` when no split satisfies eq:conditions. `𝐚` is
    `𝔹_{:Z_I}`; a longer one is outside `Y`'s domain and gives `∅`. -/
def Y (b args : Array UInt8) : Option (Array UInt8 × (Reg → Val) × Mem) := do
  guard (args.size ≤ inputSize)
  let sec ← sectionsAt b
  guard sec.fits
  pure (sec.code, stdInitRegs args.size, stdInitMem sec args)

/-- `Y`'s `ω` and `μ` as a machine state at `initPc` (gas/charged come from Ψ_M, GP ~857). -/
def stdInit (sec : Sections) (args : Array UInt8) (initPc : Addr) (gas : Int) : State :=
  { pc := initPc, gas := gas, charged := false,
    regs := stdInitRegs args.size, mem := stdInitMem sec args }

theorem ofLE_lt (o : Array UInt8) : ofLE o < 256 ^ o.size := by
  unfold ofLE
  rw [← Array.foldr_toList, ← Array.length_toList]
  induction o.toList with
  | nil => simp
  | cons v l ih =>
    simp only [List.foldr_cons, List.length_cons, Nat.pow_succ]
    have := v.toNat_lt
    omega

theorem fixedAt_lt {b : Array UInt8} {i l x n : Nat} (h : fixedAt b i l = some (x, n)) :
    x < 256 ^ l ∧ n = i + l := by
  simp only [fixedAt, octetsAt] at h
  split at h
  · simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := ofLE_lt (b.extract i (i + l))
    rw [Array.size_extract] at this
    exact ⟨by rwa [show min (i + l) b.size - i = l by omega] at this, rfl⟩
  · simp at h

theorem octetsAt_size {b o : Array UInt8} {i l n : Nat} (h : octetsAt b i l = some (o, n)) :
    o.size = l := by
  simp only [octetsAt] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, Array.size_extract]; omega
  · simp at h

/-- eq:conditions' bound (GP ~807) never fails: the length fields are too narrow to reach it. -/
theorem sectionsAt_fits {b : Array UInt8} {sec : Sections} (h : sectionsAt b = some sec) :
    sec.fits := by
  simp only [sectionsAt, bind, Option.bind_eq_some_iff, pure, guard] at h
  obtain ⟨⟨lo, i₁⟩, h₁, ⟨lw, i₂⟩, h₂, ⟨z, i₃⟩, h₃, ⟨s, i₄⟩, h₄, ⟨o, i₅⟩, h₅, ⟨w, i₆⟩, h₆,
    ⟨lp, i₇⟩, h₇, ⟨p, i₈⟩, h₈, h⟩ := h
  split at h
  · obtain ⟨_, _, h⟩ := h
    simp only [Option.some.injEq] at h
    subst h
    dsimp only at h₅ h₆ ⊢
    have := (fixedAt_lt h₁).1; have := (fixedAt_lt h₂).1
    have := (fixedAt_lt h₃).1; have := (fixedAt_lt h₄).1
    have := octetsAt_size h₅; have := octetsAt_size h₆
    simp only [Sections.fits, zoneRound, zoneSize, pageSize, inputSize, addrSpace, decide_eq_true_eq]
    omega
  · simp at h

-- GP eq:registers (~844).
example : raInit = 0xFFFF0000 := by decide
example : spInit = 0xFEFE0000 := by decide
example : a0Init = 0xFEFF0000 := by decide

end Pvm.Spec
