/-
Spec model — standard program initialization `Y` (Graypaper §789, `sec:standardprograminit`).

`Y(jam_blob, a)` decodes the JAM blob into the PVM blob + sections (ro `o`, rw `w`, heap pages `z`,
stack `s`) and lays out RAM + registers.  We model the OUTPUT layout (eq:memlayout ~810,
eq:registers ~844) as a function of the sections and the argument data `a`; the JAM-blob prefix
decoding (E₃/E₂/E₄, eq:conditions ~804) is the blob-format concern, not modelled here.
-/
import Pvm.Common.Types

namespace Pvm.Spec
open Pvm

/-- 2^32 — the address-space size (GP RAM is indexed mod 2^32). -/
def addrSpace : Nat := 4294967296

/-- GP `rnp` (~806): round up to the nearest `Z_P` (page) boundary. -/
def pageRound (x : Nat) : Nat := pageSize * ((x + pageSize - 1) / pageSize)
/-- GP `rnq` (~806): round up to the nearest `Z_Z` (zone) boundary. -/
def zoneRound (x : Nat) : Nat := zoneSize * ((x + zoneSize - 1) / zoneSize)

/-- The standard-init sections: ro data `o`, rw data `w`, heap pages `z`, stack bytes `s`, args `a`. -/
structure Sections where
  ro    : Array UInt8 := #[]   -- 𝐨
  rw    : Array UInt8 := #[]   -- 𝐰
  heap  : Nat := 0             -- z  (extra heap pages)
  stack : Nat := 0             -- s  (stack size, bytes)
  args  : Array UInt8 := #[]   -- 𝐚
  deriving Inhabited

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
def stdInitValue (sec : Sections) (a : Addr) : UInt8 :=
  let i := a.toNat
  if roBase ≤ i ∧ i < roBase + sec.ro.size then (sec.ro[i - roBase]?).getD 0
  else if rwBase sec ≤ i ∧ i < rwBase sec + sec.rw.size then (sec.rw[i - rwBase sec]?).getD 0
  else if argBase ≤ i ∧ i < argBase + sec.args.size then (sec.args[i - argBase]?).getD 0
  else 0

/-- Per-page initial access (`pg` is the page key `addr >>> pageShift`; regions are page-aligned, so
    each page is uniformly one access).  ro/args ⇒ R (read-only); rw+heap/stack ⇒ W; else unmapped. -/
def stdInitAccess (sec : Sections) (pg : Addr) : Access :=
  let base := pg.toNat * pageSize
  if roBase ≤ base ∧ base < roBase + pageRound sec.ro.size then .r
  else if rwBase sec ≤ base ∧ base < rwEnd sec then .w
  else if stackBase sec ≤ base ∧ base < stackEnd then .w
  else if argBase ≤ base ∧ base < argBase + pageRound sec.args.size then .r
  else .inaccessible

def stdInitMem (sec : Sections) : Mem :=
  { value := stdInitValue sec, access := stdInitAccess sec }

/-- `Y`'s posterior `⟨registers, μ⟩` (gas/charged come from the `Ψ_M` invocation, GP §853). -/
def stdInit (sec : Sections) (initPc : Addr) (gas : Int) : State :=
  { pc := initPc, gas := gas, charged := false,
    regs := stdInitRegs sec.args.size, mem := stdInitMem sec }

-- GP eq:registers (~844).
example : raInit = 0xFFFF0000 := by native_decide
example : spInit = 0xFEFE0000 := by native_decide
example : a0Init = 0xFEFF0000 := by native_decide

end Pvm.Spec
