/-
Core PVM state types.

Registers and RAM are modelled as total functions: this keeps the spec free of external
dependencies, and reads are computable. `State` is deliberately not `DecidableEq`; compare
specific registers and bytes instead.

Reference: (Graypaper App. A, "Basic Definition")
-/
import Pvm.Common.Bits

namespace Pvm

/-- Register index. RA=0, SP=1, T0..T2, S0..S1, A0=7, A1=8, A2..A5. There is no `x0`. -/
abbrev Reg := Fin 13

/-! ## Constants (GP App. A) -/

def pageShift : Nat  := 12
def pageSize  : Nat  := 4096          -- Z_P
def zoneSize  : Nat  := 65536         -- Z_Z = 2^16
def inputSize : Nat  := 16777216      -- Z_I = 2^24
def haltAddr  : Addr := 0xFFFF0000    -- 2^32 - 2^16 (a djump here ⇒ halt)
def dynAlign  : Nat  := 2             -- dynamic-jump alignment factor

/-- Per-page access permission. Absence of `r`/`w` ⇒ the page is unmapped. -/
inductive Access | inaccessible | r | w
  deriving DecidableEq, Repr, Inhabited

/-- PVM exit reason `ε`. `cont` is Ψ₁'s internal "keep going" marker. -/
inductive Exit
  | cont
  | halt
  | panic
  | oog
  | fault (page : Addr)
  | host  (id : BitVec 32)
  deriving DecidableEq, Repr, Inhabited

/-- RAM `μ`: a byte per 32-bit address, and a permission per page (keyed by `addr >>> pageShift`). -/
structure Mem where
  value  : Addr → UInt8
  access : Addr → Access
  deriving Inhabited

@[inline] def Mem.readByte (m : Mem) (a : Addr) : UInt8 := m.value a
@[inline] def Mem.accessAt (m : Mem) (a : Addr) : Access := m.access (a >>> pageShift)
@[inline] def Mem.writeByte (m : Mem) (a : Addr) (b : UInt8) : Mem :=
  { m with value := fun a' => if a' = a then b else m.value a' }

/-- The Ψ machine configuration. The program blob is threaded separately (see `Program`). -/
structure State where
  pc      : Addr        -- ı, an octet offset into the instruction data
  gas     : Int         -- ξ, signed; `< 0` after a charge would be out-of-gas
  charged : Bool        -- whether the current basic block's gas has been charged
  regs    : Reg → Val   -- ω
  mem     : Mem         -- μ
  deriving Inhabited

@[inline] def State.reg (s : State) (r : Reg) : Val := s.regs r
@[inline] def State.setReg (s : State) (r : Reg) (v : Val) : State :=
  { s with regs := fun r' => if r' = r then v else s.regs r' }

/-- The dynamic jump table `j` (GP ~52): `len` entries, `entries` then zeros. With `z = 0` every
    entry is `E₀ = []`, so the blob does not bound `len`. -/
structure JumpTable where
  len     : Nat
  entries : Array Val
  deriving Inhabited, Repr

def JumpTable.ofArray (a : Array Val) : JumpTable := { len := a.size, entries := a }

/-- `j_i`. -/
def JumpTable.get? (t : JumpTable) (i : Nat) : Option Val :=
  if i < t.len then some (t.entries[i]?.getD 0) else none

/-- A decoded PVM program blob: instruction data `c`, opcode bitmask `k`, jump table `j`.
    `bitmask` is empty for an ISA that does not use one. -/
structure Program where
  code      : Array UInt8
  bitmask   : Array Bool
  jumpTable : JumpTable
  deriving Inhabited, Repr

end Pvm
