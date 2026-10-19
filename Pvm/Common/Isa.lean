/-
The ISA: the encoding facts the machine depends on. Semantics, Ψ₁ and gas reach the encoding
only through these four functions.
-/
import Pvm.Common.Ast

namespace Pvm

structure Isa where
  /-- The instruction at `ı`; `none` ⇒ Ψ₁ panics. -/
  decode          : Program → Addr → Option Instr
  /-- `ı + 1 + skip(ı)` (GP eq. ~201). -/
  nextPc          : Program → Addr → Addr
  /-- `j ∈ ϖ` (GP ~136). -/
  isBlockStart    : Program → Nat → Bool
  /-- 𝔏 (GP ~142). -/
  basicBlockStart : Program → Addr → Addr

end Pvm
