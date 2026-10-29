/-
The ISA. Semantics, Ψ and gas see the encoding only through these five functions.
-/
import Pvm.Common.Ast

namespace Pvm

structure Isa where
  /-- v_blob(c, k, 0) (GP ~57); `false` ⇒ Ψ panics on its first step. -/
  valid           : Program → Bool
  /-- The instruction at `ı`; `none` ⇒ Ψ₁ panics. -/
  decode          : Program → Addr → Option Instr
  /-- The default successor ı' (GP ~201). -/
  nextPc          : Program → Addr → Addr
  /-- `j ∈ ϖ` (GP ~136). -/
  isBlockStart    : Program → Nat → Bool
  /-- 𝔏 (GP ~142). -/
  basicBlockStart : Program → Addr → Addr

end Pvm
