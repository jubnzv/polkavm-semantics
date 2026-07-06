/-
Spec model — exec dispatch + the named `Pvm.Spec.model : Pvm.PvmModel`.

`exec` routes each decoded `Instr` to its ALU / memory / control-flow function. For
non-control instructions the posterior pc is the default `ı + 1 + skip(ı)` with ε = cont
(GP eq. ~201); control instructions set their own pc/exit.

This is a NAMED def (not an `instance`) so it coexists with a sibling impl model for
equivalence checking: `run (M := Pvm.Spec.model) …`.
-/
import Pvm.Common.Interface
import Pvm.Spec.Decode
import Pvm.Spec.ExecAlu
import Pvm.Spec.ExecMem
import Pvm.Spec.ExecControl
import Pvm.Spec.Gas

namespace Pvm.Spec
open Pvm

/-- Default transition wrapper for a pure register mutation: ε = cont, pc = ı+1+skip(ı). -/
@[inline] def contNext (p : Program) (s s' : State) : Exit × State :=
  (.cont, { s' with pc := nextPc p s })

/-- Memory-op wrapper: advance pc only on `cont`; pass faults/panics through unchanged. -/
@[inline] def memNext (p : Program) (s : State) : Exit × State → Exit × State
  | (.cont, s') => (.cont, { s' with pc := nextPc p s })
  | other       => other

/-- GP single-instruction execution (the four-method `exec`). -/
def exec (p : Program) (instr : Instr) (s : State) : Exit × State :=
  match instr with
  -- ── Control flow & traps — set their own pc/exit ──────────────────────────
  | .trap                  => execTrap s
  | .fallthrough           => execFallthrough p s
  | .unlikely              => execUnlikely p s
  | .ecalli x              => execEcalli s x
  | .jump t                => execJump p s t
  | .jumpInd a x           => execJumpInd p s a x
  | .loadImmJump a x t     => execLoadImmJump p s a x t
  | .loadImmJumpInd a b x t => execLoadImmJumpInd p s a b x t
  | .branchEqImm a x t     => execBranchEqImm p s a x t
  | .branchNeImm a x t     => execBranchNeImm p s a x t
  | .branchLtUImm a x t    => execBranchLtUImm p s a x t
  | .branchLeUImm a x t    => execBranchLeUImm p s a x t
  | .branchGeUImm a x t    => execBranchGeUImm p s a x t
  | .branchGtUImm a x t    => execBranchGtUImm p s a x t
  | .branchLtSImm a x t    => execBranchLtSImm p s a x t
  | .branchLeSImm a x t    => execBranchLeSImm p s a x t
  | .branchGeSImm a x t    => execBranchGeSImm p s a x t
  | .branchGtSImm a x t    => execBranchGtSImm p s a x t
  | .branchEq a b t        => execBranchEq p s a b t
  | .branchNe a b t        => execBranchNe p s a b t
  | .branchLtU a b t       => execBranchLtU p s a b t
  | .branchLtS a b t       => execBranchLtS p s a b t
  | .branchGeU a b t       => execBranchGeU p s a b t
  | .branchGeS a b t       => execBranchGeS p s a b t
  -- ── Memory loads/stores — advance pc on cont, else pass through ───────────
  | .storeImmU8 addr val   => memNext p s (execStoreImmU8 s addr val)
  | .storeImmU16 addr val  => memNext p s (execStoreImmU16 s addr val)
  | .storeImmU32 addr val  => memNext p s (execStoreImmU32 s addr val)
  | .storeImmU64 addr val  => memNext p s (execStoreImmU64 s addr val)
  | .loadU8 a x            => memNext p s (execLoadU8 s a x)
  | .loadI8 a x            => memNext p s (execLoadI8 s a x)
  | .loadU16 a x           => memNext p s (execLoadU16 s a x)
  | .loadI16 a x           => memNext p s (execLoadI16 s a x)
  | .loadU32 a x           => memNext p s (execLoadU32 s a x)
  | .loadI32 a x           => memNext p s (execLoadI32 s a x)
  | .loadU64 a x           => memNext p s (execLoadU64 s a x)
  | .storeU8 a x           => memNext p s (execStoreU8 s a x)
  | .storeU16 a x          => memNext p s (execStoreU16 s a x)
  | .storeU32 a x          => memNext p s (execStoreU32 s a x)
  | .storeU64 a x          => memNext p s (execStoreU64 s a x)
  | .storeImmIndU8 a x val  => memNext p s (execStoreImmIndU8 s a x val)
  | .storeImmIndU16 a x val => memNext p s (execStoreImmIndU16 s a x val)
  | .storeImmIndU32 a x val => memNext p s (execStoreImmIndU32 s a x val)
  | .storeImmIndU64 a x val => memNext p s (execStoreImmIndU64 s a x val)
  | .storeIndU8 a b x      => memNext p s (execStoreIndU8 s a b x)
  | .storeIndU16 a b x     => memNext p s (execStoreIndU16 s a b x)
  | .storeIndU32 a b x     => memNext p s (execStoreIndU32 s a b x)
  | .storeIndU64 a b x     => memNext p s (execStoreIndU64 s a b x)
  | .loadIndU8 a b x       => memNext p s (execLoadIndU8 s a b x)
  | .loadIndI8 a b x       => memNext p s (execLoadIndI8 s a b x)
  | .loadIndU16 a b x      => memNext p s (execLoadIndU16 s a b x)
  | .loadIndI16 a b x      => memNext p s (execLoadIndI16 s a b x)
  | .loadIndU32 a b x      => memNext p s (execLoadIndU32 s a b x)
  | .loadIndI32 a b x      => memNext p s (execLoadIndI32 s a b x)
  | .loadIndU64 a b x      => memNext p s (execLoadIndU64 s a b x)
  -- ── ALU / register / bit ops — default transition ────────────────────────
  | .loadImm64 a x         => contNext p s (execLoadImm64 s a x)
  | .loadImm a x           => contNext p s (execLoadImm s a x)
  | .moveReg d a           => contNext p s (execMoveReg s d a)
  | .countSetBits64 d a    => contNext p s (execCountSetBits64 s d a)
  | .countSetBits32 d a    => contNext p s (execCountSetBits32 s d a)
  | .leadingZeroBits64 d a => contNext p s (execLeadingZeroBits64 s d a)
  | .leadingZeroBits32 d a => contNext p s (execLeadingZeroBits32 s d a)
  | .trailingZeroBits64 d a => contNext p s (execTrailingZeroBits64 s d a)
  | .trailingZeroBits32 d a => contNext p s (execTrailingZeroBits32 s d a)
  | .signExtend8 d a       => contNext p s (execSignExtend8 s d a)
  | .signExtend16 d a      => contNext p s (execSignExtend16 s d a)
  | .zeroExtend16 d a      => contNext p s (execZeroExtend16 s d a)
  | .reverseBytes d a      => contNext p s (execReverseBytes s d a)
  | .addImm32 a b x        => contNext p s (execAddImm32 s a b x)
  | .andImm a b x          => contNext p s (execAndImm s a b x)
  | .xorImm a b x          => contNext p s (execXorImm s a b x)
  | .orImm a b x           => contNext p s (execOrImm s a b x)
  | .mulImm32 a b x        => contNext p s (execMulImm32 s a b x)
  | .setLtUImm a b x       => contNext p s (execSetLtUImm s a b x)
  | .setLtSImm a b x       => contNext p s (execSetLtSImm s a b x)
  | .shloLImm32 a b x      => contNext p s (execShloLImm32 s a b x)
  | .shloRImm32 a b x      => contNext p s (execShloRImm32 s a b x)
  | .sharRImm32 a b x      => contNext p s (execSharRImm32 s a b x)
  | .negAddImm32 a b x     => contNext p s (execNegAddImm32 s a b x)
  | .setGtUImm a b x       => contNext p s (execSetGtUImm s a b x)
  | .setGtSImm a b x       => contNext p s (execSetGtSImm s a b x)
  | .shloLImmAlt32 a b x   => contNext p s (execShloLImmAlt32 s a b x)
  | .shloRImmAlt32 a b x   => contNext p s (execShloRImmAlt32 s a b x)
  | .sharRImmAlt32 a b x   => contNext p s (execSharRImmAlt32 s a b x)
  | .cmovIzImm a b x       => contNext p s (execCmovIzImm s a b x)
  | .cmovNzImm a b x       => contNext p s (execCmovNzImm s a b x)
  | .addImm64 a b x        => contNext p s (execAddImm64 s a b x)
  | .mulImm64 a b x        => contNext p s (execMulImm64 s a b x)
  | .shloLImm64 a b x      => contNext p s (execShloLImm64 s a b x)
  | .shloRImm64 a b x      => contNext p s (execShloRImm64 s a b x)
  | .sharRImm64 a b x      => contNext p s (execSharRImm64 s a b x)
  | .negAddImm64 a b x     => contNext p s (execNegAddImm64 s a b x)
  | .shloLImmAlt64 a b x   => contNext p s (execShloLImmAlt64 s a b x)
  | .shloRImmAlt64 a b x   => contNext p s (execShloRImmAlt64 s a b x)
  | .sharRImmAlt64 a b x   => contNext p s (execSharRImmAlt64 s a b x)
  | .rotR64Imm a b x       => contNext p s (execRotR64Imm s a b x)
  | .rotR64ImmAlt a b x    => contNext p s (execRotR64ImmAlt s a b x)
  | .rotR32Imm a b x       => contNext p s (execRotR32Imm s a b x)
  | .rotR32ImmAlt a b x    => contNext p s (execRotR32ImmAlt s a b x)
  | .add32 a b d           => contNext p s (execAdd32 s a b d)
  | .sub32 a b d           => contNext p s (execSub32 s a b d)
  | .mul32 a b d           => contNext p s (execMul32 s a b d)
  | .divU32 a b d          => contNext p s (execDivU32 s a b d)
  | .divS32 a b d          => contNext p s (execDivS32 s a b d)
  | .remU32 a b d          => contNext p s (execRemU32 s a b d)
  | .remS32 a b d          => contNext p s (execRemS32 s a b d)
  | .shloL32 a b d         => contNext p s (execShloL32 s a b d)
  | .shloR32 a b d         => contNext p s (execShloR32 s a b d)
  | .sharR32 a b d         => contNext p s (execSharR32 s a b d)
  | .add64 a b d           => contNext p s (execAdd64 s a b d)
  | .sub64 a b d           => contNext p s (execSub64 s a b d)
  | .mul64 a b d           => contNext p s (execMul64 s a b d)
  | .divU64 a b d          => contNext p s (execDivU64 s a b d)
  | .divS64 a b d          => contNext p s (execDivS64 s a b d)
  | .remU64 a b d          => contNext p s (execRemU64 s a b d)
  | .remS64 a b d          => contNext p s (execRemS64 s a b d)
  | .shloL64 a b d         => contNext p s (execShloL64 s a b d)
  | .shloR64 a b d         => contNext p s (execShloR64 s a b d)
  | .sharR64 a b d         => contNext p s (execSharR64 s a b d)
  | .and a b d             => contNext p s (execAnd s a b d)
  | .xor a b d             => contNext p s (execXor s a b d)
  | .or a b d              => contNext p s (execOr s a b d)
  | .mulUpperSS a b d      => contNext p s (execMulUpperSS s a b d)
  | .mulUpperUU a b d      => contNext p s (execMulUpperUU s a b d)
  | .mulUpperSU a b d      => contNext p s (execMulUpperSU s a b d)
  | .setLtU a b d          => contNext p s (execSetLtU s a b d)
  | .setLtS a b d          => contNext p s (execSetLtS s a b d)
  | .cmovIz a b d          => contNext p s (execCmovIz s a b d)
  | .cmovNz a b d          => contNext p s (execCmovNz s a b d)
  | .rotL64 a b d          => contNext p s (execRotL64 s a b d)
  | .rotL32 a b d          => contNext p s (execRotL32 s a b d)
  | .rotR64 a b d          => contNext p s (execRotR64 s a b d)
  | .rotR32 a b d          => contNext p s (execRotR32 s a b d)
  | .andInv a b d          => contNext p s (execAndInv s a b d)
  | .orInv a b d           => contNext p s (execOrInv s a b d)
  | .xnor a b d            => contNext p s (execXnor s a b d)
  | .max a b d             => contNext p s (execMax s a b d)
  | .maxU a b d            => contNext p s (execMaxU s a b d)
  | .min a b d             => contNext p s (execMin s a b d)
  | .minU a b d            => contNext p s (execMinU s a b d)

/-- The Spec model: a named `PvmModel` value (NOT an `instance`; `@[reducible]` only silences
    the class-typed-def lint and does not register it for typeclass resolution). -/
@[reducible] def model : Pvm.PvmModel := {
  decode          := decode
  basicBlockStart := basicBlockStart
  gasCost         := gasCost
  exec            := exec
}

end Pvm.Spec
