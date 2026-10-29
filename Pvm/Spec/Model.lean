/-
Spec model — exec dispatch and `Pvm.Spec.model : Isa → Pvm.PvmModel`.

Non-control instructions take the default transition ε = cont, ı' = `nextPc` ı (GP ~201).
`model` is a def, not an `instance`, so it coexists with other models.
-/
import Pvm.Common.Interface
import Pvm.Spec.ExecAlu
import Pvm.Spec.ExecMem
import Pvm.Spec.ExecControl
import Pvm.Spec.Gas

namespace Pvm.Spec
open Pvm

@[inline] def contNext (d : Isa) (p : Program) (s s' : State) : Exit × State :=
  (.cont, { s' with pc := d.nextPc p s.pc })

/-- Advance pc only on `cont`; faults/panics pass through. -/
@[inline] def memNext (d : Isa) (p : Program) (s : State) : Exit × State → Exit × State
  | (.cont, s') => (.cont, { s' with pc := d.nextPc p s.pc })
  | other       => other

def exec (d : Isa) (p : Program) (instr : Instr) (s : State) : Exit × State :=
  match instr with
  -- ── Control flow & traps — set their own pc/exit ──────────────────────────
  | .trap                  => execTrap s
  | .fallthrough           => execFallthrough d p s
  | .unlikely              => execUnlikely d p s
  | .ecalli x              => execEcalli s x
  | .jump t                => execJump d p s t
  | .jumpInd a x           => execJumpInd d p s a x
  | .loadImmJump a x t     => execLoadImmJump d p s a x t
  | .loadImmJumpInd a b x t => execLoadImmJumpInd d p s a b x t
  | .branchEqImm a x t     => execBranchEqImm d p s a x t
  | .branchNeImm a x t     => execBranchNeImm d p s a x t
  | .branchLtUImm a x t    => execBranchLtUImm d p s a x t
  | .branchLeUImm a x t    => execBranchLeUImm d p s a x t
  | .branchGeUImm a x t    => execBranchGeUImm d p s a x t
  | .branchGtUImm a x t    => execBranchGtUImm d p s a x t
  | .branchLtSImm a x t    => execBranchLtSImm d p s a x t
  | .branchLeSImm a x t    => execBranchLeSImm d p s a x t
  | .branchGeSImm a x t    => execBranchGeSImm d p s a x t
  | .branchGtSImm a x t    => execBranchGtSImm d p s a x t
  | .branchEq a b t        => execBranchEq d p s a b t
  | .branchNe a b t        => execBranchNe d p s a b t
  | .branchLtU a b t       => execBranchLtU d p s a b t
  | .branchLtS a b t       => execBranchLtS d p s a b t
  | .branchGeU a b t       => execBranchGeU d p s a b t
  | .branchGeS a b t       => execBranchGeS d p s a b t
  -- ── Memory loads/stores — advance pc on cont, else pass through ───────────
  | .storeImmU8 addr val   => memNext d p s (execStoreImmU8 s addr val)
  | .storeImmU16 addr val  => memNext d p s (execStoreImmU16 s addr val)
  | .storeImmU32 addr val  => memNext d p s (execStoreImmU32 s addr val)
  | .storeImmU64 addr val  => memNext d p s (execStoreImmU64 s addr val)
  | .loadU8 a x            => memNext d p s (execLoadU8 s a x)
  | .loadI8 a x            => memNext d p s (execLoadI8 s a x)
  | .loadU16 a x           => memNext d p s (execLoadU16 s a x)
  | .loadI16 a x           => memNext d p s (execLoadI16 s a x)
  | .loadU32 a x           => memNext d p s (execLoadU32 s a x)
  | .loadI32 a x           => memNext d p s (execLoadI32 s a x)
  | .loadU64 a x           => memNext d p s (execLoadU64 s a x)
  | .storeU8 a x           => memNext d p s (execStoreU8 s a x)
  | .storeU16 a x          => memNext d p s (execStoreU16 s a x)
  | .storeU32 a x          => memNext d p s (execStoreU32 s a x)
  | .storeU64 a x          => memNext d p s (execStoreU64 s a x)
  | .storeImmIndU8 a x val  => memNext d p s (execStoreImmIndU8 s a x val)
  | .storeImmIndU16 a x val => memNext d p s (execStoreImmIndU16 s a x val)
  | .storeImmIndU32 a x val => memNext d p s (execStoreImmIndU32 s a x val)
  | .storeImmIndU64 a x val => memNext d p s (execStoreImmIndU64 s a x val)
  | .storeIndU8 a b x      => memNext d p s (execStoreIndU8 s a b x)
  | .storeIndU16 a b x     => memNext d p s (execStoreIndU16 s a b x)
  | .storeIndU32 a b x     => memNext d p s (execStoreIndU32 s a b x)
  | .storeIndU64 a b x     => memNext d p s (execStoreIndU64 s a b x)
  | .loadIndU8 a b x       => memNext d p s (execLoadIndU8 s a b x)
  | .loadIndI8 a b x       => memNext d p s (execLoadIndI8 s a b x)
  | .loadIndU16 a b x      => memNext d p s (execLoadIndU16 s a b x)
  | .loadIndI16 a b x      => memNext d p s (execLoadIndI16 s a b x)
  | .loadIndU32 a b x      => memNext d p s (execLoadIndU32 s a b x)
  | .loadIndI32 a b x      => memNext d p s (execLoadIndI32 s a b x)
  | .loadIndU64 a b x      => memNext d p s (execLoadIndU64 s a b x)
  -- ── ALU / register / bit ops — default transition ────────────────────────
  | .loadImm64 a x         => contNext d p s (execLoadImm64 s a x)
  | .loadImm a x           => contNext d p s (execLoadImm s a x)
  | .moveReg r a           => contNext d p s (execMoveReg s r a)
  | .countSetBits64 r a    => contNext d p s (execCountSetBits64 s r a)
  | .countSetBits32 r a    => contNext d p s (execCountSetBits32 s r a)
  | .leadingZeroBits64 r a => contNext d p s (execLeadingZeroBits64 s r a)
  | .leadingZeroBits32 r a => contNext d p s (execLeadingZeroBits32 s r a)
  | .trailingZeroBits64 r a => contNext d p s (execTrailingZeroBits64 s r a)
  | .trailingZeroBits32 r a => contNext d p s (execTrailingZeroBits32 s r a)
  | .signExtend8 r a       => contNext d p s (execSignExtend8 s r a)
  | .signExtend16 r a      => contNext d p s (execSignExtend16 s r a)
  | .zeroExtend16 r a      => contNext d p s (execZeroExtend16 s r a)
  | .reverseBytes r a      => contNext d p s (execReverseBytes s r a)
  | .addImm32 a b x        => contNext d p s (execAddImm32 s a b x)
  | .andImm a b x          => contNext d p s (execAndImm s a b x)
  | .xorImm a b x          => contNext d p s (execXorImm s a b x)
  | .orImm a b x           => contNext d p s (execOrImm s a b x)
  | .mulImm32 a b x        => contNext d p s (execMulImm32 s a b x)
  | .setLtUImm a b x       => contNext d p s (execSetLtUImm s a b x)
  | .setLtSImm a b x       => contNext d p s (execSetLtSImm s a b x)
  | .shloLImm32 a b x      => contNext d p s (execShloLImm32 s a b x)
  | .shloRImm32 a b x      => contNext d p s (execShloRImm32 s a b x)
  | .sharRImm32 a b x      => contNext d p s (execSharRImm32 s a b x)
  | .negAddImm32 a b x     => contNext d p s (execNegAddImm32 s a b x)
  | .setGtUImm a b x       => contNext d p s (execSetGtUImm s a b x)
  | .setGtSImm a b x       => contNext d p s (execSetGtSImm s a b x)
  | .shloLImmAlt32 a b x   => contNext d p s (execShloLImmAlt32 s a b x)
  | .shloRImmAlt32 a b x   => contNext d p s (execShloRImmAlt32 s a b x)
  | .sharRImmAlt32 a b x   => contNext d p s (execSharRImmAlt32 s a b x)
  | .cmovIzImm a b x       => contNext d p s (execCmovIzImm s a b x)
  | .cmovNzImm a b x       => contNext d p s (execCmovNzImm s a b x)
  | .addImm64 a b x        => contNext d p s (execAddImm64 s a b x)
  | .mulImm64 a b x        => contNext d p s (execMulImm64 s a b x)
  | .shloLImm64 a b x      => contNext d p s (execShloLImm64 s a b x)
  | .shloRImm64 a b x      => contNext d p s (execShloRImm64 s a b x)
  | .sharRImm64 a b x      => contNext d p s (execSharRImm64 s a b x)
  | .negAddImm64 a b x     => contNext d p s (execNegAddImm64 s a b x)
  | .shloLImmAlt64 a b x   => contNext d p s (execShloLImmAlt64 s a b x)
  | .shloRImmAlt64 a b x   => contNext d p s (execShloRImmAlt64 s a b x)
  | .sharRImmAlt64 a b x   => contNext d p s (execSharRImmAlt64 s a b x)
  | .rotR64Imm a b x       => contNext d p s (execRotR64Imm s a b x)
  | .rotR64ImmAlt a b x    => contNext d p s (execRotR64ImmAlt s a b x)
  | .rotR32Imm a b x       => contNext d p s (execRotR32Imm s a b x)
  | .rotR32ImmAlt a b x    => contNext d p s (execRotR32ImmAlt s a b x)
  | .add32 a b r           => contNext d p s (execAdd32 s a b r)
  | .sub32 a b r           => contNext d p s (execSub32 s a b r)
  | .mul32 a b r           => contNext d p s (execMul32 s a b r)
  | .divU32 a b r          => contNext d p s (execDivU32 s a b r)
  | .divS32 a b r          => contNext d p s (execDivS32 s a b r)
  | .remU32 a b r          => contNext d p s (execRemU32 s a b r)
  | .remS32 a b r          => contNext d p s (execRemS32 s a b r)
  | .shloL32 a b r         => contNext d p s (execShloL32 s a b r)
  | .shloR32 a b r         => contNext d p s (execShloR32 s a b r)
  | .sharR32 a b r         => contNext d p s (execSharR32 s a b r)
  | .add64 a b r           => contNext d p s (execAdd64 s a b r)
  | .sub64 a b r           => contNext d p s (execSub64 s a b r)
  | .mul64 a b r           => contNext d p s (execMul64 s a b r)
  | .divU64 a b r          => contNext d p s (execDivU64 s a b r)
  | .divS64 a b r          => contNext d p s (execDivS64 s a b r)
  | .remU64 a b r          => contNext d p s (execRemU64 s a b r)
  | .remS64 a b r          => contNext d p s (execRemS64 s a b r)
  | .shloL64 a b r         => contNext d p s (execShloL64 s a b r)
  | .shloR64 a b r         => contNext d p s (execShloR64 s a b r)
  | .sharR64 a b r         => contNext d p s (execSharR64 s a b r)
  | .and a b r             => contNext d p s (execAnd s a b r)
  | .xor a b r             => contNext d p s (execXor s a b r)
  | .or a b r              => contNext d p s (execOr s a b r)
  | .mulUpperSS a b r      => contNext d p s (execMulUpperSS s a b r)
  | .mulUpperUU a b r      => contNext d p s (execMulUpperUU s a b r)
  | .mulUpperSU a b r      => contNext d p s (execMulUpperSU s a b r)
  | .setLtU a b r          => contNext d p s (execSetLtU s a b r)
  | .setLtS a b r          => contNext d p s (execSetLtS s a b r)
  | .cmovIz a b r          => contNext d p s (execCmovIz s a b r)
  | .cmovNz a b r          => contNext d p s (execCmovNz s a b r)
  | .rotL64 a b r          => contNext d p s (execRotL64 s a b r)
  | .rotL32 a b r          => contNext d p s (execRotL32 s a b r)
  | .rotR64 a b r          => contNext d p s (execRotR64 s a b r)
  | .rotR32 a b r          => contNext d p s (execRotR32 s a b r)
  | .andInv a b r          => contNext d p s (execAndInv s a b r)
  | .orInv a b r           => contNext d p s (execOrInv s a b r)
  | .xnor a b r            => contNext d p s (execXnor s a b r)
  | .max a b r             => contNext d p s (execMax s a b r)
  | .maxU a b r            => contNext d p s (execMaxU s a b r)
  | .min a b r             => contNext d p s (execMin s a b r)
  | .minU a b r            => contNext d p s (execMinU s a b r)

@[reducible] def model (d : Isa) : Pvm.PvmModel := {
  isa     := d
  gasCost := gasCost d
  exec    := exec d
}

theorem sjump_gas (d : Isa) (p : Program) (s : State) (b : Nat) : (sjump d p s b).2.gas = s.gas := by
  unfold sjump; split <;> rfl

theorem branch_gas (d : Isa) (p : Program) (s : State) (b : Nat) (c : Bool) :
    (branch d p s b c).2.gas = s.gas := by
  unfold branch; dsimp only; repeat' split
  all_goals rfl

theorem djump_gas (d : Isa) (p : Program) (s : State) (a : Nat) : (djump d p s a).2.gas = s.gas := by
  unfold djump; repeat' split
  all_goals first | rfl | exact sjump_gas ..

theorem doLoad_gas (s : State) (a : Reg) (addr : Addr) (n : Nat) (sg : Bool) :
    (doLoad s a addr n sg).2.gas = s.gas := by
  unfold doLoad; split <;> rfl

theorem doStore_gas (s : State) (addr : Addr) (n v : Nat) : (doStore s addr n v).2.gas = s.gas := by
  unfold doStore; split <;> rfl

theorem memNext_gas {d : Isa} {p : Program} {s : State} {r : Exit × State} (h : r.2.gas = s.gas) :
    (memNext d p s r).2.gas = s.gas := by
  unfold memNext; split <;> simp_all

theorem memNext_pc {d : Isa} {p : Program} {s s' : State} {r : Exit × State}
    (h : memNext d p s r = (.cont, s')) : s'.pc = d.nextPc p s.pc := by
  unfold memNext at h; split at h <;> simp_all; rw [← h]

theorem exec_gas (d : Isa) (p : Program) (i : Instr) (s : State) : (exec d p i s).2.gas = s.gas := by
  cases i <;> first
    | rfl
    | exact sjump_gas .. | exact branch_gas .. | exact djump_gas ..
    | exact memNext_gas (doLoad_gas ..) | exact memNext_gas (doStore_gas ..)

/-- A non-terminator that continues goes to `nextPc` (GP ~201). -/
theorem exec_next (d : Isa) (p : Program) (i : Instr) (s s' : State)
    (h : i.isTerminator = false) (he : exec d p i s = (.cont, s')) : s'.pc = d.nextPc p s.pc := by
  cases i <;> simp only [Instr.isTerminator, Bool.true_eq_false] at h <;> first
    | exact memNext_pc he
    | (simp only [exec, contNext, execUnlikely, Prod.mk.injEq] at he; rw [← he.2])
    | simp [exec, execEcalli] at he

theorem progress (d : Isa) (p : Program) (K : Nat)
    (hb : ∀ pc i, d.decode p pc = some i → pc.toNat < K)
    (hu : ∀ pc i, d.decode p pc = some i → pc.toNat < (d.nextPc p pc).toNat) :
    PvmModel.Progress (M := model d) p K :=
  @PvmModel.Progress.mk (model d) p K (gasCost_pos d p) (exec_gas d p) hb
    fun i s s' hi ht he => by rw [exec_next d p i s s' ht he]; exact hu _ _ hi

end Pvm.Spec
