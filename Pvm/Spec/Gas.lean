/-
Spec model — gasCost: the `cost_cycles` column of GP §"Gas Cost Tables" (~1134) summed over a
basic block. NOT the GP 𝔛 model (no pipeline simulation, no `max(cycles - 3, 1)`, ~998).
-/
import Pvm.Common.Isa

namespace Pvm.Spec
open Pvm

-- GP ~1172 tests the octet ζ_j; here `j` is decoded, and no instruction there counts as `trap`.
def trapOrUnlikelyAt (d : Isa) (p : Program) (j : Nat) : Bool :=
  j ≥ 2 ^ 32 ||
    match d.decode p (BitVec.ofNat 32 j) with
    | none | some .trap | some .unlikely => true
    | _ => false

/-- 𝔟 (~1175). -/
def bcost (d : Isa) (p : Program) (pc : Addr) (t : Val) : Nat :=
  if trapOrUnlikelyAt d p (d.nextPc p pc).toNat || trapOrUnlikelyAt d p t.toNat then 1 else 20

/-- `cost_cycles`; `𝔪 = 25` (~1169). -/
def costCycles (d : Isa) (p : Program) (pc : Addr) : Instr → Nat
  | .moveReg .. => 0
  | .and .. | .xor .. | .or .. | .add64 .. | .sub64 .. => 1
  | .add32 .. | .sub32 .. => 2
  | .andImm .. | .xorImm .. | .orImm .. | .addImm64 .. | .shloRImm64 .. | .sharRImm64 ..
  | .shloLImm64 .. | .rotR64Imm .. | .reverseBytes .. => 1
  | .addImm32 .. | .shloRImm32 .. | .sharRImm32 .. | .shloLImm32 .. | .rotR32Imm .. => 2
  | .countSetBits64 .. | .countSetBits32 .. | .leadingZeroBits64 .. | .leadingZeroBits32 ..
  | .signExtend8 .. | .signExtend16 .. | .zeroExtend16 .. => 1
  | .trailingZeroBits64 .. | .trailingZeroBits32 .. => 2
  | .shloL64 .. | .shloR64 .. | .sharR64 .. | .rotL64 .. | .rotR64 .. => 1
  | .shloL32 .. | .shloR32 .. | .sharR32 .. | .rotL32 .. | .rotR32 .. => 2
  | .shloLImmAlt64 .. | .shloRImmAlt64 .. | .sharRImmAlt64 .. | .rotR64ImmAlt .. => 1
  | .shloLImmAlt32 .. | .shloRImmAlt32 .. | .sharRImmAlt32 .. | .rotR32ImmAlt .. => 2
  | .setLtU .. | .setLtS .. | .setLtUImm .. | .setLtSImm .. | .setGtUImm .. | .setGtSImm .. => 3
  | .cmovIz .. | .cmovNz .. | .cmovIzImm .. | .cmovNzImm .. => 2
  | .max .. | .maxU .. | .min .. | .minU .. => 3
  | .loadIndU8 .. | .loadIndI8 .. | .loadIndU16 .. | .loadIndI16 .. | .loadIndU32 ..
  | .loadIndI32 .. | .loadIndU64 ..
  | .loadU8 .. | .loadI8 .. | .loadU16 .. | .loadI16 .. | .loadU32 .. | .loadI32 .. | .loadU64 ..
  | .storeImmIndU8 .. | .storeImmIndU16 .. | .storeImmIndU32 .. | .storeImmIndU64 ..
  | .storeIndU8 .. | .storeIndU16 .. | .storeIndU32 .. | .storeIndU64 ..
  | .storeImmU8 .. | .storeImmU16 .. | .storeImmU32 .. | .storeImmU64 ..
  | .storeU8 .. | .storeU16 .. | .storeU32 .. | .storeU64 .. => 25
  | .branchEq _ _ t | .branchNe _ _ t | .branchLtU _ _ t | .branchLtS _ _ t
  | .branchGeU _ _ t | .branchGeS _ _ t
  | .branchEqImm _ _ t | .branchNeImm _ _ t | .branchLtUImm _ _ t | .branchLeUImm _ _ t
  | .branchGeUImm _ _ t | .branchGtUImm _ _ t | .branchLtSImm _ _ t | .branchLeSImm _ _ t
  | .branchGeSImm _ _ t | .branchGtSImm _ _ t => bcost d p pc t
  | .divU32 .. | .divS32 .. | .remU32 .. | .remS32 ..
  | .divU64 .. | .divS64 .. | .remU64 .. | .remS64 .. => 60
  | .andInv .. | .orInv .. | .xnor .. | .negAddImm64 .. => 2
  | .negAddImm32 .. => 3
  | .loadImm .. | .loadImm64 .. => 1
  | .mul64 .. | .mulImm64 .. => 3
  | .mul32 .. | .mulImm32 .. | .mulUpperSS .. | .mulUpperUU .. => 4
  | .mulUpperSU .. => 6
  | .trap | .fallthrough => 2
  | .unlikely => 40
  | .jump .. | .loadImmJump .. => 15
  | .jumpInd .. | .loadImmJumpInd .. => 22
  | .ecalli .. => 100

-- No instruction at `pc`: unreachable under v_blob (GP ~57); costed as `trap`, ending the walk.
def blockCost (d : Isa) (p : Program) (pc : Addr) : Nat → Nat
  | 0 => 0
  | fuel + 1 =>
    match d.decode p pc with
    | none => costCycles d p pc .trap
    | some i =>
      if i.isTerminator then costCycles d p pc i
      else costCycles d p pc i + blockCost d p (d.nextPc p pc) fuel

def gasCost (d : Isa) (p : Program) (pc : Addr) : Nat := blockCost d p pc (p.code.size + 1)

end Pvm.Spec
