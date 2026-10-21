/-
Spec model — control-flow & trap instructions: sjump (~248), branch (~256), djump (~267).

Per Ψ₁ (~184) a register posterior (`load_imm_jump`'s reg'_A) is applied even when the control
verdict is panic/halt.
-/
import Pvm.Common.Isa

namespace Pvm.Spec
open Pvm

/-! ## Control-flow primitives -/

def sjump (d : Isa) (p : Program) (s : State) (b : Nat) : Exit × State :=
  if d.isBlockStart p b then (.cont, { s with pc := BitVec.ofNat 32 b }) else (.panic, s)

/-- Both `b` and the fallthrough `ft` must be in ϖ, taken or not. -/
def branch (d : Isa) (p : Program) (s : State) (b : Nat) (c : Bool) : Exit × State :=
  let ft := (d.nextPc p s.pc).toNat
  if !(d.isBlockStart p b) || !(d.isBlockStart p ft) then (.panic, s)
  else if c then (.cont, { s with pc := BitVec.ofNat 32 b })
  else (.cont, { s with pc := BitVec.ofNat 32 ft })

def djump (d : Isa) (p : Program) (s : State) (a : Nat) : Exit × State :=
  if a == haltAddr.toNat then (.halt, s)
  else if a == 0 || a > p.jumpTable.size * dynAlign || a % dynAlign != 0 then (.panic, s)
  else
    match p.jumpTable[a / dynAlign - 1]? with
    | some tgt => if d.isBlockStart p tgt.toNat then (.cont, { s with pc := tgt }) else (.panic, s)
    | none     => (.panic, s)

/-! ## No arguments -/

def execTrap (s : State) : Exit × State := (.panic, s)
def execFallthrough (d : Isa) (p : Program) (s : State) : Exit × State :=
  sjump d p s (d.nextPc p s.pc).toNat
def execUnlikely (d : Isa) (p : Program) (s : State) : Exit × State :=
  (.cont, { s with pc := d.nextPc p s.pc })

/-! ## One immediate -/

-- The GP's host id is the 64-bit immed_X (~74, ~311); `Exit.host` keeps its low 32 bits.
-- pc stays at the ecalli (GP ~77).
def execEcalli (s : State) (x : Val) : Exit × State := (.host (x.setWidth 32), s)

/-! ## One offset -/

def execJump (d : Isa) (p : Program) (s : State) (target : Val) : Exit × State :=
  sjump d p s target.toNat

/-! ## One register & one immediate -/

-- djump((reg_A + immed_X) mod 2^32)
def execJumpInd (d : Isa) (p : Program) (s : State) (a : Reg) (x : Val) : Exit × State :=
  djump d p s ((s.reg a + x).setWidth 32).toNat

/-! ## One register, one immediate & one offset -/

def execLoadImmJump (d : Isa) (p : Program) (s : State) (a : Reg) (x target : Val) : Exit × State :=
  sjump d p (s.setReg a x) target.toNat

private def doBranch (d : Isa) (p : Program) (s : State) (c : Bool) (t : Val) : Exit × State :=
  branch d p s t.toNat c

def execBranchEqImm  (d : Isa) (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranch d p s (s.reg a == x) t
def execBranchNeImm  (d : Isa) (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranch d p s (s.reg a != x) t
def execBranchLtUImm (d : Isa) (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranch d p s ((s.reg a).ult x) t
def execBranchLeUImm (d : Isa) (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranch d p s ((s.reg a).ule x) t
def execBranchGeUImm (d : Isa) (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranch d p s (x.ule (s.reg a)) t
def execBranchGtUImm (d : Isa) (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranch d p s (x.ult (s.reg a)) t
def execBranchLtSImm (d : Isa) (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranch d p s ((s.reg a).slt x) t
def execBranchLeSImm (d : Isa) (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranch d p s ((s.reg a).sle x) t
def execBranchGeSImm (d : Isa) (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranch d p s (x.sle (s.reg a)) t
def execBranchGtSImm (d : Isa) (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranch d p s (x.slt (s.reg a)) t

/-! ## Two registers & one offset -/

def execBranchEq  (d : Isa) (p : Program) (s : State) (a b : Reg) (t : Val) : Exit × State := doBranch d p s (s.reg a == s.reg b) t
def execBranchNe  (d : Isa) (p : Program) (s : State) (a b : Reg) (t : Val) : Exit × State := doBranch d p s (s.reg a != s.reg b) t
def execBranchLtU (d : Isa) (p : Program) (s : State) (a b : Reg) (t : Val) : Exit × State := doBranch d p s ((s.reg a).ult (s.reg b)) t
def execBranchLtS (d : Isa) (p : Program) (s : State) (a b : Reg) (t : Val) : Exit × State := doBranch d p s ((s.reg a).slt (s.reg b)) t
def execBranchGeU (d : Isa) (p : Program) (s : State) (a b : Reg) (t : Val) : Exit × State := doBranch d p s ((s.reg b).ule (s.reg a)) t
def execBranchGeS (d : Isa) (p : Program) (s : State) (a b : Reg) (t : Val) : Exit × State := doBranch d p s ((s.reg b).sle (s.reg a)) t

/-! ## Two registers & two immediates -/

-- djump((reg_B + immed_Y) mod 2^32) on the PRIOR reg_B; reg'_A = immed_X persists.
def execLoadImmJumpInd (d : Isa) (p : Program) (s : State) (a b : Reg) (x target : Val) : Exit × State :=
  djump d p (s.setReg a x) ((s.reg b + target).setWidth 32).toNat

end Pvm.Spec
