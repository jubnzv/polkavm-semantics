/-
Spec model — control-flow & trap instructions.
Transcribed from `graypaper/text/pvm.tex`:
  no-arg (0–2), one-imm ecalli (10), one-offset jump (40), one-reg-one-imm jump_ind (50),
  one-reg-one-imm-one-offset (80–90), two-reg-one-offset (170–175), two-reg-two-imm (180);
  sjump (~248), branch (~256), djump (~267).

Each function returns `Exit × State` with the posterior pc already set.
Per Ψ₁ eq. (~184), the regular register posterior (e.g. load_imm_jump's reg'_A) is applied
even when the control verdict is panic/halt; only ε and ı' come from sjump/branch/djump.
-/
import Pvm.Common.Ast
import Pvm.Spec.Decode

namespace Pvm.Spec
open Pvm

/-! ## Control-flow primitives (GP ~248, ~256, ~267) -/

/-- GP `sjump(b)` (~248): target must be a basic-block start, else panic. -/
def sjump (p : Program) (s : State) (b : Nat) : Exit × State :=
  if isBlockStart p b then (.cont, { s with pc := BitVec.ofNat 32 b }) else (.panic, s)

/-- GP `branch(b, C)` (~256): panic unless BOTH the target `b` and the fallthrough `ft`
    are block starts (regardless of whether taken); else go to `b` if `C`, else `ft`. -/
def branch (p : Program) (s : State) (b : Nat) (c : Bool) (ft : Nat) : Exit × State :=
  if !(isBlockStart p b) || !(isBlockStart p ft) then (.panic, s)
  else if c then (.cont, { s with pc := BitVec.ofNat 32 b })
  else (.cont, { s with pc := BitVec.ofNat 32 ft })

/-- GP `djump(a)` (~267): `a = 2^32-2^16 ⇒ halt`; else validity (nonzero, in range, aligned,
    table entry is a block start) then jump to `j_{a/2 - 1}`, else panic. -/
def djump (p : Program) (s : State) (a : Nat) : Exit × State :=
  if a == haltAddr.toNat then (.halt, s)
  else if a == 0 || a > p.jumpTable.size * dynAlign || a % dynAlign != 0 then (.panic, s)
  else
    match p.jumpTable[a / dynAlign - 1]? with
    | some tgt => if isBlockStart p tgt.toNat then (.cont, { s with pc := tgt }) else (.panic, s)
    | none     => (.panic, s)

/-! ## No-argument (0–2) -/

-- GP 0: trap — ε = panic
def execTrap (s : State) : Exit × State := (.panic, s)
-- GP 1: fallthrough — sjump(ı + 1 + skip(ı))
def execFallthrough (p : Program) (s : State) : Exit × State := sjump p s (nextPc p s).toNat
-- GP 2: unlikely — no-op, advance pc
def execUnlikely (p : Program) (s : State) : Exit × State := (.cont, { s with pc := nextPc p s })

/-! ## One immediate (10) -/

-- GP 10: ecalli — ε = host × immed_X; pc left at the ecalli (GP ~77 resume semantics).
-- SPEC-AMBIGUITY(pvm.tex eq. ~311): host id is `host × immed_X` (immed_X a 64-bit value) but
-- Exit.host carries BitVec 32; l_X≤4 so immed_X is a sext'd ≤32-bit value — take its low 32 bits.
def execEcalli (s : State) (x : Val) : Exit × State := (.host (x.setWidth 32), s)

/-! ## One offset (40) -/

-- GP 40: jump — sjump(immed_X)
def execJump (p : Program) (s : State) (target : Val) : Exit × State := sjump p s target.toNat

/-! ## One register & one immediate (50): jump_ind -/

-- GP 50: jump_ind — djump((reg_A + immed_X) mod 2^32)
def execJumpInd (p : Program) (s : State) (a : Reg) (x : Val) : Exit × State :=
  djump p s ((s.reg a + x).setWidth 32).toNat

/-! ## One register, one immediate & one offset (80–90) -/

-- GP 80: load_imm_jump — sjump(immed_Y), reg'_A = immed_X (register update persists on panic)
def execLoadImmJump (p : Program) (s : State) (a : Reg) (x target : Val) : Exit × State :=
  sjump p (s.setReg a x) target.toNat

private def doBranchImm (p : Program) (s : State) (c : Bool) (target : Val) : Exit × State :=
  branch p s target.toNat c (nextPc p s).toNat

-- GP 81–90: immediate branches — branch(immed_Y, reg_A ⋈ immed_X)
def execBranchEqImm  (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranchImm p s (s.reg a == x) t
def execBranchNeImm  (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranchImm p s (s.reg a != x) t
def execBranchLtUImm (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranchImm p s ((s.reg a).ult x) t
def execBranchLeUImm (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranchImm p s ((s.reg a).ule x) t
def execBranchGeUImm (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranchImm p s (x.ule (s.reg a)) t
def execBranchGtUImm (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranchImm p s (x.ult (s.reg a)) t
def execBranchLtSImm (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranchImm p s ((s.reg a).slt x) t
def execBranchLeSImm (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranchImm p s ((s.reg a).sle x) t
def execBranchGeSImm (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranchImm p s (x.sle (s.reg a)) t
def execBranchGtSImm (p : Program) (s : State) (a : Reg) (x t : Val) : Exit × State := doBranchImm p s (x.slt (s.reg a)) t

/-! ## Two registers & one offset (170–175) -/

private def doBranch (p : Program) (s : State) (c : Bool) (target : Val) : Exit × State :=
  branch p s target.toNat c (nextPc p s).toNat

-- GP 170–175: register branches — branch(immed_X, reg_A ⋈ reg_B)
def execBranchEq  (p : Program) (s : State) (a b : Reg) (t : Val) : Exit × State := doBranch p s (s.reg a == s.reg b) t
def execBranchNe  (p : Program) (s : State) (a b : Reg) (t : Val) : Exit × State := doBranch p s (s.reg a != s.reg b) t
def execBranchLtU (p : Program) (s : State) (a b : Reg) (t : Val) : Exit × State := doBranch p s ((s.reg a).ult (s.reg b)) t
def execBranchLtS (p : Program) (s : State) (a b : Reg) (t : Val) : Exit × State := doBranch p s ((s.reg a).slt (s.reg b)) t
def execBranchGeU (p : Program) (s : State) (a b : Reg) (t : Val) : Exit × State := doBranch p s ((s.reg b).ule (s.reg a)) t
def execBranchGeS (p : Program) (s : State) (a b : Reg) (t : Val) : Exit × State := doBranch p s ((s.reg b).sle (s.reg a)) t

/-! ## Two registers & two immediates (180): load_imm_jump_ind -/

-- GP 180: load_imm_jump_ind — djump((reg_B + immed_Y) mod 2^32), reg'_A = immed_X.
-- djump uses PRIOR reg_B; reg'_A update persists.
def execLoadImmJumpInd (p : Program) (s : State) (a b : Reg) (x target : Val) : Exit × State :=
  djump p (s.setReg a x) ((s.reg b + target).setWidth 32).toNat

end Pvm.Spec
