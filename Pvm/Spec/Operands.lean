/-
Operand decoding, GP §"Instruction Tables" preambles. GP's `ζ_{ı+1+k}` is `arg p x k` here.
-/
import Pvm.Common.Ast

namespace Pvm.Spec
open Pvm

/-- ζ (GP eq:instructions). -/
def codeByte (p : Program) (i : Nat) : UInt8 := p.code[i]?.getD 0

def decodeBytes (p : Program) (start len : Nat) : Nat :=
  (List.range len).foldl (fun acc i => acc + (codeByte p (start + i)).toNat * 256 ^ i) 0

/-- `sext_l` (GP eq:signedextension). -/
def sextVal (l raw : Nat) : Val := (BitVec.ofNat (8 * l) raw).signExtend 64

def zextVal (raw : Nat) : Val := BitVec.ofNat 64 raw

def regLo (b : UInt8) : Reg := ⟨min 12 (b.toNat % 16), by omega⟩
def regHi (b : UInt8) : Reg := ⟨min 12 (b.toNat / 16), by omega⟩

/-- Opcode at `i` (ı), first argument octet at `a`, `l` argument octets (ℓ). -/
structure Site where
  i : Nat
  a : Nat
  l : Nat

def arg (p : Program) (x : Site) (k : Nat) : UInt8 := codeByte p (x.a + k)

def imm (p : Program) (x : Site) (k l : Nat) : Val := sextVal l (decodeBytes p (x.a + k) l)

def off (p : Program) (x : Site) (k l : Nat) : Val :=
  BitVec.ofNat 64 x.i + sextVal l (decodeBytes p (x.a + k) l)

def oneImm (p : Program) (x : Site) : Val := imm p x 0 (min 4 x.l)

def regExtImm (p : Program) (x : Site) : Reg × Val :=
  (regLo (arg p x 0), zextVal (decodeBytes p (x.a + 1) 8))

def twoImm (p : Program) (x : Site) : Val × Val :=
  let lX := min 4 ((arg p x 0).toNat % 8)
  (imm p x 1 lX, imm p x (1 + lX) (min 4 (x.l - lX - 1)))

def oneOffset (p : Program) (x : Site) : Val := off p x 0 (min 4 x.l)

def regImm (p : Program) (x : Site) : Reg × Val :=
  (regLo (arg p x 0), imm p x 1 (min 4 (x.l - 1)))

def regTwoImm (p : Program) (x : Site) : Reg × Val × Val :=
  let lX := min 4 ((arg p x 0).toNat / 16 % 8)
  (regLo (arg p x 0), imm p x 1 lX, imm p x (1 + lX) (min 4 (x.l - lX - 1)))

def regImmOffset (p : Program) (x : Site) : Reg × Val × Val :=
  let lX := min 4 ((arg p x 0).toNat / 16 % 8)
  (regLo (arg p x 0), imm p x 1 lX, off p x (1 + lX) (min 4 (x.l - lX - 1)))

/-- `(r_D, r_A)`. -/
def twoReg (p : Program) (x : Site) : Reg × Reg := (regLo (arg p x 0), regHi (arg p x 0))

def twoRegImm (p : Program) (x : Site) : Reg × Reg × Val :=
  (regLo (arg p x 0), regHi (arg p x 0), imm p x 1 (min 4 (x.l - 1)))

def twoRegOffset (p : Program) (x : Site) : Reg × Reg × Val :=
  (regLo (arg p x 0), regHi (arg p x 0), off p x 1 (min 4 (x.l - 1)))

def twoRegTwoImm (p : Program) (x : Site) : Reg × Reg × Val × Val :=
  let lX := min 4 ((arg p x 1).toNat % 8)
  (regLo (arg p x 0), regHi (arg p x 0), imm p x 2 lX, imm p x (2 + lX) (min 4 (x.l - lX - 2)))

/-- `(r_A, r_B, r_D)`. -/
def threeReg (p : Program) (x : Site) : Reg × Reg × Reg :=
  (regLo (arg p x 0), regHi (arg p x 0), regLo (arg p x 1))

/-- An operand group bound to the mnemonic it builds. -/
abbrev Op := Option (Program → Site → Instr)
-- GP ~281
def g0 (c : Instr) : Op := some fun _ _ => c
-- GP ~297
def gI (f : Val → Instr) : Op := some fun p x => f (oneImm p x)
-- GP ~315
def gRE (f : Reg → Val → Instr) : Op := some fun p x => let (a, v) := regExtImm p x; f a v
-- GP ~332
def gII (f : Val → Val → Instr) : Op := some fun p x => let (u, v) := twoImm p x; f u v
-- GP ~355
def gO (f : Val → Instr) : Op := some fun p x => f (oneOffset p x)
-- GP ~373
def gRI (f : Reg → Val → Instr) : Op := some fun p x => let (a, v) := regImm p x; f a v
-- GP ~406
def gRII (f : Reg → Val → Val → Instr) : Op :=
  some fun p x => let (a, u, v) := regTwoImm p x; f a u v
-- GP ~432
def gRIO (f : Reg → Val → Val → Instr) : Op :=
  some fun p x => let (a, u, v) := regImmOffset p x; f a u v
-- GP ~465
def gRR (f : Reg → Reg → Instr) : Op := some fun p x => let (d, a) := twoReg p x; f d a
-- GP ~498
def gRRI (f : Reg → Reg → Val → Instr) : Op :=
  some fun p x => let (a, b, v) := twoRegImm p x; f a b v
-- GP ~570
def gRRO (f : Reg → Reg → Val → Instr) : Op :=
  some fun p x => let (a, b, v) := twoRegOffset p x; f a b v
-- GP ~599
def gRRII (f : Reg → Reg → Val → Val → Instr) : Op :=
  some fun p x => let (a, b, u, v) := twoRegTwoImm p x; f a b u v
-- GP ~629
def gRRR (f : Reg → Reg → Reg → Instr) : Op :=
  some fun p x => let (a, b, d) := threeReg p x; f a b d

end Pvm.Spec
