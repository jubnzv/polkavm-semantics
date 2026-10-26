/-
Spec model — ALU & bit instruction register mutators: the "Mutations" cells of GP
§"Instruction Tables"; smod (~731), rtz (~742). The Model sets the posterior pc.
GP `mod 2^n` ↔ `setWidth`; `sext_4` ↔ `(·).signExtend 64` on a 32-bit word.
-/
import Pvm.Common.Ast

namespace Pvm.Spec
open Pvm

/-! ## Helpers -/

/-- `signed_4(x mod 2^32)` (GP `\signedn{4}`): signed interpretation of the low 32 bits. -/
@[inline] def s32 (x : Val) : Int := (x.setWidth 32).toInt

/-- Boolean → register (GP comparison results yield `0`/`1`). -/
@[inline] def b2v (c : Bool) : Val := if c then 1 else 0

/-- 64-bit all-ones `= 2^64 - 1` (GP div-by-zero result). -/
@[inline] def ones64 : Val := -1

/-- GP `smod` (~731): `b=0 ⇒ a`; else `sgn(a)·(|a| mod |b|)`. -/
def smodI (a b : Int) : Int :=
  if b == 0 then a else (Int.sign a) * ((a.natAbs % b.natAbs : Nat) : Int)

/-- GP `rtz` (~742): round toward zero ↔ `Int.tdiv`. -/
@[inline] def rtzDiv (a b : Int) : Int := Int.tdiv a b

/-! ## One register & one (extended) immediate -/

-- load_imm_64 — reg'_A = immed_X
def execLoadImm64 (s : State) (a : Reg) (x : Val) : State := s.setReg a x
-- load_imm — reg'_A = immed_X
def execLoadImm (s : State) (a : Reg) (x : Val) : State := s.setReg a x

/-! ## Two registers — dest = r_D, src = r_A -/

-- move_reg — reg'_D = reg_A
def execMoveReg (s : State) (d a : Reg) : State := s.setReg d (s.reg a)

private def popcount (x : Val) (w : Nat) : Nat :=
  (List.range w).foldl (fun acc i => acc + (if x.getLsbD i then 1 else 0)) 0
private def leadingZeros (x : Val) (w : Nat) : Nat :=
  ((List.range w).reverse.takeWhile (fun i => !x.getLsbD i)).length
private def trailingZeros (x : Val) (w : Nat) : Nat :=
  ((List.range w).takeWhile (fun i => !x.getLsbD i)).length

-- count_set_bits_64 — Σ_{i<64} bits_8(reg_A)_i
def execCountSetBits64 (s : State) (d a : Reg) : State :=
  s.setReg d (BitVec.ofNat 64 (popcount (s.reg a) 64))
-- count_set_bits_32 — Σ_{i<32} bits_4(reg_A mod 2^32)_i
def execCountSetBits32 (s : State) (d a : Reg) : State :=
  s.setReg d (BitVec.ofNat 64 (popcount (s.reg a) 32))
-- leading_zero_bits_64 — max n : top n bits (MSB-first) are zero
def execLeadingZeroBits64 (s : State) (d a : Reg) : State :=
  s.setReg d (BitVec.ofNat 64 (leadingZeros (s.reg a) 64))
def execLeadingZeroBits32 (s : State) (d a : Reg) : State :=
  s.setReg d (BitVec.ofNat 64 (leadingZeros (s.reg a) 32))
-- trailing_zero_bits_64 — max n : low n bits are zero
def execTrailingZeroBits64 (s : State) (d a : Reg) : State :=
  s.setReg d (BitVec.ofNat 64 (trailingZeros (s.reg a) 64))
def execTrailingZeroBits32 (s : State) (d a : Reg) : State :=
  s.setReg d (BitVec.ofNat 64 (trailingZeros (s.reg a) 32))
-- sign_extend_8 — unsigned(signed_1(reg_A mod 2^8))
def execSignExtend8 (s : State) (d a : Reg) : State :=
  s.setReg d (((s.reg a).setWidth 8).signExtend 64)
def execSignExtend16 (s : State) (d a : Reg) : State :=
  s.setReg d (((s.reg a).setWidth 16).signExtend 64)
-- zero_extend_16 — reg_A mod 2^16
def execZeroExtend16 (s : State) (d a : Reg) : State :=
  s.setReg d ((s.reg a) &&& 0xFFFF)
-- reverse_bytes — encode_8(reg'_D)_i = encode_8(reg_A)_{7-i}
def execReverseBytes (s : State) (d a : Reg) : State :=
  let x := s.reg a
  s.setReg d ((List.range 8).foldl
    (fun acc i => acc ||| (((x >>> (8 * (7 - i))) &&& 0xFF) <<< (8 * i))) 0)

/-! ## Two registers & one immediate, ALU rows — dest = r_A, src = r_B -/

-- add_imm_32 — reg'_A = sext_4((reg_B + immed_X) mod 2^32)
def execAddImm32 (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a (((s.reg b + x).setWidth 32).signExtend 64)
def execAndImm (s : State) (a b : Reg) (x : Val) : State := s.setReg a (s.reg b &&& x)
def execXorImm (s : State) (a b : Reg) (x : Val) : State := s.setReg a (s.reg b ^^^ x)
def execOrImm (s : State) (a b : Reg) (x : Val) : State := s.setReg a (s.reg b ||| x)
-- mul_imm_32 — sext_4((reg_B · immed_X) mod 2^32)
def execMulImm32 (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a (((s.reg b * x).setWidth 32).signExtend 64)
-- set_lt_u_imm — reg_B < immed_X
def execSetLtUImm (s : State) (a b : Reg) (x : Val) : State := s.setReg a (b2v ((s.reg b).ult x))
-- set_lt_s_imm — signed(reg_B) < signed(immed_X)
def execSetLtSImm (s : State) (a b : Reg) (x : Val) : State := s.setReg a (b2v ((s.reg b).slt x))
-- shlo_l_imm_32 — sext_4((reg_B · 2^(immed_X mod 32)) mod 2^32)
def execShloLImm32 (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a ((((s.reg b) <<< (x.toNat % 32)).setWidth 32).signExtend 64)
-- shlo_r_imm_32 — sext_4(⌊(reg_B mod 2^32) / 2^(immed_X mod 32)⌋)
def execShloRImm32 (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a (((s.reg b).setWidth 32 >>> (x.toNat % 32)).signExtend 64)
-- shar_r_imm_32 — unsigned(⌊signed_4(reg_B mod 2^32) / 2^(immed_X mod 32)⌋)
def execSharRImm32 (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a (((s.reg b).setWidth 32 |>.sshiftRight (x.toNat % 32)).signExtend 64)
-- neg_add_imm_32 — sext_4((immed_X + 2^32 - reg_B) mod 2^32)
def execNegAddImm32 (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a (((x - s.reg b).setWidth 32).signExtend 64)
-- set_gt_u_imm — reg_B > immed_X
def execSetGtUImm (s : State) (a b : Reg) (x : Val) : State := s.setReg a (b2v (x.ult (s.reg b)))
-- set_gt_s_imm — signed(reg_B) > signed(immed_X)
def execSetGtSImm (s : State) (a b : Reg) (x : Val) : State := s.setReg a (b2v (x.slt (s.reg b)))
-- shlo_l_imm_alt_32 — sext_4((immed_X · 2^(reg_B mod 32)) mod 2^32)
def execShloLImmAlt32 (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a (((x <<< ((s.reg b).toNat % 32)).setWidth 32).signExtend 64)
-- shlo_r_imm_alt_32 — sext_4(⌊(immed_X mod 2^32) / 2^(reg_B mod 32)⌋)
def execShloRImmAlt32 (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a ((x.setWidth 32 >>> ((s.reg b).toNat % 32)).signExtend 64)
-- shar_r_imm_alt_32 — unsigned(⌊signed_4(immed_X mod 2^32) / 2^(reg_B mod 32)⌋)
def execSharRImmAlt32 (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a ((x.setWidth 32 |>.sshiftRight ((s.reg b).toNat % 32)).signExtend 64)
-- cmov_iz_imm — immed_X if reg_B=0 else reg_A
def execCmovIzImm (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a (if s.reg b == 0 then x else s.reg a)
-- cmov_nz_imm — immed_X if reg_B≠0 else reg_A
def execCmovNzImm (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a (if s.reg b != 0 then x else s.reg a)
-- add_imm_64 — (reg_B + immed_X) mod 2^64
def execAddImm64 (s : State) (a b : Reg) (x : Val) : State := s.setReg a (s.reg b + x)
-- mul_imm_64 — (reg_B · immed_X) mod 2^64
def execMulImm64 (s : State) (a b : Reg) (x : Val) : State := s.setReg a (s.reg b * x)
-- shlo_l_imm_64 — sext_8((reg_B · 2^(immed_X mod 64)) mod 2^64)  [sext_8 = id]
def execShloLImm64 (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a (s.reg b <<< (x.toNat % 64))
-- shlo_r_imm_64 — sext_8(⌊reg_B / 2^(immed_X mod 64)⌋)
def execShloRImm64 (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a (s.reg b >>> (x.toNat % 64))
-- shar_r_imm_64 — unsigned(⌊signed(reg_B) / 2^(immed_X mod 64)⌋)
def execSharRImm64 (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a ((s.reg b).sshiftRight (x.toNat % 64))
-- neg_add_imm_64 — (immed_X + 2^64 - reg_B) mod 2^64
def execNegAddImm64 (s : State) (a b : Reg) (x : Val) : State := s.setReg a (x - s.reg b)
-- shlo_l_imm_alt_64 — (immed_X · 2^(reg_B mod 64)) mod 2^64
def execShloLImmAlt64 (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a (x <<< ((s.reg b).toNat % 64))
-- shlo_r_imm_alt_64 — ⌊immed_X / 2^(reg_B mod 64)⌋
def execShloRImmAlt64 (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a (x >>> ((s.reg b).toNat % 64))
-- shar_r_imm_alt_64 — unsigned(⌊signed(immed_X) / 2^(reg_B mod 64)⌋)
def execSharRImmAlt64 (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a (x.sshiftRight ((s.reg b).toNat % 64))
-- rot_r_64_imm — bits_8(reg'_A)_i = bits_8(reg_B)_{(i+immed_X) mod 64}
def execRotR64Imm (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a ((s.reg b).rotateRight (x.toNat % 64))
-- rot_r_64_imm_alt — rotate immed_X right by reg_B
def execRotR64ImmAlt (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a (x.rotateRight ((s.reg b).toNat % 64))
-- rot_r_32_imm — sext_4(rotate low-32 of reg_B right by immed_X)
def execRotR32Imm (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a ((((s.reg b).setWidth 32).rotateRight (x.toNat % 32)).signExtend 64)
-- rot_r_32_imm_alt — sext_4(rotate low-32 of immed_X right by reg_B)
def execRotR32ImmAlt (s : State) (a b : Reg) (x : Val) : State :=
  s.setReg a (((x.setWidth 32).rotateRight ((s.reg b).toNat % 32)).signExtend 64)

/-! ## Three registers — dest = r_D, src = r_A, r_B -/

-- add_32 — sext_4((reg_A + reg_B) mod 2^32)
def execAdd32 (s : State) (a b d : Reg) : State :=
  s.setReg d (((s.reg a + s.reg b).setWidth 32).signExtend 64)
-- sub_32 — sext_4((reg_A + 2^32 - (reg_B mod 2^32)) mod 2^32)
def execSub32 (s : State) (a b d : Reg) : State :=
  s.setReg d (((s.reg a - s.reg b).setWidth 32).signExtend 64)
-- mul_32 — sext_4((reg_A · reg_B) mod 2^32)
def execMul32 (s : State) (a b d : Reg) : State :=
  s.setReg d (((s.reg a * s.reg b).setWidth 32).signExtend 64)
-- div_u_32 — 2^64-1 if (reg_B mod 2^32)=0 else sext_4(⌊(reg_A mod 2^32)/(reg_B mod 2^32)⌋)
def execDivU32 (s : State) (a b d : Reg) : State :=
  let bb := (s.reg b).setWidth 32
  s.setReg d (if bb == 0 then ones64 else (((s.reg a).setWidth 32 / bb).signExtend 64))
-- div_s_32 — corners ÷0 ⇒ 2^64-1, MIN/−1 ⇒ unsigned(a); else unsigned(rtz(a÷b))
def execDivS32 (s : State) (a b d : Reg) : State :=
  let av := s32 (s.reg a); let bv := s32 (s.reg b)
  s.setReg d (if bv == 0 then ones64
              else if av == -(2^31) && bv == -1 then unsigned av
              else unsigned (rtzDiv av bv))
-- rem_u_32 — reg_A mod 2^32 if (reg_B mod 2^32)=0 else (reg_A mod 2^32) mod (reg_B mod 2^32)
def execRemU32 (s : State) (a b d : Reg) : State :=
  let aa := (s.reg a).setWidth 32; let bb := (s.reg b).setWidth 32
  s.setReg d (if bb == 0 then aa.signExtend 64 else (aa % bb).signExtend 64)
-- rem_s_32 — 0 if MIN/−1 else unsigned(smod(a,b))
def execRemS32 (s : State) (a b d : Reg) : State :=
  let av := s32 (s.reg a); let bv := s32 (s.reg b)
  s.setReg d (if av == -(2^31) && bv == -1 then 0 else unsigned (smodI av bv))
-- shlo_l_32 — sext_4((reg_A · 2^(reg_B mod 32)) mod 2^32)
def execShloL32 (s : State) (a b d : Reg) : State :=
  s.setReg d (((s.reg a <<< ((s.reg b).toNat % 32)).setWidth 32).signExtend 64)
-- shlo_r_32 — sext_4(⌊(reg_A mod 2^32)/2^(reg_B mod 32)⌋)
def execShloR32 (s : State) (a b d : Reg) : State :=
  s.setReg d (((s.reg a).setWidth 32 >>> ((s.reg b).toNat % 32)).signExtend 64)
-- shar_r_32 — unsigned(⌊signed_4(reg_A mod 2^32)/2^(reg_B mod 32)⌋)
def execSharR32 (s : State) (a b d : Reg) : State :=
  s.setReg d (((s.reg a).setWidth 32 |>.sshiftRight ((s.reg b).toNat % 32)).signExtend 64)
def execAdd64 (s : State) (a b d : Reg) : State := s.setReg d (s.reg a + s.reg b)
def execSub64 (s : State) (a b d : Reg) : State := s.setReg d (s.reg a - s.reg b)
def execMul64 (s : State) (a b d : Reg) : State := s.setReg d (s.reg a * s.reg b)
-- div_u_64 — 2^64-1 if reg_B=0 else ⌊reg_A/reg_B⌋
def execDivU64 (s : State) (a b d : Reg) : State :=
  s.setReg d (if s.reg b == 0 then ones64 else s.reg a / s.reg b)
-- div_s_64 — corners ÷0, MIN/−1; else unsigned(rtz(signed÷signed))
def execDivS64 (s : State) (a b d : Reg) : State :=
  s.setReg d (if s.reg b == 0 then ones64
              else if (s.reg a).toInt == -(2^63) && (s.reg b).toInt == -1 then s.reg a
              else unsigned (rtzDiv (s.reg a).toInt (s.reg b).toInt))
-- rem_u_64 — reg_A if reg_B=0 else reg_A mod reg_B
def execRemU64 (s : State) (a b d : Reg) : State :=
  s.setReg d (if s.reg b == 0 then s.reg a else s.reg a % s.reg b)
-- rem_s_64 — 0 if MIN/−1 else unsigned(smod(signed,signed))
def execRemS64 (s : State) (a b d : Reg) : State :=
  s.setReg d (if (s.reg a).toInt == -(2^63) && (s.reg b).toInt == -1 then 0
              else unsigned (smodI (s.reg a).toInt (s.reg b).toInt))
def execShloL64 (s : State) (a b d : Reg) : State :=
  s.setReg d (s.reg a <<< ((s.reg b).toNat % 64))
def execShloR64 (s : State) (a b d : Reg) : State :=
  s.setReg d (s.reg a >>> ((s.reg b).toNat % 64))
def execSharR64 (s : State) (a b d : Reg) : State :=
  s.setReg d ((s.reg a).sshiftRight ((s.reg b).toNat % 64))
def execAnd (s : State) (a b d : Reg) : State := s.setReg d (s.reg a &&& s.reg b)
def execXor (s : State) (a b d : Reg) : State := s.setReg d (s.reg a ^^^ s.reg b)
def execOr (s : State) (a b d : Reg) : State := s.setReg d (s.reg a ||| s.reg b)
-- mul_upper_s_s — unsigned(⌊(signed·signed)/2^64⌋)
def execMulUpperSS (s : State) (a b d : Reg) : State :=
  s.setReg d (unsigned (Int.fdiv ((s.reg a).toInt * (s.reg b).toInt) (2^64)))
-- mul_upper_u_u — ⌊(reg_A·reg_B)/2^64⌋
def execMulUpperUU (s : State) (a b d : Reg) : State :=
  s.setReg d (BitVec.ofNat 64 ((s.reg a).toNat * (s.reg b).toNat / 2^64))
-- mul_upper_s_u — unsigned(⌊(signed·reg_B)/2^64⌋)
def execMulUpperSU (s : State) (a b d : Reg) : State :=
  s.setReg d (unsigned (Int.fdiv ((s.reg a).toInt * ((s.reg b).toNat : Int)) (2^64)))
def execSetLtU (s : State) (a b d : Reg) : State := s.setReg d (b2v ((s.reg a).ult (s.reg b)))
def execSetLtS (s : State) (a b d : Reg) : State := s.setReg d (b2v ((s.reg a).slt (s.reg b)))
-- cmov_iz — reg_A if reg_B=0 else reg_D
def execCmovIz (s : State) (a b d : Reg) : State :=
  s.setReg d (if s.reg b == 0 then s.reg a else s.reg d)
-- cmov_nz — reg_A if reg_B≠0 else reg_D
def execCmovNz (s : State) (a b d : Reg) : State :=
  s.setReg d (if s.reg b != 0 then s.reg a else s.reg d)
-- rot_l_64 — bits_8(reg'_D)_{(i+reg_B) mod 64} = bits_8(reg_A)_i
def execRotL64 (s : State) (a b d : Reg) : State :=
  s.setReg d ((s.reg a).rotateLeft ((s.reg b).toNat % 64))
-- rot_l_32 — sext_4(rotate low-32 of reg_A left by reg_B)
def execRotL32 (s : State) (a b d : Reg) : State :=
  s.setReg d ((((s.reg a).setWidth 32).rotateLeft ((s.reg b).toNat % 32)).signExtend 64)
def execRotR64 (s : State) (a b d : Reg) : State :=
  s.setReg d ((s.reg a).rotateRight ((s.reg b).toNat % 64))
-- rot_r_32 — sext_4(rotate low-32 of reg_A right by reg_B)
def execRotR32 (s : State) (a b d : Reg) : State :=
  s.setReg d ((((s.reg a).setWidth 32).rotateRight ((s.reg b).toNat % 32)).signExtend 64)
-- and_inv — reg_A ∧ ¬reg_B
def execAndInv (s : State) (a b d : Reg) : State := s.setReg d (s.reg a &&& ~~~(s.reg b))
-- or_inv — reg_A ∨ ¬reg_B
def execOrInv (s : State) (a b d : Reg) : State := s.setReg d (s.reg a ||| ~~~(s.reg b))
-- xnor — ¬(reg_A ⊕ reg_B)
def execXnor (s : State) (a b d : Reg) : State := s.setReg d (~~~(s.reg a ^^^ s.reg b))
-- max — unsigned(max(signed reg_A, signed reg_B))
def execMax (s : State) (a b d : Reg) : State :=
  s.setReg d (if (s.reg a).slt (s.reg b) then s.reg b else s.reg a)
def execMaxU (s : State) (a b d : Reg) : State :=
  s.setReg d (if (s.reg a).ult (s.reg b) then s.reg b else s.reg a)
-- min — unsigned(min(signed reg_A, signed reg_B))
def execMin (s : State) (a b d : Reg) : State :=
  s.setReg d (if (s.reg a).slt (s.reg b) then s.reg a else s.reg b)
def execMinU (s : State) (a b d : Reg) : State :=
  s.setReg d (if (s.reg a).ult (s.reg b) then s.reg a else s.reg b)

end Pvm.Spec
