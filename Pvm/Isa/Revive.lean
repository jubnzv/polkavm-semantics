/-
ReviveV1: the GP blob (~49), encoding (~79–142) and operand groups (~274), with its own opcode
numbers.
-/
import Pvm.Common.Isa
import Pvm.Spec.Operands
import Pvm.Spec.Serialization

namespace Pvm.Revive
open Pvm Pvm.Spec

/-- (k ⌢ [1, 1, …])_i (GP ~90). -/
def kPad (p : Program) (i : Nat) : Bool := p.bitmask[i]?.getD true

/-- k_i = 1 (GP ~66). -/
def kSet (p : Program) (i : Nat) : Bool := p.bitmask[i]?.getD false

/-- skip (GP ~90). -/
def skip (p : Program) (i : Nat) : Nat :=
  ((List.range 24).find? fun j => kPad p (i + 1 + j)).getD 24

/-- Arguments at ı + 1, ℓ = skip(ı) (GP ~278). -/
def site (p : Program) (i : Nat) : Site := { i := i, a := i + 1, l := skip p i }

/-- Opcode ↦ operand group and mnemonic; defined exactly on U (GP ~134). -/
def op : Nat → Op
  | 0   => g0 .trap
  | 1   => g0 .fallthrough
  | 10  => gI .ecalli
  | 20  => gRE .loadImm64
  | 30  => gII .storeImmU8
  | 31  => gII .storeImmU16
  | 32  => gII .storeImmU32
  | 33  => gII .storeImmU64
  | 40  => gO .jump
  | 50  => gRI .jumpInd
  | 51  => gRI .loadImm
  | 52  => gRI .loadU8
  | 53  => gRI .loadI8
  | 54  => gRI .loadU16
  | 55  => gRI .loadI16
  | 56  => gRI .loadU32
  | 57  => gRI .loadI32
  | 58  => gRI .loadU64
  | 59  => gRI .storeU8
  | 60  => gRI .storeU16
  | 61  => gRI .storeU32
  | 62  => gRI .storeU64
  | 70  => gRII .storeImmIndU8
  | 71  => gRII .storeImmIndU16
  | 72  => gRII .storeImmIndU32
  | 73  => gRII .storeImmIndU64
  | 80  => gRIO .loadImmJump
  | 81  => gRIO .branchEqImm
  | 82  => gRIO .branchNeImm
  | 83  => gRIO .branchLtUImm
  | 84  => gRIO .branchLeUImm
  | 85  => gRIO .branchGeUImm
  | 86  => gRIO .branchGtUImm
  | 87  => gRIO .branchLtSImm
  | 88  => gRIO .branchLeSImm
  | 89  => gRIO .branchGeSImm
  | 90  => gRIO .branchGtSImm
  | 100 => gRR .moveReg
  | 102 => gRR .countSetBits64
  | 103 => gRR .countSetBits32
  | 104 => gRR .leadingZeroBits64
  | 105 => gRR .leadingZeroBits32
  | 106 => gRR .trailingZeroBits64
  | 107 => gRR .trailingZeroBits32
  | 108 => gRR .signExtend8
  | 109 => gRR .signExtend16
  | 110 => gRR .zeroExtend16
  | 111 => gRR .reverseBytes
  | 120 => gRRI .storeIndU8
  | 121 => gRRI .storeIndU16
  | 122 => gRRI .storeIndU32
  | 123 => gRRI .storeIndU64
  | 124 => gRRI .loadIndU8
  | 125 => gRRI .loadIndI8
  | 126 => gRRI .loadIndU16
  | 127 => gRRI .loadIndI16
  | 128 => gRRI .loadIndU32
  | 129 => gRRI .loadIndI32
  | 130 => gRRI .loadIndU64
  | 131 => gRRI .addImm32
  | 132 => gRRI .andImm
  | 133 => gRRI .xorImm
  | 134 => gRRI .orImm
  | 135 => gRRI .mulImm32
  | 136 => gRRI .setLtUImm
  | 137 => gRRI .setLtSImm
  | 138 => gRRI .shloLImm32
  | 139 => gRRI .shloRImm32
  | 140 => gRRI .sharRImm32
  | 141 => gRRI .negAddImm32
  | 142 => gRRI .setGtUImm
  | 143 => gRRI .setGtSImm
  | 144 => gRRI .shloLImmAlt32
  | 145 => gRRI .shloRImmAlt32
  | 146 => gRRI .sharRImmAlt32
  | 147 => gRRI .cmovIzImm
  | 148 => gRRI .cmovNzImm
  | 149 => gRRI .addImm64
  | 150 => gRRI .mulImm64
  | 151 => gRRI .shloLImm64
  | 152 => gRRI .shloRImm64
  | 153 => gRRI .sharRImm64
  | 154 => gRRI .negAddImm64
  | 155 => gRRI .shloLImmAlt64
  | 156 => gRRI .shloRImmAlt64
  | 157 => gRRI .sharRImmAlt64
  | 158 => gRRI .rotR64Imm
  | 159 => gRRI .rotR64ImmAlt
  | 160 => gRRI .rotR32Imm
  | 161 => gRRI .rotR32ImmAlt
  | 170 => gRRO .branchEq
  | 171 => gRRO .branchNe
  | 172 => gRRO .branchLtU
  | 173 => gRRO .branchLtS
  | 174 => gRRO .branchGeU
  | 175 => gRRO .branchGeS
  | 180 => gRRII .loadImmJumpInd
  | 190 => gRRR .add32
  | 191 => gRRR .sub32
  | 192 => gRRR .mul32
  | 193 => gRRR .divU32
  | 194 => gRRR .divS32
  | 195 => gRRR .remU32
  | 196 => gRRR .remS32
  | 197 => gRRR .shloL32
  | 198 => gRRR .shloR32
  | 199 => gRRR .sharR32
  | 200 => gRRR .add64
  | 201 => gRRR .sub64
  | 202 => gRRR .mul64
  | 203 => gRRR .divU64
  | 204 => gRRR .divS64
  | 205 => gRRR .remU64
  | 206 => gRRR .remS64
  | 207 => gRRR .shloL64
  | 208 => gRRR .shloR64
  | 209 => gRRR .sharR64
  | 210 => gRRR .and
  | 211 => gRRR .xor
  | 212 => gRRR .or
  | 213 => gRRR .mulUpperSS
  | 214 => gRRR .mulUpperUU
  | 215 => gRRR .mulUpperSU
  | 216 => gRRR .setLtU
  | 217 => gRRR .setLtS
  | 218 => gRRR .cmovIz
  | 219 => gRRR .cmovNz
  | 220 => gRRR .rotL64
  | 221 => gRRR .rotL32
  | 222 => gRRR .rotR64
  | 223 => gRRR .rotR32
  | 224 => gRRR .andInv
  | 225 => gRRR .orInv
  | 226 => gRRR .xnor
  | 227 => gRRR .max
  | 228 => gRRR .maxU
  | 229 => gRRR .min
  | 230 => gRRR .minU
  | _   => none

/-- The instruction with opcode c_n (GP ~274). -/
def ins (p : Program) (n : Nat) : Option Instr :=
  p.code[n]? >>= fun c => (op c.toNat).map (· p (site p n))

/-- c_n ∈ T (GP ~108). -/
def isT (p : Program) (n : Nat) : Bool := (ins p n).any Instr.isTerminator

/-- k_n = 1 ∧ c_n ∈ U (GP ~136). -/
def inU (p : Program) (n : Nat) : Bool := kSet p n && (ins p n).isSome

/-- k_n = 1 ∧ c_n ∈ T (GP ~136). -/
def inT (p : Program) (n : Nat) : Bool := kSet p n && isT p n

/-- v_inst (GP ~66). -/
def vInst (p : Program) (i : Nat) : Bool := p.bitmask.size == p.code.size && inU p i

def decode (p : Program) (pc : Addr) : Option Instr :=
  if vInst p pc.toNat then ins p pc.toNat else none

/-- v_blob (GP ~57); ı grows and stays ≤ |k|, so |k| + 1 steps decide it. -/
def vBlob (p : Program) : Nat → Nat → Bool
  | 0,        _ => false
  | fuel + 1, i =>
    let n := i + 1 + skip p i
    if i > 0 && i == p.bitmask.size then true
    else if n == p.bitmask.size && !isT p i then false
    else vInst p i && vBlob p fuel n

/-- ϖ (GP ~136); skip ≤ 24 puts n in [j - 25, j). -/
def isBlockStart (p : Program) (j : Nat) : Bool :=
  inU p j && (j == 0 || (List.range (min j 25)).any fun d =>
    let n := j - 1 - d
    inT p n && n + 1 + skip p n == j)

/-- 𝔏 (GP ~142); `max ∅` ↦ 0, unreachable under v_blob (GP ~57). -/
def basicBlockStart (p : Program) (pc : Addr) : Addr :=
  BitVec.ofNat 32
    (((List.range (min (pc.toNat + 1) p.code.size)).reverse.find? (isBlockStart p)).getD 0)

/-- deblob's `(c, k, j)` (GP ~52): the blob is exactly
    `E(|j|) ⌢ E₁(z) ⌢ E(|c|) ⌢ E_z(j) ⌢ E(c) ⌢ E(k)`, each `j_i` a `pvmreg`. `E(k)` leaves
    `|k|` open up to padding; v_inst's `|k| = |c|` settles it. v_blob is `isa.valid`, v_inst at
    ı `isa.decode`. -/
def deblob (b : Array UInt8) : Option Program := do
  let (nj, i) ← natAt b 0
  let (z, i) ← fixedAt b i 1
  let (nc, i) ← natAt b i
  let (o, i) ← octetsAt b i (nj * z)
  let js := (List.range (if z = 0 then 0 else nj)).map fun e =>
    ofLE (o.extract (e * z) (e * z + z))
  guard (js.all (· < 2 ^ 64))
  let (c, i) ← octetsAt b i nc
  let (k, i) ← bitsAt b i nc
  guard (i == b.size)
  pure { code := c, bitmask := k,
         jumpTable := { len := nj, entries := (js.map (BitVec.ofNat 64)).toArray } }

def isa : Isa where
  valid p         := vBlob p (p.bitmask.size + 1) 0
  decode          := decode
  -- GP ~201
  nextPc p pc     := pc + 1 + BitVec.ofNat 32 (skip p pc.toNat)
  isBlockStart    := isBlockStart
  basicBlockStart := basicBlockStart

end Pvm.Revive
