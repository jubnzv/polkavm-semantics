/-
Latest64: the GP operand groups (~274) on an encoding that GP 0.8.0 does not describe, defined
below. `Program.bitmask` is unused.

c = `Program.code`, n = |c|, ζ = c ⌢ [0, 0, …] (GP ~102), B = 1024, U = the domain of `op`,
T = the opcodes in U whose mnemonic is in GP T (~108).

Opcode: c_ı = 255 ⇒ r(ı) = 255 + ζ_{ı+1}, o(ı) = 2; otherwise r(ı) = c_ı, o(ı) = 1.
Length: L(ı) = o(ı) + A(r(ı)), with A(r) from `op` and 0 for r ∉ U.
Macro block of ı: from b(ı) = ı − (ı mod B) to e(ı) = min(b(ı) + B, n).
Instruction starts S: in every macro block [b, e), s₀ = b and s_{m+1} = s_m + λ(s_m) while
  s_m < e, where λ(s) = min(L(s), e(s) − s).
Valid instructions: V = { s ∈ S : r(s) ∈ U ∧ (s + L(s) < e(s) ∨ (s + L(s) = e(s) ∧ r(s) ∈ T)) }.
Block starts: ϖ = ({ b < n : b ≡ 0 (mod B) } ∪ { s + L(s) : s ∈ V ∧ r(s) ∈ T }) ∩ V.
𝔏(ı) = max(j ∈ ϖ : j ≤ ı) (GP ~142), and 0 when there is no such j.
decode(ı) = none for ı ∉ V; otherwise the mnemonic of r(ı), read with its GP operand group from
  ı + o(ı) with ℓ = A(r(ı)).
nextPc(ı) = ı + λ(ı) for ı ∈ S, and ı + 1 otherwise.
Every program is valid: GP 0.8.0 has no v_blob for this encoding.
-/
import Pvm.Common.Isa
import Pvm.Spec.Operands

namespace Pvm.L64
open Pvm Pvm.Spec

def B : Nat := 1024

/-- (r(ı), o(ı)). -/
def opc (p : Program) (i : Nat) : Nat × Nat :=
  if codeByte p i == 255 then (255 + (codeByte p (i + 1)).toNat, 2) else ((codeByte p i).toNat, 1)

/-- Opcode ↦ A(r), operand group and mnemonic; defined exactly on U. -/
def op : Nat → Nat × Op
  | 0   => (0, g0 .trap)
  | 1   => (0, g0 .fallthrough)
  | 2   => (0, g0 .unlikely)
  | 3   => (1, gRI .jumpInd)
  | 4   => (1, gRI .loadImm)
  | 5   => (2, gRI .loadImm)
  | 6   => (3, gRI .loadImm)
  | 7   => (4, gRI .loadImm)
  | 8   => (5, gRI .loadImm)
  | 9   => (5, gRI .loadU8)
  | 10  => (4, gRI .loadI8)
  | 11  => (5, gRI .loadU16)
  | 12  => (5, gRI .loadI16)
  | 13  => (4, gRI .loadI32)
  | 14  => (5, gRI .loadI32)
  | 15  => (5, gRI .loadU32)
  | 16  => (4, gRI .loadU64)
  | 17  => (5, gRI .loadU64)
  | 18  => (5, gRI .storeU8)
  | 19  => (5, gRI .storeU16)
  | 20  => (5, gRI .storeU32)
  | 21  => (4, gRI .storeU64)
  | 22  => (5, gRI .storeU64)
  | 23  => (4, gRIO .loadImmJump)
  | 24  => (5, gRIO .loadImmJump)
  | 25  => (6, gRIO .loadImmJump)
  | 26  => (7, gRIO .loadImmJump)
  | 27  => (8, gRIO .loadImmJump)
  | 28  => (2, gRIO .branchEqImm)
  | 29  => (3, gRIO .branchEqImm)
  | 30  => (4, gRIO .branchEqImm)
  | 31  => (5, gRIO .branchEqImm)
  | 32  => (6, gRIO .branchEqImm)
  | 33  => (9, gRIO .branchEqImm)
  | 34  => (2, gRIO .branchNeImm)
  | 35  => (3, gRIO .branchNeImm)
  | 36  => (4, gRIO .branchNeImm)
  | 37  => (6, gRIO .branchNeImm)
  | 38  => (3, gRIO .branchLtUImm)
  | 39  => (4, gRIO .branchLtUImm)
  | 40  => (5, gRIO .branchLtUImm)
  | 41  => (9, gRIO .branchLtUImm)
  | 42  => (2, gRIO .branchLtSImm)
  | 43  => (3, gRIO .branchLtSImm)
  | 44  => (4, gRIO .branchLtSImm)
  | 45  => (9, gRIO .branchLtSImm)
  | 46  => (3, gRIO .branchGeUImm)
  | 47  => (4, gRIO .branchGeUImm)
  | 48  => (5, gRIO .branchGeUImm)
  | 49  => (2, gRIO .branchGeSImm)
  | 50  => (3, gRIO .branchGeSImm)
  | 51  => (9, gRIO .branchGeSImm)
  | 52  => (2, gRIO .branchLeSImm)
  | 53  => (3, gRIO .branchLeSImm)
  | 54  => (6, gRIO .branchLeSImm)
  | 55  => (3, gRIO .branchLeUImm)
  | 56  => (4, gRIO .branchLeUImm)
  | 57  => (6, gRIO .branchLeUImm)
  | 58  => (3, gRIO .branchGtSImm)
  | 59  => (4, gRIO .branchGtSImm)
  | 60  => (5, gRIO .branchGtSImm)
  | 61  => (9, gRIO .branchGtSImm)
  | 62  => (3, gRIO .branchGtUImm)
  | 63  => (4, gRIO .branchGtUImm)
  | 64  => (5, gRIO .branchGtUImm)
  | 65  => (9, gRIO .branchGtUImm)
  | 66  => (1, gRII .storeImmIndU8)
  | 67  => (2, gRII .storeImmIndU8)
  | 68  => (3, gRII .storeImmIndU8)
  | 69  => (4, gRII .storeImmIndU8)
  | 70  => (5, gRII .storeImmIndU8)
  | 71  => (2, gRII .storeImmIndU16)
  | 72  => (3, gRII .storeImmIndU16)
  | 73  => (4, gRII .storeImmIndU16)
  | 74  => (5, gRII .storeImmIndU16)
  | 75  => (1, gRII .storeImmIndU32)
  | 76  => (2, gRII .storeImmIndU32)
  | 77  => (3, gRII .storeImmIndU32)
  | 78  => (4, gRII .storeImmIndU32)
  | 79  => (6, gRII .storeImmIndU32)
  | 80  => (9, gRII .storeImmIndU32)
  | 81  => (1, gRII .storeImmIndU64)
  | 82  => (2, gRII .storeImmIndU64)
  | 83  => (3, gRII .storeImmIndU64)
  | 84  => (4, gRII .storeImmIndU64)
  | 85  => (5, gRII .storeImmIndU64)
  | 86  => (6, gRII .storeImmIndU64)
  | 87  => (7, gRII .storeImmIndU64)
  | 88  => (1, gRRI .storeIndU8)
  | 89  => (2, gRRI .storeIndU8)
  | 90  => (3, gRRI .storeIndU8)
  | 91  => (1, gRRI .storeIndU16)
  | 92  => (2, gRRI .storeIndU16)
  | 93  => (3, gRRI .storeIndU16)
  | 94  => (1, gRRI .storeIndU32)
  | 95  => (2, gRRI .storeIndU32)
  | 96  => (3, gRRI .storeIndU32)
  | 97  => (1, gRRI .storeIndU64)
  | 98  => (2, gRRI .storeIndU64)
  | 99  => (3, gRRI .storeIndU64)
  | 100 => (1, gRRI .loadIndU8)
  | 101 => (2, gRRI .loadIndU8)
  | 102 => (3, gRRI .loadIndU8)
  | 103 => (1, gRRI .loadIndI8)
  | 104 => (2, gRRI .loadIndI8)
  | 105 => (3, gRRI .loadIndI8)
  | 106 => (1, gRRI .loadIndU16)
  | 107 => (2, gRRI .loadIndU16)
  | 108 => (3, gRRI .loadIndU16)
  | 109 => (1, gRRI .loadIndI16)
  | 110 => (2, gRRI .loadIndI16)
  | 111 => (3, gRRI .loadIndI16)
  | 112 => (1, gRRI .loadIndI32)
  | 113 => (2, gRRI .loadIndI32)
  | 114 => (3, gRRI .loadIndI32)
  | 115 => (1, gRRI .loadIndU32)
  | 116 => (2, gRRI .loadIndU32)
  | 117 => (3, gRRI .loadIndU32)
  | 118 => (1, gRRI .loadIndU64)
  | 119 => (2, gRRI .loadIndU64)
  | 120 => (3, gRRI .loadIndU64)
  | 121 => (1, gRRI .addImm32)
  | 122 => (2, gRRI .addImm32)
  | 123 => (3, gRRI .addImm32)
  | 124 => (5, gRRI .addImm32)
  | 125 => (2, gRRI .addImm64)
  | 126 => (3, gRRI .addImm64)
  | 127 => (4, gRRI .addImm64)
  | 128 => (5, gRRI .addImm64)
  | 129 => (2, gRRI .andImm)
  | 130 => (3, gRRI .andImm)
  | 131 => (5, gRRI .andImm)
  | 132 => (2, gRRI .xorImm)
  | 133 => (3, gRRI .xorImm)
  | 134 => (5, gRRI .xorImm)
  | 135 => (2, gRRI .orImm)
  | 136 => (3, gRRI .orImm)
  | 137 => (5, gRRI .orImm)
  | 138 => (5, gRRI .mulImm32)
  | 139 => (2, gRRI .mulImm64)
  | 140 => (3, gRRI .mulImm64)
  | 141 => (5, gRRI .mulImm64)
  | 142 => (2, gRRI .setLtUImm)
  | 143 => (3, gRRI .setLtUImm)
  | 144 => (5, gRRI .setLtUImm)
  | 145 => (1, gRRI .setLtSImm)
  | 146 => (2, gRRI .setLtSImm)
  | 147 => (2, gRRI .shloLImm32)
  | 148 => (2, gRRI .shloLImm64)
  | 149 => (2, gRRI .shloRImm32)
  | 150 => (2, gRRI .shloRImm64)
  | 151 => (2, gRRI .sharRImm32)
  | 152 => (2, gRRI .sharRImm64)
  | 153 => (1, gRRI .negAddImm32)
  | 154 => (3, gRRI .negAddImm32)
  | 155 => (1, gRRI .negAddImm64)
  | 156 => (2, gRRI .negAddImm64)
  | 157 => (5, gRRI .negAddImm64)
  | 158 => (1, gRRI .setGtUImm)
  | 159 => (5, gRRI .setGtUImm)
  | 160 => (1, gRRI .setGtSImm)
  | 161 => (2, gRRI .shloRImmAlt64)
  | 162 => (5, gRRI .shloRImmAlt64)
  | 163 => (5, gRRI .shloLImmAlt32)
  | 164 => (2, gRRI .shloLImmAlt64)
  | 165 => (1, gRRI .cmovIzImm)
  | 166 => (2, gRRI .cmovIzImm)
  | 167 => (5, gRRI .cmovIzImm)
  | 168 => (1, gRRI .cmovNzImm)
  | 169 => (2, gRRI .cmovNzImm)
  | 170 => (5, gRRI .cmovNzImm)
  | 171 => (2, gRRI .rotR32Imm)
  | 172 => (2, gRRI .rotR64Imm)
  | 173 => (2, gRRO .branchEq)
  | 174 => (3, gRRO .branchEq)
  | 175 => (5, gRRO .branchEq)
  | 176 => (2, gRRO .branchNe)
  | 177 => (3, gRRO .branchNe)
  | 178 => (5, gRRO .branchNe)
  | 179 => (2, gRRO .branchLtU)
  | 180 => (3, gRRO .branchLtU)
  | 181 => (2, gRRO .branchLtS)
  | 182 => (3, gRRO .branchLtS)
  | 183 => (2, gRRO .branchGeU)
  | 184 => (3, gRRO .branchGeU)
  | 185 => (2, gRRO .branchGeS)
  | 186 => (3, gRRO .branchGeS)
  | 187 => (2, gRRR .add32)
  | 188 => (2, gRRR .add64)
  | 189 => (2, gRRR .sub32)
  | 190 => (2, gRRR .sub64)
  | 191 => (2, gRRR .and)
  | 192 => (2, gRRR .xor)
  | 193 => (2, gRRR .or)
  | 194 => (2, gRRR .mul32)
  | 195 => (2, gRRR .mul64)
  | 196 => (2, gRRR .mulUpperUU)
  | 197 => (2, gRRR .setLtU)
  | 198 => (2, gRRR .setLtS)
  | 199 => (2, gRRR .shloL32)
  | 200 => (2, gRRR .shloL64)
  | 201 => (2, gRRR .shloR32)
  | 202 => (2, gRRR .shloR64)
  | 203 => (2, gRRR .divU32)
  | 204 => (2, gRRR .divU64)
  | 205 => (2, gRRR .divS32)
  | 206 => (2, gRRR .remU32)
  | 207 => (2, gRRR .remU64)
  | 208 => (2, gRRR .remS32)
  | 209 => (2, gRRR .cmovIz)
  | 210 => (2, gRRR .cmovNz)
  | 211 => (2, gRRR .andInv)
  | 212 => (2, gRRR .orInv)
  | 213 => (2, gRRR .xnor)
  | 214 => (2, gRRR .maxU)
  | 215 => (2, gRRR .minU)
  | 216 => (2, gRRR .rotL64)
  | 217 => (1, gO .jump)
  | 218 => (2, gO .jump)
  | 219 => (3, gO .jump)
  | 220 => (4, gO .jump)
  | 221 => (1, gI .ecalli)
  | 222 => (6, gII .storeImmU8)
  | 223 => (5, gII .storeImmU32)
  | 224 => (6, gII .storeImmU32)
  | 225 => (9, gII .storeImmU32)
  | 226 => (5, gII .storeImmU64)
  | 227 => (1, gRR .moveReg)
  | 228 => (1, gRR .leadingZeroBits32)
  | 229 => (1, gRR .leadingZeroBits64)
  | 230 => (1, gRR .trailingZeroBits64)
  | 231 => (1, gRR .countSetBits32)
  | 232 => (1, gRR .countSetBits64)
  | 233 => (1, gRR .signExtend8)
  | 234 => (1, gRR .signExtend16)
  | 235 => (1, gRR .zeroExtend16)
  | 236 => (1, gRR .reverseBytes)
  | 237 => (4, gRRII .loadImmJumpInd)
  | 238 => (5, gRRII .loadImmJumpInd)
  | 239 => (9, gRE .loadImm64)
  | 255 => (5, gRI .jumpInd)
  | 256 => (5, gRI .loadI8)
  | 257 => (9, gRIO .loadImmJump)
  | 258 => (9, gRIO .branchNeImm)
  | 259 => (9, gRIO .branchGeUImm)
  | 260 => (9, gRIO .branchLeSImm)
  | 261 => (9, gRIO .branchLeUImm)
  | 262 => (9, gRII .storeImmIndU8)
  | 263 => (9, gRII .storeImmIndU16)
  | 264 => (9, gRII .storeImmIndU64)
  | 265 => (5, gRRI .storeIndU8)
  | 266 => (5, gRRI .storeIndU16)
  | 267 => (5, gRRI .storeIndU32)
  | 268 => (5, gRRI .storeIndU64)
  | 269 => (5, gRRI .loadIndU8)
  | 270 => (5, gRRI .loadIndI8)
  | 271 => (5, gRRI .loadIndU16)
  | 272 => (5, gRRI .loadIndI16)
  | 273 => (5, gRRI .loadIndI32)
  | 274 => (5, gRRI .loadIndU32)
  | 275 => (5, gRRI .loadIndU64)
  | 276 => (5, gRRI .setLtSImm)
  | 277 => (5, gRRI .shloLImm32)
  | 278 => (5, gRRI .shloLImm64)
  | 279 => (5, gRRI .shloRImm32)
  | 280 => (5, gRRI .shloRImm64)
  | 281 => (5, gRRI .sharRImm32)
  | 282 => (5, gRRI .sharRImm64)
  | 283 => (5, gRRI .negAddImm32)
  | 284 => (5, gRRI .setGtSImm)
  | 285 => (5, gRRI .shloRImmAlt32)
  | 286 => (5, gRRI .sharRImmAlt32)
  | 287 => (5, gRRI .sharRImmAlt64)
  | 288 => (5, gRRI .shloLImmAlt64)
  | 289 => (5, gRRI .rotR32Imm)
  | 290 => (5, gRRI .rotR32ImmAlt)
  | 291 => (5, gRRI .rotR64Imm)
  | 292 => (5, gRRI .rotR64ImmAlt)
  | 293 => (5, gRRO .branchLtU)
  | 294 => (5, gRRO .branchLtS)
  | 295 => (5, gRRO .branchGeU)
  | 296 => (5, gRRO .branchGeS)
  | 297 => (2, gRRR .mulUpperSS)
  | 298 => (2, gRRR .mulUpperSU)
  | 299 => (2, gRRR .sharR32)
  | 300 => (2, gRRR .sharR64)
  | 301 => (2, gRRR .divS64)
  | 302 => (2, gRRR .remS64)
  | 303 => (2, gRRR .max)
  | 304 => (2, gRRR .min)
  | 305 => (2, gRRR .rotL32)
  | 306 => (2, gRRR .rotR32)
  | 307 => (2, gRRR .rotR64)
  | 308 => (4, gI .ecalli)
  | 309 => (9, gII .storeImmU8)
  | 310 => (9, gII .storeImmU16)
  | 311 => (9, gII .storeImmU64)
  | 312 => (1, gRR .trailingZeroBits32)
  | 313 => (10, gRRII .loadImmJumpInd)
  | _   => (0, none)

/-- L(ı). -/
def len (p : Program) (i : Nat) : Nat := let (r, o) := opc p i; o + (op r).1

/-- e(ı). -/
def blockEnd (p : Program) (i : Nat) : Nat := min (i - i % B + B) p.code.size

/-- λ(s). -/
def lam (p : Program) (s : Nat) : Nat := min (len p s) (blockEnd p s - s)

/-- s, s + λ(s), … below e. -/
def walk (p : Program) (e : Nat) : Nat → Nat → List Nat
  | 0,        _ => []
  | fuel + 1, s => if s < e then s :: walk p e fuel (s + lam p s) else []

/-- S ∩ [b, e(b)). -/
def chain (p : Program) (b : Nat) : List Nat := walk p (blockEnd p b) B b

/-- ı ∈ S. -/
def inS (p : Program) (i : Nat) : Bool := (chain p (i - i % B)).contains i

/-- Arguments at ı + o(ı), ℓ = A(r(ı)). -/
def site (p : Program) (i : Nat) : Site :=
  let (r, o) := opc p i; { i := i, a := i + o, l := (op r).1 }

/-- The instruction with opcode r(ı). -/
def ins (p : Program) (i : Nat) : Option Instr := (op (opc p i).1).2.map (· p (site p i))

/-- r(s) ∈ T (GP ~108). -/
def inT (p : Program) (s : Nat) : Bool := (ins p s).any Instr.isTerminator

/-- s ∈ V for s ∈ S. -/
def fits (p : Program) (s : Nat) : Bool :=
  (ins p s).isSome &&
    (s + len p s < blockEnd p s || s + len p s == blockEnd p s && inT p s)

/-- ı ∈ V. -/
def inV (p : Program) (i : Nat) : Bool := inS p i && fits p i

def decode (p : Program) (pc : Addr) : Option Instr :=
  if inV p pc.toNat then ins p pc.toNat else none

/-- ϖ; s ∈ V ends within its macro block. -/
def isBlockStart (p : Program) (j : Nat) : Bool :=
  inV p j && (j % B == 0 || (chain p (j - j % B)).any fun s =>
    fits p s && inT p s && s + len p s == j)

/-- 𝔏 (GP ~142). -/
def basicBlockStart (p : Program) (pc : Addr) : Addr :=
  let i := pc.toNat
  let blocks := (List.range ((min (i + 1) p.code.size + B - 1) / B)).reverse
  BitVec.ofNat 32 ((blocks.findSome? fun k =>
    ((chain p (k * B)).filter (· ≤ i)).reverse.find? (isBlockStart p)).getD 0)

def isa : Isa where
  valid _         := true
  decode          := decode
  nextPc p pc     := pc + BitVec.ofNat 32 (if inS p pc.toNat then lam p pc.toNat else 1)
  isBlockStart    := isBlockStart
  basicBlockStart := basicBlockStart

theorem mem_walk {p : Program} {e : Nat} : ∀ {f s x : Nat}, x ∈ walk p e f s → x < e
  | 0, _, _, h => by simp [walk] at h
  | f + 1, s, x, h => by
    unfold walk at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · assumption
      · exact mem_walk h
    · simp at h

theorem inS_lt {p : Program} {i : Nat} (h : inS p i = true) : i < blockEnd p i := by
  unfold inS chain at h
  have := mem_walk (List.contains_iff_mem.mp h)
  simp only [blockEnd, B] at this ⊢
  omega

theorem decode_lt {p : Program} {pc : Addr} {i : Instr} (h : decode p pc = some i) :
    pc.toNat < p.code.size := by
  unfold decode at h
  split at h
  · rename_i hv
    have := inS_lt (Bool.and_eq_true _ _ ▸ hv).1
    simp only [blockEnd] at this
    omega
  · simp at h

theorem len_pos (p : Program) (i : Nat) : 1 ≤ len p i := by
  have : 1 ≤ (opc p i).2 := by unfold opc; split <;> simp
  show 1 ≤ (opc p i).2 + (op (opc p i).1).1
  omega

theorem nextPc_gt {p : Program} {pc : Addr} {i : Instr} (h : decode p pc = some i)
    (hc : p.code.size < 2 ^ 32) : pc.toNat < (isa.nextPc p pc).toNat := by
  unfold decode at h
  split at h
  · rename_i hv
    have hs := (Bool.and_eq_true _ _ ▸ hv).1
    have h1 := inS_lt hs
    have := len_pos p pc.toNat
    simp only [isa, hs, if_true, BitVec.toNat_add, BitVec.toNat_ofNat, lam]
    simp only [blockEnd] at h1 ⊢
    omega
  · simp at h

end Pvm.L64
