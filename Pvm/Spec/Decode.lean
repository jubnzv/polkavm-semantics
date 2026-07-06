/-
Spec model — program decoding, basic blocks, operand decode, decode dispatch.

Transcribed from `graypaper/text/pvm.tex`, App. A:
  §"Instructions, Opcodes and Skip-distance" (eq:skip ~90, eq:instructions ~102),
  §"Basic Blocks and Termination Instructions" (T ~108, ϖ ~136, 𝔏 ~142),
  §"Instruction Tables" per-group operand preambles (~297..642),
  eq:signedextension (~239).

Derived from the GP text alone.
-/
import Pvm.Common.Ast

namespace Pvm.Spec
open Pvm

/-! ## Decode core -/

/-- `ζ_i` (= `c_i`, else 0 past the end). GP eq:instructions (~102): `ζ ≡ c ++ [0,0,…]`. -/
def codeByte (p : Program) (i : Nat) : UInt8 := p.code[i]?.getD 0

/-- GP eq:skip (~90): `skip(i) = min(24, least j : (k ++ [1,1,…])_{i+1+j} = 1)`.
    The bitmask is padded with set bits so the final instruction is well-defined (~97). -/
def skip (p : Program) (i : Nat) : Nat :=
  let kbit := fun (m : Nat) => p.bitmask[m]?.getD true   -- padded tail is all-ones
  ((List.range 25).find? (fun j => kbit (i + 1 + j))).getD 24

/-- The block-termination opcode set `T` (GP ~108..132), as opcode indices.
    Matches `Pvm.Instr.isTerminator`. `unlikely` (2) is NOT a terminator. -/
def opcodeIsTerminator (op : UInt8) : Bool :=
  let n := op.toNat
  n == 0 || n == 1 || n == 40 || n == 50 || n == 180
    || (80 ≤ n && n ≤ 90) || (170 ≤ n && n ≤ 175)

/-- The valid-opcode set `U` (every row of the GP instruction tables). -/
def opcodeIsValid (op : UInt8) : Bool :=
  let n := op.toNat
  n ≤ 2 || n == 10 || n == 20 || (30 ≤ n && n ≤ 33) || n == 40
    || (50 ≤ n && n ≤ 62) || (70 ≤ n && n ≤ 73) || (80 ≤ n && n ≤ 90)
    || (100 ≤ n && n ≤ 110) || (120 ≤ n && n ≤ 161) || (170 ≤ n && n ≤ 175)
    || n == 180 || (190 ≤ n && n ≤ 230)

/-- GP ϖ (~136): `j ∈ ϖ` iff `j` is a valid instruction (`k_j=1 ∧ c_j∈U`) AND
    `j=0` or `j = n+1+skip(n)` for some terminator instruction `n`. -/
def isBlockStart (p : Program) (j : Nat) : Bool :=
  let validJ := (p.bitmask[j]?.getD false) && opcodeIsValid (codeByte p j)
  let afterTerm := j == 0 ||
    (List.range p.code.size).any (fun n =>
      (p.bitmask[n]?.getD false) && opcodeIsTerminator (codeByte p n)
        && (n + 1 + skip p n == j))
  validJ && afterTerm

/-- GP 𝔏 (~142): `𝔏(ı) = max(j ∈ ϖ : j ≤ ı)`. -/
def basicBlockStartNat (p : Program) (i : Nat) : Nat :=
  -- SPEC-AMBIGUITY(pvm.tex eq. ~142): 𝔏 is a max over a possibly-empty set if no block
  -- start ≤ ı exists (malformed program); chose to default to 0.
  ((List.range (i + 1)).reverse.find? (fun j => isBlockStart p j)).getD 0

def basicBlockStart (p : Program) (pc : Addr) : Addr :=
  BitVec.ofNat 32 (basicBlockStartNat p pc.toNat)

/-! ## Operand decode -/

/-- `decode_l` (GP `\decode[l]`): little-endian read of `l` octets of `ζ` starting at `start`. -/
def decodeBytes (p : Program) (start len : Nat) : Nat :=
  (List.range len).foldl (fun acc i => acc + (codeByte p (start + i)).toNat * 256 ^ i) 0

/-- `sext_l` (GP eq:signedextension ~239) on the value of `l` octets: sign-extend the
    `8l`-bit word `raw` to 64 bits. Octet elision: the MSB of the `l`-octet field is the
    sign. `l=0 ⇒ 0`. -/
def sextVal (l raw : Nat) : Val := (BitVec.ofNat (8 * l) raw).signExtend 64

/-- Zero/truncate an `l`-octet little-endian value into a 64-bit register (unsigned reads). -/
def zextVal (raw : Nat) : Val := BitVec.ofNat 64 raw

/-- Resolve a static offset operand `ı + sext_l(decode_l(…))` (GP one-offset preambles). -/
def resolveOffset (i l raw : Nat) : Val := BitVec.ofNat 64 i + sextVal l raw

/-- Register-nibble clamp `min(12, ·)` (GP `r_A = min(12, …)`), as a `Fin 13`. -/
def regOf (n : Nat) : Reg := ⟨min 12 n, by omega⟩

/-- Low nibble `ζ_{ı+1} mod 16`. -/
def loNib (b : UInt8) : Nat := b.toNat % 16
/-- High nibble `⌊ζ_{ı+1} / 16⌋`. -/
def hiNib (b : UInt8) : Nat := b.toNat / 16

/-! ## Decode dispatch -/

/-- GP §"Instruction Tables": read `ζ_ı`, select the operand group by opcode, extract
    operands, build the matching `Instr`. `none` for any opcode not in `U`, or `k_ı≠1`. -/
def decode (p : Program) (pc : Addr) : Option Instr :=
  let i := pc.toNat
  -- v_inst: require k_ı = 1 (and opcode ∈ U, enforced by the match below). GP deblob ~68.
  if !(p.bitmask[i]?.getD false) then none
  else
    let l  := skip p i
    let op := (codeByte p i).toNat
    let b1 := codeByte p (i + 1)
    -- No arguments (0–2)
    if op == 0 then some .trap
    else if op == 1 then some .fallthrough
    else if op == 2 then some .unlikely
    -- One immediate (10): l_X = min(4, ℓ); ν_X = sext_{l_X}(decode_{l_X}(ζ[ı+1..]))
    else if op == 10 then
      let lX := min 4 l
      some (.ecalli (sextVal lX (decodeBytes p (i + 1) lX)))
    -- One register & one extended-width immediate (20): r_A=min(12,ζ_{ı+1} mod16); ν_X=decode_8(ζ[ı+2..])
    else if op == 20 then
      some (.loadImm64 (regOf (loNib b1)) (zextVal (decodeBytes p (i + 2) 8)))
    -- Two immediates (30–33): l_X=min(4,ζ_{ı+1} mod8); l_Y=min(4,max(0,ℓ-l_X-1))
    else if 30 ≤ op && op ≤ 33 then
      let lX := min 4 (b1.toNat % 8)
      let nX := sextVal lX (decodeBytes p (i + 2) lX)
      let lY := min 4 (l - lX - 1)
      let nY := sextVal lY (decodeBytes p (i + 2 + lX) lY)
      match op with
      | 30 => some (.storeImmU8 nX nY)
      | 31 => some (.storeImmU16 nX nY)
      | 32 => some (.storeImmU32 nX nY)
      | _  => some (.storeImmU64 nX nY)
    -- One offset (40): l_X=min(4,ℓ); ν_X = ı + sign_{l_X}(decode_{l_X}(ζ[ı+1..]))
    else if op == 40 then
      let lX := min 4 l
      some (.jump (resolveOffset i lX (decodeBytes p (i + 1) lX)))
    -- One register & one immediate (50–62): r_A=min(12,ζ_{ı+1} mod16); l_X=min(4,max(0,ℓ-1))
    else if 50 ≤ op && op ≤ 62 then
      let a  := regOf (loNib b1)
      let lX := min 4 (l - 1)
      let x  := sextVal lX (decodeBytes p (i + 2) lX)
      match op with
      | 50 => some (.jumpInd a x)
      | 51 => some (.loadImm a x)
      | 52 => some (.loadU8 a x)
      | 53 => some (.loadI8 a x)
      | 54 => some (.loadU16 a x)
      | 55 => some (.loadI16 a x)
      | 56 => some (.loadU32 a x)
      | 57 => some (.loadI32 a x)
      | 58 => some (.loadU64 a x)
      | 59 => some (.storeU8 a x)
      | 60 => some (.storeU16 a x)
      | 61 => some (.storeU32 a x)
      | _  => some (.storeU64 a x)
    -- One register & two immediates (70–73): l_X=min(4,⌊ζ_{ı+1}/16⌋ mod8); l_Y=min(4,max(0,ℓ-l_X-1))
    else if 70 ≤ op && op ≤ 73 then
      let a  := regOf (loNib b1)
      let lX := min 4 (hiNib b1 % 8)
      let nX := sextVal lX (decodeBytes p (i + 2) lX)
      let lY := min 4 (l - lX - 1)
      let nY := sextVal lY (decodeBytes p (i + 2 + lX) lY)
      match op with
      | 70 => some (.storeImmIndU8 a nX nY)
      | 71 => some (.storeImmIndU16 a nX nY)
      | 72 => some (.storeImmIndU32 a nX nY)
      | _  => some (.storeImmIndU64 a nX nY)
    -- One register, one immediate & one offset (80–90): l_X=min(4,⌊ζ_{ı+1}/16⌋ mod8);
    --   ν_X=sext; l_Y=min(4,max(0,ℓ-l_X-1)); ν_Y = ı + sign_{l_Y}(…)
    else if 80 ≤ op && op ≤ 90 then
      let a  := regOf (loNib b1)
      let lX := min 4 (hiNib b1 % 8)
      let nX := sextVal lX (decodeBytes p (i + 2) lX)
      let lY := min 4 (l - lX - 1)
      let tY := resolveOffset i lY (decodeBytes p (i + 2 + lX) lY)
      match op with
      | 80 => some (.loadImmJump a nX tY)
      | 81 => some (.branchEqImm a nX tY)
      | 82 => some (.branchNeImm a nX tY)
      | 83 => some (.branchLtUImm a nX tY)
      | 84 => some (.branchLeUImm a nX tY)
      | 85 => some (.branchGeUImm a nX tY)
      | 86 => some (.branchGtUImm a nX tY)
      | 87 => some (.branchLtSImm a nX tY)
      | 88 => some (.branchLeSImm a nX tY)
      | 89 => some (.branchGeSImm a nX tY)
      | _  => some (.branchGtSImm a nX tY)
    -- Two registers (100–110): r_D=min(12,ζ_{ı+1} mod16); r_A=min(12,⌊ζ_{ı+1}/16⌋)
    else if 100 ≤ op && op ≤ 110 then
      let d := regOf (loNib b1)
      let a := regOf (hiNib b1)
      match op with
      | 100 => some (.moveReg d a)
      | 101 => some (.countSetBits64 d a)
      | 102 => some (.countSetBits32 d a)
      | 103 => some (.leadingZeroBits64 d a)
      | 104 => some (.leadingZeroBits32 d a)
      | 105 => some (.trailingZeroBits64 d a)
      | 106 => some (.trailingZeroBits32 d a)
      | 107 => some (.signExtend8 d a)
      | 108 => some (.signExtend16 d a)
      | 109 => some (.zeroExtend16 d a)
      | _   => some (.reverseBytes d a)
    -- Two registers & one immediate (120–161): r_A=min(12,ζ_{ı+1} mod16); r_B=min(12,⌊ζ_{ı+1}/16⌋);
    --   l_X=min(4,max(0,ℓ-1))
    else if 120 ≤ op && op ≤ 161 then
      let a  := regOf (loNib b1)
      let b  := regOf (hiNib b1)
      let lX := min 4 (l - 1)
      let x  := sextVal lX (decodeBytes p (i + 2) lX)
      match op with
      | 120 => some (.storeIndU8 a b x)
      | 121 => some (.storeIndU16 a b x)
      | 122 => some (.storeIndU32 a b x)
      | 123 => some (.storeIndU64 a b x)
      | 124 => some (.loadIndU8 a b x)
      | 125 => some (.loadIndI8 a b x)
      | 126 => some (.loadIndU16 a b x)
      | 127 => some (.loadIndI16 a b x)
      | 128 => some (.loadIndU32 a b x)
      | 129 => some (.loadIndI32 a b x)
      | 130 => some (.loadIndU64 a b x)
      | 131 => some (.addImm32 a b x)
      | 132 => some (.andImm a b x)
      | 133 => some (.xorImm a b x)
      | 134 => some (.orImm a b x)
      | 135 => some (.mulImm32 a b x)
      | 136 => some (.setLtUImm a b x)
      | 137 => some (.setLtSImm a b x)
      | 138 => some (.shloLImm32 a b x)
      | 139 => some (.shloRImm32 a b x)
      | 140 => some (.sharRImm32 a b x)
      | 141 => some (.negAddImm32 a b x)
      | 142 => some (.setGtUImm a b x)
      | 143 => some (.setGtSImm a b x)
      | 144 => some (.shloLImmAlt32 a b x)
      | 145 => some (.shloRImmAlt32 a b x)
      | 146 => some (.sharRImmAlt32 a b x)
      | 147 => some (.cmovIzImm a b x)
      | 148 => some (.cmovNzImm a b x)
      | 149 => some (.addImm64 a b x)
      | 150 => some (.mulImm64 a b x)
      | 151 => some (.shloLImm64 a b x)
      | 152 => some (.shloRImm64 a b x)
      | 153 => some (.sharRImm64 a b x)
      | 154 => some (.negAddImm64 a b x)
      | 155 => some (.shloLImmAlt64 a b x)
      | 156 => some (.shloRImmAlt64 a b x)
      | 157 => some (.sharRImmAlt64 a b x)
      | 158 => some (.rotR64Imm a b x)
      | 159 => some (.rotR64ImmAlt a b x)
      | 160 => some (.rotR32Imm a b x)
      | _   => some (.rotR32ImmAlt a b x)
    -- Two registers & one offset (170–175): l_X=min(4,max(0,ℓ-1)); ν_X = ı + sign_{l_X}(…)
    else if 170 ≤ op && op ≤ 175 then
      let a  := regOf (loNib b1)
      let b  := regOf (hiNib b1)
      let lX := min 4 (l - 1)
      let t  := resolveOffset i lX (decodeBytes p (i + 2) lX)
      match op with
      | 170 => some (.branchEq a b t)
      | 171 => some (.branchNe a b t)
      | 172 => some (.branchLtU a b t)
      | 173 => some (.branchLtS a b t)
      | 174 => some (.branchGeU a b t)
      | _   => some (.branchGeS a b t)
    -- Two registers & two immediates (180): l_X=min(4,ζ_{ı+2} mod8); ν_X=sext;
    --   l_Y=min(4,max(0,ℓ-l_X-2)); ν_Y=sext
    else if op == 180 then
      let a  := regOf (loNib b1)
      let b  := regOf (hiNib b1)
      let lX := min 4 ((codeByte p (i + 2)).toNat % 8)
      let nX := sextVal lX (decodeBytes p (i + 3) lX)
      let lY := min 4 (l - lX - 2)
      let nY := sextVal lY (decodeBytes p (i + 3 + lX) lY)
      some (.loadImmJumpInd a b nX nY)
    -- Three registers (190–230): r_A=min(12,ζ_{ı+1} mod16); r_B=min(12,⌊ζ_{ı+1}/16⌋); r_D=min(12,ζ_{ı+2})
    else if 190 ≤ op && op ≤ 230 then
      let a := regOf (loNib b1)
      let b := regOf (hiNib b1)
      let d := regOf (codeByte p (i + 2)).toNat
      match op with
      | 190 => some (.add32 a b d)
      | 191 => some (.sub32 a b d)
      | 192 => some (.mul32 a b d)
      | 193 => some (.divU32 a b d)
      | 194 => some (.divS32 a b d)
      | 195 => some (.remU32 a b d)
      | 196 => some (.remS32 a b d)
      | 197 => some (.shloL32 a b d)
      | 198 => some (.shloR32 a b d)
      | 199 => some (.sharR32 a b d)
      | 200 => some (.add64 a b d)
      | 201 => some (.sub64 a b d)
      | 202 => some (.mul64 a b d)
      | 203 => some (.divU64 a b d)
      | 204 => some (.divS64 a b d)
      | 205 => some (.remU64 a b d)
      | 206 => some (.remS64 a b d)
      | 207 => some (.shloL64 a b d)
      | 208 => some (.shloR64 a b d)
      | 209 => some (.sharR64 a b d)
      | 210 => some (.and a b d)
      | 211 => some (.xor a b d)
      | 212 => some (.or a b d)
      | 213 => some (.mulUpperSS a b d)
      | 214 => some (.mulUpperUU a b d)
      | 215 => some (.mulUpperSU a b d)
      | 216 => some (.setLtU a b d)
      | 217 => some (.setLtS a b d)
      | 218 => some (.cmovIz a b d)
      | 219 => some (.cmovNz a b d)
      | 220 => some (.rotL64 a b d)
      | 221 => some (.rotL32 a b d)
      | 222 => some (.rotR64 a b d)
      | 223 => some (.rotR32 a b d)
      | 224 => some (.andInv a b d)
      | 225 => some (.orInv a b d)
      | 226 => some (.xnor a b d)
      | 227 => some (.max a b d)
      | 228 => some (.maxU a b d)
      | 229 => some (.min a b d)
      | _   => some (.minU a b d)
    else none

/-- Posterior pc of the *default* transition `ı' = ı + 1 + skip(ı)` (GP eq. ~201). -/
def nextPc (p : Program) (s : State) : Addr :=
  s.pc + 1 + BitVec.ofNat 32 (skip p s.pc.toNat)

end Pvm.Spec
