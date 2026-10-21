/-
Bit-width helpers.
Graypaper App. A: sign/unsigned conversions and sign extension (eqs. for `𝒵`, `sext`).
-/
namespace Pvm

/-- A 64-bit register value (GP `pvmreg`). -/
abbrev Val  := BitVec 64
/-- A 32-bit address / instruction counter (the PVM address space is `mod 2^32`). -/
abbrev Addr := BitVec 32

/-- Sign-extend a `w`-bit word to a 64-bit register value (GP `sext`). -/
@[inline] def sext {w : Nat} (x : BitVec w) : Val := x.signExtend 64

/-- Zero-extend / truncate a `w`-bit word to a 64-bit register value. -/
@[inline] def zext {w : Nat} (x : BitVec w) : Val := x.setWidth 64

/-- Signed (two's-complement) interpretation of a register (GP `𝒵`), in `[-2^63, 2^63)`. -/
@[inline] def signed (x : Val) : Int := x.toInt

/-- Unsigned re-encoding of an `Int` into a 64-bit register (GP `𝒵⁻¹`). -/
@[inline] def unsigned (a : Int) : Val := BitVec.ofInt 64 a

end Pvm
