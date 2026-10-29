/-
The codec `E` (GP §"Serialization Codec") and its inverse on the terms program blobs use.
Exactly one value is encoded into any octet sequence (GP ~5): each decoder re-encodes what it read
and rejects octets `E` would not have produced.
-/
import Pvm.Common.Types

namespace Pvm.Spec
open Pvm

/-- `E_l` (GP ~107). -/
def encFixed (l x : Nat) : List UInt8 := (List.range l).map fun t => (x / 256 ^ t % 256).toUInt8

/-- `E` on naturals below 2^64 (GP ~34). -/
def encNat (x : Nat) : List UInt8 :=
  if x = 0 then [0]
  else match (List.range 8).find? fun l => 2 ^ (7 * l) ≤ x && x < 2 ^ (7 * (l + 1)) with
    | some l => (2 ^ 8 - 2 ^ (8 - l) + x / 2 ^ (8 * l)).toUInt8 :: encFixed l (x % 2 ^ (8 * l))
    | none   => 255 :: encFixed 8 x

/-- `E` on bit sequences (GP ~72). -/
def encBits (k : List Bool) : List UInt8 :=
  (List.range ((k.length + 7) / 8)).map fun o =>
    ((List.range 8).foldl (fun a t => a + if k.getD (8 * o + t) false then 2 ^ t else 0) 0).toUInt8

/-- The natural `E_|o|` encodes as `o`. -/
def ofLE (o : Array UInt8) : Nat := o.foldr (fun v a => v.toNat + 256 * a) 0

/-- `n` octets at `i`, and the index past them. -/
def octetsAt (b : Array UInt8) (i n : Nat) : Option (Array UInt8 × Nat) :=
  if i + n ≤ b.size then some (b.extract i (i + n), i + n) else none

/-- `E_l⁻¹` at `i`. -/
def fixedAt (b : Array UInt8) (i l : Nat) : Option (Nat × Nat) := do
  let (o, n) ← octetsAt b i l
  pure (ofLE o, n)

/-- `E⁻¹` on naturals at `i`: the leading ones of the first octet give the length. -/
def natAt (b : Array UInt8) (i : Nat) : Option (Nat × Nat) := do
  let h := (← b[i]?).toNat
  let l := ((List.range 8).takeWhile fun t => h.testBit (7 - t)).length
  let (lo, n) ← fixedAt b (i + 1) l
  let x := h % 2 ^ (7 - l) * 2 ^ (8 * l) + lo
  guard ((b.extract i n).toList == encNat x)
  pure (x, n)

/-- `E⁻¹` on a bit sequence of length `n` at `i`. -/
def bitsAt (b : Array UInt8) (i n : Nat) : Option (Array Bool × Nat) := do
  let (o, m) ← octetsAt b i ((n + 7) / 8)
  let k := (List.range n).map fun t => (o[t / 8]?.getD 0).toNat.testBit (t % 8)
  guard (encBits k == o.toList)
  pure (k.toArray, m)

end Pvm.Spec
