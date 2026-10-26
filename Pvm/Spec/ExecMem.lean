/-
Spec model — loads/stores and ε^μ (~171–180), with the `< 2^16 ⇒ panic` rule (~168).
On fault/panic the PRIOR state is returned. On `cont` the Model advances the pc.
-/
import Pvm.Common.Ast
import Pvm.Spec.Operands

namespace Pvm.Spec
open Pvm

/-! ## ε^μ — memory-access exception (GP ~168, ~171–180) -/

-- GP access per page is W, R or ∅: readable(μ) = {R, W}, writable(μ) = {W} (overview.tex ~178).
def isReadable : Access → Bool | .r => true | .w => true | .inaccessible => false
def isWritable : Access → Bool | .w => true | _ => false

-- GP ~168 (and the TODO #446 atop pvm.tex): an index below 2^16 is ALWAYS inaccessible,
-- regardless of the page tag, so it lands in 𝐱 and, being lowest, forces a panic.
-- GP ~178: μ is CYCLIC (μ^↺), so the constituent indices 𝐫/𝐰 are RAW (unwrapped) naturals
-- {A, A+1, …} (A+i may reach 2^32). Accessibility is looked up at the cyclic address (x mod 2^32),
-- but the index kept in 𝐱 is the RAW x — `min(𝐱)` is over raw indices, reduced mod 2^32 only at the
-- panic/fault test (GP eq. ~175–178).
def addrBadRead (m : Mem) (x : Nat) : Bool :=
  x % 2 ^ 32 < zoneSize || !(isReadable (m.accessAt (BitVec.ofNat 32 x)))
def addrBadWrite (m : Mem) (x : Nat) : Bool :=
  x % 2 ^ 32 < zoneSize || !(isWritable (m.accessAt (BitVec.ofNat 32 x)))

/-- GP ε^μ (~171–180). `reads`/`writes` are the RAW constituent byte indices (GP 𝐫/𝐰; cyclic μ, so
    an index may be ≥ 2^32). The lowest bad index decides panic-vs-fault, reduced mod 2^32 only at
    the test — NOT per byte. `.cont` ⇒ access permitted; otherwise the panic/fault to surface. -/
def emu (m : Mem) (reads writes : List Nat) : Exit :=
  let bad := (reads.filter (addrBadRead m)) ++ (writes.filter (addrBadWrite m))
  match bad with
  | []      => .cont
  | x0 :: _ =>
    let mn := (bad.foldl (fun acc x => min acc x) x0) % 2 ^ 32
    if mn < zoneSize then .panic
    else .fault (BitVec.ofNat 32 (pageSize * (mn / pageSize)))

/-! ## Little-endian byte access (GP `decode`/`encode`; multi-byte straddles wrap mod 2^32) -/

def readBytesLE (m : Mem) (addr : Addr) (n : Nat) : Nat :=
  (List.range n).foldl
    (fun acc i => acc + (m.readByte (addr + BitVec.ofNat 32 i)).toNat * 256 ^ i) 0

def writeBytesLE (m : Mem) (addr : Addr) (n : Nat) (v : Nat) : Mem :=
  (List.range n).foldl
    (fun mm i => mm.writeByte (addr + BitVec.ofNat 32 i) (UInt8.ofNat ((v >>> (8 * i)) % 256))) m

/-- RAW constituent byte indices of an `n`-byte access at `addr` (GP 𝐫/𝐰; cyclic μ ⇒ a forward
    access keeps raw `addr.toNat + i`, which may reach 2^32 and is reduced mod 2^32 only at use). -/
def accessAddrs (addr : Addr) (n : Nat) : List Nat :=
  (List.range n).map (fun i => addr.toNat + i)

/-! ## Generic load / store (apply ε^μ before any mutation) -/

/-- Load `n` little-endian bytes into `a`; `signed ⇒ sext_n`, else zero-extend. -/
def doLoad (s : State) (a : Reg) (addr : Addr) (n : Nat) (signed : Bool) : Exit × State :=
  match emu s.mem (accessAddrs addr n) [] with
  | .cont =>
    let raw := readBytesLE s.mem addr n
    (.cont, s.setReg a (if signed then sextVal n raw else zextVal raw))
  | e => (e, s)

/-- Store the low `n` little-endian bytes of `v` at `addr`. -/
def doStore (s : State) (addr : Addr) (n : Nat) (v : Nat) : Exit × State :=
  match emu s.mem [] (accessAddrs addr n) with
  | .cont => (.cont, { s with mem := writeBytesLE s.mem addr n v })
  | e => (e, s)

/-! ## Two immediates — stores: addr = ν_X, value = ν_Y -/

def execStoreImmU8  (s : State) (addr val : Val) : Exit × State := doStore s (addr.setWidth 32) 1 val.toNat
def execStoreImmU16 (s : State) (addr val : Val) : Exit × State := doStore s (addr.setWidth 32) 2 val.toNat
def execStoreImmU32 (s : State) (addr val : Val) : Exit × State := doStore s (addr.setWidth 32) 4 val.toNat
def execStoreImmU64 (s : State) (addr val : Val) : Exit × State := doStore s (addr.setWidth 32) 8 val.toNat

/-! ## One register & one immediate — loads/stores: addr = immed_X -/

def execLoadU8  (s : State) (a : Reg) (x : Val) : Exit × State := doLoad s a (x.setWidth 32) 1 false
def execLoadI8  (s : State) (a : Reg) (x : Val) : Exit × State := doLoad s a (x.setWidth 32) 1 true
def execLoadU16 (s : State) (a : Reg) (x : Val) : Exit × State := doLoad s a (x.setWidth 32) 2 false
def execLoadI16 (s : State) (a : Reg) (x : Val) : Exit × State := doLoad s a (x.setWidth 32) 2 true
def execLoadU32 (s : State) (a : Reg) (x : Val) : Exit × State := doLoad s a (x.setWidth 32) 4 false
def execLoadI32 (s : State) (a : Reg) (x : Val) : Exit × State := doLoad s a (x.setWidth 32) 4 true
def execLoadU64 (s : State) (a : Reg) (x : Val) : Exit × State := doLoad s a (x.setWidth 32) 8 false
def execStoreU8  (s : State) (a : Reg) (x : Val) : Exit × State := doStore s (x.setWidth 32) 1 (s.reg a).toNat
def execStoreU16 (s : State) (a : Reg) (x : Val) : Exit × State := doStore s (x.setWidth 32) 2 (s.reg a).toNat
def execStoreU32 (s : State) (a : Reg) (x : Val) : Exit × State := doStore s (x.setWidth 32) 4 (s.reg a).toNat
def execStoreU64 (s : State) (a : Reg) (x : Val) : Exit × State := doStore s (x.setWidth 32) 8 (s.reg a).toNat

/-! ## One register & two immediates — stores: addr = reg_A + ν_X, value = ν_Y -/

def execStoreImmIndU8  (s : State) (a : Reg) (x val : Val) : Exit × State :=
  doStore s ((s.reg a + x).setWidth 32) 1 val.toNat
def execStoreImmIndU16 (s : State) (a : Reg) (x val : Val) : Exit × State :=
  doStore s ((s.reg a + x).setWidth 32) 2 val.toNat
def execStoreImmIndU32 (s : State) (a : Reg) (x val : Val) : Exit × State :=
  doStore s ((s.reg a + x).setWidth 32) 4 val.toNat
def execStoreImmIndU64 (s : State) (a : Reg) (x val : Val) : Exit × State :=
  doStore s ((s.reg a + x).setWidth 32) 8 val.toNat

/-! ## Two registers & one immediate — loads/stores: addr = reg_B + ν_X -/

-- stores: value source = reg_A
def execStoreIndU8  (s : State) (a b : Reg) (x : Val) : Exit × State :=
  doStore s ((s.reg b + x).setWidth 32) 1 (s.reg a).toNat
def execStoreIndU16 (s : State) (a b : Reg) (x : Val) : Exit × State :=
  doStore s ((s.reg b + x).setWidth 32) 2 (s.reg a).toNat
def execStoreIndU32 (s : State) (a b : Reg) (x : Val) : Exit × State :=
  doStore s ((s.reg b + x).setWidth 32) 4 (s.reg a).toNat
def execStoreIndU64 (s : State) (a b : Reg) (x : Val) : Exit × State :=
  doStore s ((s.reg b + x).setWidth 32) 8 (s.reg a).toNat
-- loads: dest = reg_A. Signed forms are unsigned(signed_n(decode_n)) = sext_n.
def execLoadIndU8  (s : State) (a b : Reg) (x : Val) : Exit × State :=
  doLoad s a ((s.reg b + x).setWidth 32) 1 false
def execLoadIndI8  (s : State) (a b : Reg) (x : Val) : Exit × State :=
  doLoad s a ((s.reg b + x).setWidth 32) 1 true
def execLoadIndU16 (s : State) (a b : Reg) (x : Val) : Exit × State :=
  doLoad s a ((s.reg b + x).setWidth 32) 2 false
def execLoadIndI16 (s : State) (a b : Reg) (x : Val) : Exit × State :=
  doLoad s a ((s.reg b + x).setWidth 32) 2 true
def execLoadIndU32 (s : State) (a b : Reg) (x : Val) : Exit × State :=
  doLoad s a ((s.reg b + x).setWidth 32) 4 false
def execLoadIndI32 (s : State) (a b : Reg) (x : Val) : Exit × State :=
  doLoad s a ((s.reg b + x).setWidth 32) 4 true
def execLoadIndU64 (s : State) (a b : Reg) (x : Val) : Exit × State :=
  doLoad s a ((s.reg b + x).setWidth 32) 8 false

end Pvm.Spec
