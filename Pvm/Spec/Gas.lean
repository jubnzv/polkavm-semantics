/-
Spec model — gasCost: ϱ^Δ (GP ~998), the 𝔛 simulation (~1010) over the cost tables (~1134).

The GP tests `move_reg` (~1029), T (~1064) and `trap`/`unlikely` (~1178) on raw octets in its own
numbering. These test the decoded instruction; an ı without one counts as `trap`.
-/
import Pvm.Common.Isa

namespace Pvm.Spec
open Pvm

/-- š (GP ~992): the registers read unprimed in the mutation (~274); `ecalli` reads none. -/
def srcRegs : Instr → List Reg
  | .trap | .fallthrough | .unlikely | .ecalli _ | .loadImm64 .. | .jump _ | .loadImm .. => []
  | .storeImmU8 .. | .storeImmU16 .. | .storeImmU32 .. | .storeImmU64 .. => []
  | .loadU8 .. | .loadI8 .. | .loadU16 .. | .loadI16 .. | .loadU32 .. | .loadI32 ..
  | .loadU64 .. | .loadImmJump .. => []
  | .jumpInd a _ | .storeU8 a _ | .storeU16 a _ | .storeU32 a _ | .storeU64 a _ => [a]
  | .storeImmIndU8 a .. | .storeImmIndU16 a .. | .storeImmIndU32 a .. | .storeImmIndU64 a .. => [a]
  | .branchEqImm a .. | .branchNeImm a .. | .branchLtUImm a .. | .branchLeUImm a ..
  | .branchGeUImm a .. | .branchGtUImm a .. | .branchLtSImm a .. | .branchLeSImm a ..
  | .branchGeSImm a .. | .branchGtSImm a .. => [a]
  | .moveReg _ a | .countSetBits64 _ a | .countSetBits32 _ a | .leadingZeroBits64 _ a
  | .leadingZeroBits32 _ a | .trailingZeroBits64 _ a | .trailingZeroBits32 _ a
  | .signExtend8 _ a | .signExtend16 _ a | .zeroExtend16 _ a | .reverseBytes _ a => [a]
  | .storeIndU8 a b _ | .storeIndU16 a b _ | .storeIndU32 a b _ | .storeIndU64 a b _ => [a, b]
  | .loadIndU8 _ b _ | .loadIndI8 _ b _ | .loadIndU16 _ b _ | .loadIndI16 _ b _
  | .loadIndU32 _ b _ | .loadIndI32 _ b _ | .loadIndU64 _ b _ => [b]
  | .addImm32 _ b _ | .andImm _ b _ | .xorImm _ b _ | .orImm _ b _ | .mulImm32 _ b _
  | .setLtUImm _ b _ | .setLtSImm _ b _ | .shloLImm32 _ b _ | .shloRImm32 _ b _
  | .sharRImm32 _ b _ | .negAddImm32 _ b _ | .setGtUImm _ b _ | .setGtSImm _ b _
  | .shloLImmAlt32 _ b _ | .shloRImmAlt32 _ b _ | .sharRImmAlt32 _ b _ | .addImm64 _ b _
  | .mulImm64 _ b _ | .shloLImm64 _ b _ | .shloRImm64 _ b _ | .sharRImm64 _ b _
  | .negAddImm64 _ b _ | .shloLImmAlt64 _ b _ | .shloRImmAlt64 _ b _ | .sharRImmAlt64 _ b _
  | .rotR64Imm _ b _ | .rotR64ImmAlt _ b _ | .rotR32Imm _ b _ | .rotR32ImmAlt _ b _ => [b]
  | .cmovIzImm a b _ | .cmovNzImm a b _ => [a, b]
  | .branchEq a b _ | .branchNe a b _ | .branchLtU a b _ | .branchLtS a b _
  | .branchGeU a b _ | .branchGeS a b _ => [a, b]
  | .loadImmJumpInd _ b .. => [b]
  | .add32 a b _ | .sub32 a b _ | .mul32 a b _ | .divU32 a b _ | .divS32 a b _ | .remU32 a b _
  | .remS32 a b _ | .shloL32 a b _ | .shloR32 a b _ | .sharR32 a b _ | .add64 a b _
  | .sub64 a b _ | .mul64 a b _ | .divU64 a b _ | .divS64 a b _ | .remU64 a b _ | .remS64 a b _
  | .shloL64 a b _ | .shloR64 a b _ | .sharR64 a b _ | .and a b _ | .xor a b _ | .or a b _
  | .mulUpperSS a b _ | .mulUpperUU a b _ | .mulUpperSU a b _ | .setLtU a b _ | .setLtS a b _
  | .rotL64 a b _ | .rotL32 a b _ | .rotR64 a b _ | .rotR32 a b _ | .andInv a b _
  | .orInv a b _ | .xnor a b _ | .max a b _ | .maxU a b _ | .min a b _ | .minU a b _ => [a, b]
  | .cmovIz a b r | .cmovNz a b r => [a, b, r]

/-- ř (GP ~992): the registers primed in the mutation (~274), written or not. -/
def dstRegs : Instr → List Reg
  | .trap | .fallthrough | .unlikely | .ecalli _ | .jump _ | .jumpInd .. => []
  | .storeImmU8 .. | .storeImmU16 .. | .storeImmU32 .. | .storeImmU64 .. => []
  | .storeU8 .. | .storeU16 .. | .storeU32 .. | .storeU64 .. => []
  | .storeImmIndU8 .. | .storeImmIndU16 .. | .storeImmIndU32 .. | .storeImmIndU64 .. => []
  | .storeIndU8 .. | .storeIndU16 .. | .storeIndU32 .. | .storeIndU64 .. => []
  | .branchEqImm .. | .branchNeImm .. | .branchLtUImm .. | .branchLeUImm .. | .branchGeUImm ..
  | .branchGtUImm .. | .branchLtSImm .. | .branchLeSImm .. | .branchGeSImm .. | .branchGtSImm ..
  | .branchEq .. | .branchNe .. | .branchLtU .. | .branchLtS .. | .branchGeU .. | .branchGeS .. => []
  | .loadImm64 a _ | .loadImm a _ | .loadU8 a _ | .loadI8 a _ | .loadU16 a _ | .loadI16 a _
  | .loadU32 a _ | .loadI32 a _ | .loadU64 a _ | .loadImmJump a .. => [a]
  | .moveReg r _ | .countSetBits64 r _ | .countSetBits32 r _ | .leadingZeroBits64 r _
  | .leadingZeroBits32 r _ | .trailingZeroBits64 r _ | .trailingZeroBits32 r _
  | .signExtend8 r _ | .signExtend16 r _ | .zeroExtend16 r _ | .reverseBytes r _ => [r]
  | .loadIndU8 a .. | .loadIndI8 a .. | .loadIndU16 a .. | .loadIndI16 a .. | .loadIndU32 a ..
  | .loadIndI32 a .. | .loadIndU64 a .. => [a]
  | .addImm32 a .. | .andImm a .. | .xorImm a .. | .orImm a .. | .mulImm32 a .. | .setLtUImm a ..
  | .setLtSImm a .. | .shloLImm32 a .. | .shloRImm32 a .. | .sharRImm32 a .. | .negAddImm32 a ..
  | .setGtUImm a .. | .setGtSImm a .. | .shloLImmAlt32 a .. | .shloRImmAlt32 a ..
  | .sharRImmAlt32 a .. | .cmovIzImm a .. | .cmovNzImm a .. | .addImm64 a .. | .mulImm64 a ..
  | .shloLImm64 a .. | .shloRImm64 a .. | .sharRImm64 a .. | .negAddImm64 a ..
  | .shloLImmAlt64 a .. | .shloRImmAlt64 a .. | .sharRImmAlt64 a .. | .rotR64Imm a ..
  | .rotR64ImmAlt a .. | .rotR32Imm a .. | .rotR32ImmAlt a .. | .loadImmJumpInd a .. => [a]
  | .add32 _ _ r | .sub32 _ _ r | .mul32 _ _ r | .divU32 _ _ r | .divS32 _ _ r | .remU32 _ _ r
  | .remS32 _ _ r | .shloL32 _ _ r | .shloR32 _ _ r | .sharR32 _ _ r | .add64 _ _ r
  | .sub64 _ _ r | .mul64 _ _ r | .divU64 _ _ r | .divS64 _ _ r | .remU64 _ _ r | .remS64 _ _ r
  | .shloL64 _ _ r | .shloR64 _ _ r | .sharR64 _ _ r | .and _ _ r | .xor _ _ r | .or _ _ r
  | .mulUpperSS _ _ r | .mulUpperUU _ _ r | .mulUpperSU _ _ r | .setLtU _ _ r | .setLtS _ _ r
  | .cmovIz _ _ r | .cmovNz _ _ r | .rotL64 _ _ r | .rotL32 _ _ r | .rotR64 _ _ r
  | .rotR32 _ _ r | .andInv _ _ r | .orInv _ _ r | .xnor _ _ r | .max _ _ r | .maxU _ _ r
  | .min _ _ r | .minU _ _ r => [r]

/-- 𝔼 (GP ~965): units of kind A, L, S, M, D. -/
structure Units where
  a : Nat
  l : Nat
  s : Nat
  m : Nat
  d : Nat
  deriving DecidableEq, Repr, Inhabited

instance : Add Units := ⟨fun x y => ⟨x.a + y.a, x.l + y.l, x.s + y.s, x.m + y.m, x.d + y.d⟩⟩
instance : Sub Units := ⟨fun x y => ⟨x.a - y.a, x.l - y.l, x.s - y.s, x.m - y.m, x.d - y.d⟩⟩

def Units.le (x y : Units) : Bool := x.a ≤ y.a && x.l ≤ y.l && x.s ≤ y.s && x.m ≤ y.m && x.d ≤ y.d

def uN : Units := ⟨0, 0, 0, 0, 0⟩
def uA : Units := ⟨1, 0, 0, 0, 0⟩
def uL : Units := ⟨1, 1, 0, 0, 0⟩
def uS : Units := ⟨1, 0, 1, 0, 0⟩
def uM : Units := ⟨1, 0, 0, 1, 0⟩
def uD : Units := ⟨1, 0, 0, 0, 1⟩

def trapOrUnlikelyAt (d : Isa) (p : Program) (j : Nat) : Bool :=
  j ≥ 2 ^ 32 ||
    match d.decode p (BitVec.ofNat 32 j) with
    | none | some .trap | some .unlikely => true
    | _ => false

/-- 𝔟 (~1175). -/
def bcost (d : Isa) (p : Program) (pc : Addr) (t : Val) : Nat :=
  if trapOrUnlikelyAt d p (d.nextPc p pc).toNat || trapOrUnlikelyAt d p t.toNat then 1 else 20

/-- A row of the cost table (GP ~1223). -/
structure Row where
  c : Nat
  d : Nat
  x : Units

/-- (č, ď, x̂) (GP ~1223), ď by 𝔓 (~1139) and 𝔓_S (~1151); `𝔪 = 25` (~1169). -/
def row (d : Isa) (p : Program) (pc : Addr) (i : Instr) : Row :=
  let P (a b : Nat) := if (srcRegs i).any (dstRegs i).contains then a else b
  match i with
  | .moveReg .. => ⟨0, 1, uN⟩
  | .and .. | .xor .. | .or .. | .add64 .. | .sub64 .. => ⟨1, P 1 2, uA⟩
  | .add32 .. | .sub32 .. => ⟨2, P 2 3, uA⟩
  | .andImm .. | .xorImm .. | .orImm .. | .addImm64 .. | .shloRImm64 .. | .sharRImm64 ..
  | .shloLImm64 .. | .rotR64Imm .. | .reverseBytes .. => ⟨1, P 1 2, uA⟩
  | .addImm32 .. | .shloRImm32 .. | .sharRImm32 .. | .shloLImm32 .. | .rotR32Imm .. =>
    ⟨2, P 2 3, uA⟩
  | .countSetBits64 .. | .countSetBits32 .. | .leadingZeroBits64 .. | .leadingZeroBits32 ..
  | .signExtend8 .. | .signExtend16 .. | .zeroExtend16 .. => ⟨1, 1, uA⟩
  | .trailingZeroBits64 .. | .trailingZeroBits32 .. => ⟨2, 1, ⟨2, 0, 0, 0, 0⟩⟩
  | .shloL64 a _ r | .shloR64 a _ r | .sharR64 a _ r | .rotL64 a _ r | .rotR64 a _ r =>
    ⟨1, if a = r then 2 else 3, uA⟩
  | .shloL32 a _ r | .shloR32 a _ r | .sharR32 a _ r | .rotL32 a _ r | .rotR32 a _ r =>
    ⟨2, if a = r then 3 else 4, uA⟩
  | .shloLImmAlt64 .. | .shloRImmAlt64 .. | .sharRImmAlt64 .. | .rotR64ImmAlt .. => ⟨1, 3, uA⟩
  | .shloLImmAlt32 .. | .shloRImmAlt32 .. | .sharRImmAlt32 .. | .rotR32ImmAlt .. => ⟨2, 4, uA⟩
  | .setLtU .. | .setLtS .. | .setLtUImm .. | .setLtSImm .. | .setGtUImm .. | .setGtSImm .. =>
    ⟨3, 3, uA⟩
  | .cmovIz .. | .cmovNz .. => ⟨2, 2, uA⟩
  | .cmovIzImm .. | .cmovNzImm .. => ⟨2, 3, uA⟩
  | .max .. | .maxU .. | .min .. | .minU .. => ⟨3, P 2 3, uA⟩
  | .loadIndU8 .. | .loadIndI8 .. | .loadIndU16 .. | .loadIndI16 .. | .loadIndU32 ..
  | .loadIndI32 .. | .loadIndU64 ..
  | .loadU8 .. | .loadI8 .. | .loadU16 .. | .loadI16 .. | .loadU32 .. | .loadI32 .. | .loadU64 .. =>
    ⟨25, 1, uL⟩
  | .storeImmIndU8 .. | .storeImmIndU16 .. | .storeImmIndU32 .. | .storeImmIndU64 ..
  | .storeIndU8 .. | .storeIndU16 .. | .storeIndU32 .. | .storeIndU64 ..
  | .storeImmU8 .. | .storeImmU16 .. | .storeImmU32 .. | .storeImmU64 ..
  | .storeU8 .. | .storeU16 .. | .storeU32 .. | .storeU64 .. => ⟨25, 1, uS⟩
  | .branchEq _ _ t | .branchNe _ _ t | .branchLtU _ _ t | .branchLtS _ _ t
  | .branchGeU _ _ t | .branchGeS _ _ t
  | .branchEqImm _ _ t | .branchNeImm _ _ t | .branchLtUImm _ _ t | .branchLeUImm _ _ t
  | .branchGeUImm _ _ t | .branchGtUImm _ _ t | .branchLtSImm _ _ t | .branchLeSImm _ _ t
  | .branchGeSImm _ _ t | .branchGtSImm _ _ t => ⟨bcost d p pc t, 1, uA⟩
  | .divU32 .. | .divS32 .. | .remU32 .. | .remS32 ..
  | .divU64 .. | .divS64 .. | .remU64 .. | .remS64 .. => ⟨60, 4, uD⟩
  | .andInv .. | .orInv .. | .negAddImm64 .. => ⟨2, 3, uA⟩
  | .xnor .. => ⟨2, P 2 3, uA⟩
  | .negAddImm32 .. => ⟨3, 4, uA⟩
  | .loadImm .. => ⟨1, 1, uN⟩
  | .loadImm64 .. => ⟨1, 2, uN⟩
  | .mul64 .. | .mulImm64 .. => ⟨3, P 1 2, uM⟩
  | .mul32 .. | .mulImm32 .. => ⟨4, P 2 3, uM⟩
  | .mulUpperSS .. | .mulUpperUU .. => ⟨4, 4, uM⟩
  | .mulUpperSU .. => ⟨6, 4, uM⟩
  | .trap | .fallthrough => ⟨2, 1, uN⟩
  | .unlikely => ⟨40, 1, uN⟩
  | .jump .. | .loadImmJump .. => ⟨15, 1, uN⟩
  | .jumpInd .. | .loadImmJumpInd .. => ⟨22, 1, uN⟩
  | .ecalli .. => ⟨100, 4, uA⟩

/-- DEC, WAIT, EXE, FIN (GP ~917); ∅ is `none`. -/
inductive RobState | dec | wait | exe | fin
  deriving DecidableEq, Repr

/-- ℝ (GP ~952). -/
structure Entry where
  s : Option RobState
  c : Nat
  p : List Nat
  r : List Reg
  t : Units
  deriving Repr

/-- 𝕊 (GP ~939). -/
structure Sim where
  i : Option Addr
  c : Nat
  d : Nat
  e : Nat
  t : Units
  r : Array Entry
  deriving Repr

def instrAt (d : Isa) (p : Program) (pc : Addr) : Instr := (d.decode p pc).getD .trap

/-- 𝔛' (GP ~1026): 𝔛^mov (~1038) or 𝔛^dec (~1058). -/
def ingest (d : Isa) (p : Program) (pc : Addr) (x : Sim) : Sim :=
  let i := instrAt d p pc
  let s := srcRegs i
  let r := dstRegs i
  let w := row d p pc i
  match i with
  | .moveReg .. =>
    { x with i := some (d.nextPc p pc), d := x.d - 1,
             r := x.r.map fun e => { e with
               r := if e.r.any s.contains then e.r ++ r.filter (· ∉ e.r) else e.r.filter (· ∉ r) } }
  | _ =>
    let deps := (List.range x.r.size).filter fun j => x.r[j]?.any (·.r.any s.contains)
    { x with i := if i.isTerminator then none else some (d.nextPc p pc), d := x.d - w.d,
             r := (x.r.map fun e => { e with r := e.r.filter (· ∉ r) }).push
               ⟨some .dec, w.c, deps, r, w.x⟩ }

/-- 𝔖 (GP ~1096). -/
def ready (x : Sim) : Option Nat :=
  x.r.findIdx? fun e =>
    e.s == some .wait && e.t.le x.t && e.p.all fun k => x.r[k]?.any (·.c == 0)

/-- 𝔛'' (GP ~1081). -/
def start (x : Sim) (n : Nat) : Sim :=
  { x with e := x.e - 1, t := x.t - (x.r[n]?.map (·.t)).getD uN,
           r := x.r.modify n fun e => { e with s := some .exe } }

/-- 𝔛''' (GP ~1111). `∀ k ≤ j, FIN or ∅` holds exactly below the first entry that is neither. -/
def tick (x : Sim) : Sim :=
  let q := (x.r.findIdx? fun e => !(e.s == some .fin || e.s == none)).getD x.r.size
  { x with d := 4, e := 5, c := x.c + 1,
           t := x.r.foldl (fun t e => if e.s == some .exe && e.c == 1 then t + e.t else t) x.t,
           r := x.r.mapIdx fun j e => { e with
             s := if j < q then none else match e.s with
               | some .dec => some .wait
               | some .exe => if e.c == 0 then some .fin else e.s
               | s => s
             c := if e.s == some .exe && e.c > 0 then e.c - 1 else e.c } }

/-- One case of 𝔛 (GP ~1011); `none` once converged. -/
def simStep (d : Isa) (p : Program) (x : Sim) : Option Sim :=
  let l := x.r.countP (·.s.isSome)
  if let some pc := x.i.filter fun pc => (row d p pc (instrAt d p pc)).d ≤ x.d && l < 32 then
    some (ingest d p pc x)
  else if let some n := (ready x).filter fun _ => x.e > 0 then some (start x n)
  else if x.i.isNone && l == 0 then none
  else some (tick x)

def sim (d : Isa) (p : Program) : Nat → Sim → Sim
  | 0,     x => x
  | f + 1, x =>
    match simStep d p x with
    | some y => sim d p f y
    | none   => x

-- Fuel: ≤ |c| + 1 instructions, each ingested and started once and done ≤ č + 3 ≤ 103 cycles
-- after the previous one.
/-- x^final (GP ~1003). -/
def simFinal (d : Isa) (p : Program) (pc : Addr) : Sim :=
  sim d p (128 * (p.code.size + 2)) ⟨some pc, 0, 4, 5, ⟨4, 4, 4, 1, 1⟩, #[]⟩

/-- ϱ^Δ (GP ~998). -/
def gasCost (d : Isa) (p : Program) (pc : Addr) : Nat := max ((simFinal d p pc).c - 3) 1

theorem gasCost_pos (d : Isa) (p : Program) (pc : Addr) : 1 ≤ gasCost d p pc :=
  Nat.le_max_right _ _

/-- Every entry 𝔛^dec adds counts down to 0, so 𝔛''' (at c = 1) frees its units. -/
theorem row_c_pos (d : Isa) (p : Program) (pc : Addr) (i : Instr) (h : ∀ r a, i ≠ .moveReg r a) :
    0 < (row d p pc i).c := by
  cases i <;> simp [row, bcost] at h ⊢ <;> split <;> omega

end Pvm.Spec
