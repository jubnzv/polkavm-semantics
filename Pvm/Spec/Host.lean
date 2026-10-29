/-
Spec model — host functions (GP `pvm_invocations.tex`, "Host Functions").
-/
import Pvm.Common.Interface
import Pvm.Spec.Init
import Pvm.Spec.Model

namespace Pvm.Spec
open Pvm

/-- The host-call gas rule (GP ~284): short of `cost`, `oog` takes all the gas and changes
    nothing else. -/
def charge {X : Type} (cost : Nat) (g : Int) (r : Reg → Val) (m : Mem) (x : X)
    (body : HostExit × (Reg → Val) × Mem × X) : HostExit × Int × (Reg → Val) × Mem × X :=
  if g < cost then (.oog, max (g - cost) 0, r, m, x)
  else let (e, r', m', x') := body; (e, g - cost, r', m', x')

/-- `Ω_Gemini`, `grow_heap` = 1 (GP ~324): the rw region spans pages `a..b`, writable up to `h`;
    `ω₇` asks for `a..ω₇` and gets back the new `h`. Only `o` and `s` of the JAM blob are read. -/
def growHeap {X : Type} (sec : Sections) (g : Int) (r : Reg → Val) (m : Mem) (x : X) :
    HostExit × Int × (Reg → Val) × Mem × X :=
  let a := rwBase sec / pageSize
  let b := (addrSpace - 3 * zoneSize - inputSize - zoneRound sec.stack) / pageSize
  let c := ((List.range' a (b - a)).filter fun q => m.access (BitVec.ofNat 32 q) == .w).length
  let h := a + c
  let w := (r 7).toNat
  let n := if w ≤ h || w > b then h else w
  charge (275 + (n - h) * 121) g r m x
    (.cont, (fun i => if i = 7 then BitVec.ofNat 64 n else r i),
      { m with access := fun q => if a ≤ q.toNat ∧ q.toNat < n then .w else m.access q }, x)

theorem charge_gas {X : Type} {cost : Nat} {g : Int} {r : Reg → Val} {m : Mem} {x : X}
    {body : HostExit × (Reg → Val) × Mem × X} (h0 : 0 ≤ g) :
    0 ≤ (charge cost g r m x body).2.1 ∧ (charge cost g r m x body).2.1 ≤ g := by
  unfold charge
  split <;> simp only <;> omega

theorem growHeap_gas {X : Type} (sec : Sections) (g : Int) (r : Reg → Val) (m : Mem) (x : X)
    (h0 : 0 ≤ g) : 0 ≤ (growHeap sec g r m x).2.1 ∧ (growHeap sec g r m x).2.1 ≤ g :=
  charge_gas h0

/-- `runArgs_gas` for the spec model (GP ~881). -/
theorem runArgs_gas {X : Type} (d : Isa) {deblob : Array UInt8 → Option Program}
    {b args : Array UInt8} {pc : Addr} {gas : Nat} {f : HostFn X} {x x' : X} {fuel calls : Nat}
    {u : Int} {o : Output}
    (hf : ∀ h g r m x, 0 ≤ g → 0 ≤ (f h g r m x).2.1 ∧ (f h g r m x).2.1 ≤ g)
    (h : PvmModel.runArgs (M := model d) deblob Y b pc gas args f x fuel calls = some (u, o, x')) :
    0 ≤ u ∧ u ≤ gas :=
  PvmModel.runArgs_gas (M := model d) (fun p i s => exec_gas d p i s) hf h

end Pvm.Spec
