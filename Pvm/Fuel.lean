/-
Ψ on the spec model exits once its fuel exceeds `ξ·(|c| + 2) + |c| + 1`.
-/
import Pvm.Spec.Model
import Pvm.Isa.Revive
import Pvm.Isa.L64

namespace Pvm
open Pvm.Spec

theorem Revive.run_ne_cont {p : Program} {fuel : Nat} {s : State}
    (hc : p.code.size + 25 ≤ 2 ^ 32)
    (hf : s.gas.toNat * (p.code.size + 2) + p.code.size + 1 < fuel) :
    (PvmModel.run (M := model Revive.isa) p fuel s).1 ≠ .cont :=
  PvmModel.run_ne_cont (M := model Revive.isa)
    (progress _ _ _ (fun _ _ => Revive.decode_lt) fun _ _ h => Revive.nextPc_gt h hc) hf

theorem L64.run_ne_cont {p : Program} {fuel : Nat} {s : State} (hc : p.code.size < 2 ^ 32)
    (hf : s.gas.toNat * (p.code.size + 2) + p.code.size + 1 < fuel) :
    (PvmModel.run (M := model L64.isa) p fuel s).1 ≠ .cont :=
  PvmModel.run_ne_cont (M := model L64.isa)
    (progress _ _ _ (fun _ _ => L64.decode_lt) fun _ _ h => L64.nextPc_gt h hc) hf

end Pvm
