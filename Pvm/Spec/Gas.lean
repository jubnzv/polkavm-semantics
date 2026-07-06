/-
Spec model — gasCost.
Transcribed from `graypaper/text/pvm.tex` §"Gas Cost Tables" (~1134), the `cost_cycles`
column only, plus the memory cost `𝔪 = 25` (~1169) and branch cost `𝔟` (~1174).

This is a naive cycle-sum, NOT the full 𝔛 gas model (GP §"Gas Cost Model", ~883): the full
model additionally runs an out-of-order pipeline simulation and applies `max(cycles - 3, 1)`
(GP eq:gascostforblock ~998) — NONE of that is done here.
-/
import Pvm.Spec.Decode

namespace Pvm.Spec
open Pvm

/-- Resolved target index of a branch (GP `ı_target`), for the `𝔟` cost. -/
def branchTargetIdx : Instr → Option Nat
  | .branchEqImm _ _ t  | .branchNeImm _ _ t
  | .branchLtUImm _ _ t | .branchLeUImm _ _ t | .branchGeUImm _ _ t | .branchGtUImm _ _ t
  | .branchLtSImm _ _ t | .branchLeSImm _ _ t | .branchGeSImm _ _ t | .branchGtSImm _ _ t
  | .branchEq _ _ t  | .branchNe _ _ t
  | .branchLtU _ _ t | .branchLtS _ _ t | .branchGeU _ _ t | .branchGeS _ _ t => some t.toNat
  | _ => none

/-- GP `𝔟` (~1174): cost 1 if the fallthrough or the branch target opcode byte is
    `unlikely` (2) or `trap` (0); else 20. -/
def bcost (p : Program) (i : Nat) : Nat :=
  let ft := i + 1 + skip p i
  let tgt := match decode p (BitVec.ofNat 32 i) with
             | some instr => (branchTargetIdx instr).getD ft
             | none => ft
  let isUT := fun (j : Nat) => let z := (codeByte p j).toNat; z == 0 || z == 2
  if isUT ft || isUT tgt then 1 else 20

/-- GP `cost_cycles` (~1225): cycles for the instruction whose opcode byte is at `i`. -/
def costCycles (p : Program) (i : Nat) : Nat :=
  let op := (codeByte p i).toNat
  if op == 100 then 0                                                  -- move_reg
  else if op == 2 then 40                                              -- unlikely
  else if op == 10 then 100                                            -- ecalli
  else if op == 50 || op == 180 then 22                               -- jump_ind, load_imm_jump_ind
  else if op == 40 || op == 80 then 15                                -- jump, load_imm_jump
  else if op == 0 || op == 1 then 2                                   -- trap, fallthrough
  else if (81 ≤ op && op ≤ 90) || (170 ≤ op && op ≤ 175) then bcost p i  -- branches: 𝔟
  -- memory: 𝔪 = 25 (loads/stores)
  else if (30 ≤ op && op ≤ 33) || (52 ≤ op && op ≤ 62)
       || (70 ≤ op && op ≤ 73) || (120 ≤ op && op ≤ 130) then 25
  -- div/rem
  else if (193 ≤ op && op ≤ 196) || (203 ≤ op && op ≤ 206) then 60
  -- multiplies
  else if op == 215 then 6                                            -- mul_upper_s_u
  else if op == 192 || op == 135 || op == 213 || op == 214 then 4     -- mul_32, mul_imm_32, mul_upper_u/s
  else if op == 202 || op == 150 then 3                               -- mul_64, mul_imm_64
  -- comparisons-to-register
  else if op == 216 || op == 217 || (136 ≤ op && op ≤ 137) || (142 ≤ op && op ≤ 143) then 3
  else if (227 ≤ op && op ≤ 230) then 3                               -- max/min
  else if (218 ≤ op && op ≤ 219) || (147 ≤ op && op ≤ 148) then 2     -- cmov / cmov_imm
  else if op == 224 || op == 225 || op == 226 || op == 154 then 2     -- and_inv, or_inv, xnor, neg_add_imm_64
  else if op == 141 then 3                                            -- neg_add_imm_32
  else if op == 51 || op == 20 then 1                                 -- load_imm, load_imm_64
  -- 32-bit two-cycle ALU / shift-rotate
  else if op == 190 || op == 191 then 2                              -- add_32, sub_32
  else if op == 131 || op == 139 || op == 140 || op == 138 || op == 160 then 2  -- *_imm_32
  else if op == 105 || op == 106 then 2                              -- trailing_zero_bits_*
  else if (197 ≤ op && op ≤ 199) || op == 221 || op == 223 then 2    -- shlo/shar/rot _32
  else if (144 ≤ op && op ≤ 146) || op == 161 then 2                 -- *_imm_alt_32
  -- one-cycle ALU / shift-rotate / bit ops (everything else valid)
  else if op == 200 || op == 201 || op == 210 || op == 211 || op == 212 then 1  -- add/sub/and/xor/or _64
  else 1

/-- Sum `cost_cycles` over the instructions of the block starting at `i`, walking via
    `skip` until (and including) a terminator. Fuel-bounded for totality. -/
def blockCost (p : Program) (i fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel + 1 =>
    let c := costCycles p i
    if opcodeIsTerminator (codeByte p i) then c
    else c + blockCost p (i + 1 + skip p i) fuel

/-- GP `ζ^Δ`: naive cycle-sum of the block starting at `pc`. -/
def gasCost (p : Program) (pc : Addr) : Nat := blockCost p pc.toNat (p.code.size + 2)

end Pvm.Spec
