/-
The decoded PVM instruction set (Graypaper App. A, "Instruction Tables"), `JamV1`.

Operands are post-decode:
  * register nibbles are already clamped to `Fin 13`;
  * immediates are already sign-extended to 64 bits (`Val`);
  * offset instructions carry their *resolved* target address (`ı + sext(offset)`) in a `Val`.

Opcode numbers are the leftmost column of the GP instruction tables (`graypaper/text/pvm.tex`).
-/
import Pvm.Common.Types

namespace Pvm

inductive Instr
  -- No arguments (0–2)
  | trap                                          -- 0
  | fallthrough                                   -- 1
  | unlikely                                      -- 2
  -- One immediate (10)
  | ecalli          (x : Val)                     -- 10
  -- One register & one extended-width immediate (20)
  | loadImm64       (a : Reg) (x : Val)           -- 20
  -- Two immediates (30–33)
  | storeImmU8      (addr val : Val)              -- 30
  | storeImmU16     (addr val : Val)              -- 31
  | storeImmU32     (addr val : Val)              -- 32
  | storeImmU64     (addr val : Val)              -- 33
  -- One offset (40)
  | jump            (target : Val)                -- 40
  -- One register & one immediate (50–62)
  | jumpInd         (a : Reg) (x : Val)           -- 50
  | loadImm         (a : Reg) (x : Val)           -- 51
  | loadU8          (a : Reg) (x : Val)           -- 52
  | loadI8          (a : Reg) (x : Val)           -- 53
  | loadU16         (a : Reg) (x : Val)           -- 54
  | loadI16         (a : Reg) (x : Val)           -- 55
  | loadU32         (a : Reg) (x : Val)           -- 56
  | loadI32         (a : Reg) (x : Val)           -- 57
  | loadU64         (a : Reg) (x : Val)           -- 58
  | storeU8         (a : Reg) (x : Val)           -- 59
  | storeU16        (a : Reg) (x : Val)           -- 60
  | storeU32        (a : Reg) (x : Val)           -- 61
  | storeU64        (a : Reg) (x : Val)           -- 62
  -- One register & two immediates (70–73)
  | storeImmIndU8   (a : Reg) (x val : Val)       -- 70
  | storeImmIndU16  (a : Reg) (x val : Val)       -- 71
  | storeImmIndU32  (a : Reg) (x val : Val)       -- 72
  | storeImmIndU64  (a : Reg) (x val : Val)       -- 73
  -- One register, one immediate & one offset (80–90)
  | loadImmJump     (a : Reg) (x target : Val)    -- 80
  | branchEqImm     (a : Reg) (x target : Val)    -- 81
  | branchNeImm     (a : Reg) (x target : Val)    -- 82
  | branchLtUImm    (a : Reg) (x target : Val)    -- 83
  | branchLeUImm    (a : Reg) (x target : Val)    -- 84
  | branchGeUImm    (a : Reg) (x target : Val)    -- 85
  | branchGtUImm    (a : Reg) (x target : Val)    -- 86
  | branchLtSImm    (a : Reg) (x target : Val)    -- 87
  | branchLeSImm    (a : Reg) (x target : Val)    -- 88
  | branchGeSImm    (a : Reg) (x target : Val)    -- 89
  | branchGtSImm    (a : Reg) (x target : Val)    -- 90
  -- Two registers (100–110)
  | moveReg            (d a : Reg)                -- 100
  | countSetBits64     (d a : Reg)                -- 101
  | countSetBits32     (d a : Reg)                -- 102
  | leadingZeroBits64  (d a : Reg)                -- 103
  | leadingZeroBits32  (d a : Reg)                -- 104
  | trailingZeroBits64 (d a : Reg)                -- 105
  | trailingZeroBits32 (d a : Reg)                -- 106
  | signExtend8        (d a : Reg)                -- 107
  | signExtend16       (d a : Reg)                -- 108
  | zeroExtend16       (d a : Reg)                -- 109
  | reverseBytes       (d a : Reg)                -- 110
  -- Two registers & one immediate (120–161)
  | storeIndU8      (a b : Reg) (x : Val)         -- 120
  | storeIndU16     (a b : Reg) (x : Val)         -- 121
  | storeIndU32     (a b : Reg) (x : Val)         -- 122
  | storeIndU64     (a b : Reg) (x : Val)         -- 123
  | loadIndU8       (a b : Reg) (x : Val)         -- 124
  | loadIndI8       (a b : Reg) (x : Val)         -- 125
  | loadIndU16      (a b : Reg) (x : Val)         -- 126
  | loadIndI16      (a b : Reg) (x : Val)         -- 127
  | loadIndU32      (a b : Reg) (x : Val)         -- 128
  | loadIndI32      (a b : Reg) (x : Val)         -- 129
  | loadIndU64      (a b : Reg) (x : Val)         -- 130
  | addImm32        (a b : Reg) (x : Val)         -- 131
  | andImm          (a b : Reg) (x : Val)         -- 132
  | xorImm          (a b : Reg) (x : Val)         -- 133
  | orImm           (a b : Reg) (x : Val)         -- 134
  | mulImm32        (a b : Reg) (x : Val)         -- 135
  | setLtUImm       (a b : Reg) (x : Val)         -- 136
  | setLtSImm       (a b : Reg) (x : Val)         -- 137
  | shloLImm32      (a b : Reg) (x : Val)         -- 138
  | shloRImm32      (a b : Reg) (x : Val)         -- 139
  | sharRImm32      (a b : Reg) (x : Val)         -- 140
  | negAddImm32     (a b : Reg) (x : Val)         -- 141
  | setGtUImm       (a b : Reg) (x : Val)         -- 142
  | setGtSImm       (a b : Reg) (x : Val)         -- 143
  | shloLImmAlt32   (a b : Reg) (x : Val)         -- 144
  | shloRImmAlt32   (a b : Reg) (x : Val)         -- 145
  | sharRImmAlt32   (a b : Reg) (x : Val)         -- 146
  | cmovIzImm       (a b : Reg) (x : Val)         -- 147
  | cmovNzImm       (a b : Reg) (x : Val)         -- 148
  | addImm64        (a b : Reg) (x : Val)         -- 149
  | mulImm64        (a b : Reg) (x : Val)         -- 150
  | shloLImm64      (a b : Reg) (x : Val)         -- 151
  | shloRImm64      (a b : Reg) (x : Val)         -- 152
  | sharRImm64      (a b : Reg) (x : Val)         -- 153
  | negAddImm64     (a b : Reg) (x : Val)         -- 154
  | shloLImmAlt64   (a b : Reg) (x : Val)         -- 155
  | shloRImmAlt64   (a b : Reg) (x : Val)         -- 156
  | sharRImmAlt64   (a b : Reg) (x : Val)         -- 157
  | rotR64Imm       (a b : Reg) (x : Val)         -- 158
  | rotR64ImmAlt    (a b : Reg) (x : Val)         -- 159
  | rotR32Imm       (a b : Reg) (x : Val)         -- 160
  | rotR32ImmAlt    (a b : Reg) (x : Val)         -- 161
  -- Two registers & one offset (170–175)
  | branchEq        (a b : Reg) (target : Val)    -- 170
  | branchNe        (a b : Reg) (target : Val)    -- 171
  | branchLtU       (a b : Reg) (target : Val)    -- 172
  | branchLtS       (a b : Reg) (target : Val)    -- 173
  | branchGeU       (a b : Reg) (target : Val)    -- 174
  | branchGeS       (a b : Reg) (target : Val)    -- 175
  -- Two registers & two immediates (180)
  | loadImmJumpInd  (a b : Reg) (x target : Val)  -- 180
  -- Three registers (190–230)
  | add32           (a b d : Reg)                 -- 190
  | sub32           (a b d : Reg)                 -- 191
  | mul32           (a b d : Reg)                 -- 192
  | divU32          (a b d : Reg)                 -- 193
  | divS32          (a b d : Reg)                 -- 194
  | remU32          (a b d : Reg)                 -- 195
  | remS32          (a b d : Reg)                 -- 196
  | shloL32         (a b d : Reg)                 -- 197
  | shloR32         (a b d : Reg)                 -- 198
  | sharR32         (a b d : Reg)                 -- 199
  | add64           (a b d : Reg)                 -- 200
  | sub64           (a b d : Reg)                 -- 201
  | mul64           (a b d : Reg)                 -- 202
  | divU64          (a b d : Reg)                 -- 203
  | divS64          (a b d : Reg)                 -- 204
  | remU64          (a b d : Reg)                 -- 205
  | remS64          (a b d : Reg)                 -- 206
  | shloL64         (a b d : Reg)                 -- 207
  | shloR64         (a b d : Reg)                 -- 208
  | sharR64         (a b d : Reg)                 -- 209
  | and             (a b d : Reg)                 -- 210
  | xor             (a b d : Reg)                 -- 211
  | or              (a b d : Reg)                 -- 212
  | mulUpperSS      (a b d : Reg)                 -- 213
  | mulUpperUU      (a b d : Reg)                 -- 214
  | mulUpperSU      (a b d : Reg)                 -- 215
  | setLtU          (a b d : Reg)                 -- 216
  | setLtS          (a b d : Reg)                 -- 217
  | cmovIz          (a b d : Reg)                 -- 218
  | cmovNz          (a b d : Reg)                 -- 219
  | rotL64          (a b d : Reg)                 -- 220
  | rotL32          (a b d : Reg)                 -- 221
  | rotR64          (a b d : Reg)                 -- 222
  | rotR32          (a b d : Reg)                 -- 223
  | andInv          (a b d : Reg)                 -- 224
  | orInv           (a b d : Reg)                 -- 225
  | xnor            (a b d : Reg)                 -- 226
  | max             (a b d : Reg)                 -- 227
  | maxU            (a b d : Reg)                 -- 228
  | min             (a b d : Reg)                 -- 229
  | minU            (a b d : Reg)                 -- 230
  deriving DecidableEq, Repr, Inhabited

/-- Block-termination instructions (GP set `T`): those that may set the instruction
    counter to something other than `ı + 1 + skip(ı)`, plus `trap`/`fallthrough`.
    Note `unlikely` is *not* a terminator. -/
def Instr.isTerminator : Instr → Bool
  | .trap | .fallthrough
  | .jump _ | .jumpInd _ _
  | .loadImmJump _ _ _ | .loadImmJumpInd _ _ _ _
  | .branchEqImm _ _ _ | .branchNeImm _ _ _
  | .branchLtUImm _ _ _ | .branchLeUImm _ _ _ | .branchGeUImm _ _ _ | .branchGtUImm _ _ _
  | .branchLtSImm _ _ _ | .branchLeSImm _ _ _ | .branchGeSImm _ _ _ | .branchGtSImm _ _ _
  | .branchEq _ _ _ | .branchNe _ _ _
  | .branchLtU _ _ _ | .branchLtS _ _ _ | .branchGeU _ _ _ | .branchGeS _ _ _ => true
  | _ => false

end Pvm
