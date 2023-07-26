import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Vector.Basic
import Mathlib.Tactic.GCongr
import Risc0.BasicTypes
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart31
import Risc0.Gadgets.Decoder.Lemmas

open Risc0

-- void DecoderImpl::set(U32Val inst) {
--   NONDET {
--     f7_6->set((inst.bytes[3] & 0x80) / (1 << 7));
--     f7_45->set((inst.bytes[3] & 0x60) / (1 << 5));
--     f7_3->set((inst.bytes[3] & 0x10) / (1 << 4));
--     f7_2->set((inst.bytes[3] & 0x08) / (1 << 3));
--     f7_01->set((inst.bytes[3] & 0x06) / (1 << 1));
--     rs2_4->set((inst.bytes[3] & 0x01) / (1 << 0));
--     rs2_3->set((inst.bytes[2] & 0x80) / (1 << 7));
--     rs2_12->set((inst.bytes[2] & 0x60) / (1 << 5));
--     rs2_0->set((inst.bytes[2] & 0x10) / (1 << 4));
--     rs1_34->set((inst.bytes[2] & 0x0C) / (1 << 2));
--     rs1_12->set((inst.bytes[2] & 0x03) / (1 << 0));
--     rs1_0->set((inst.bytes[1] & 0x80) / (1 << 7));
--     func3_2->set((inst.bytes[1] & 0x40) / (1 << 6));
--     func3_01->set((inst.bytes[1] & 0x30) / (1 << 4));
--     rd_34->set((inst.bytes[1] & 0x0C) / (1 << 2));
--     rd_12->set((inst.bytes[1] & 0x03) / (1 << 0));
--     rd_0->set((inst.bytes[0] & 0x80) / (1 << 7));
--     opcode_->set(inst.bytes[0] & 0x7f);
--   }
--   eq(inst.bytes[3], func7() * 0x02 + rs2_4);
--   eq(inst.bytes[2], (rs2_3 * 0x08 + rs2_12 * 0x02 + rs2_0) * 0x10 + rs1_34 * 0x04 + rs1_12);
--   eq(inst.bytes[1], rs1_0 * 0x80 + func3() * 0x10 + rd_34 * 0x04 + rd_12);
--   eq(inst.bytes[0], rd_0 * 0x80 + opcode_);
-- }

structure Instruction where
  f7_6     : Felt
  f7_45    : Felt
  f7_3     : Felt
  f7_2     : Felt
  f7_01    : Felt
  rs2_4    : Felt
  rs2_3    : Felt
  rs2_12   : Felt
  rs2_0    : Felt 
  rs1_34   : Felt
  rs1_12   : Felt
  rs1_0    : Felt
  func3_2  : Felt
  func3_01 : Felt
  rd_34    : Felt
  rd_12    : Felt
  rd_0     : Felt
  opcode_  : Felt

def Instruction.toList (instr : Instruction) : List Felt :=
  [instr.f7_01, instr.f7_45, instr.rs2_12, instr.rs1_12, instr.rs1_34, instr.func3_01, instr.rd_12, instr.rd_34, instr.f7_2, instr.f7_3, instr.f7_6, instr.rs2_0, instr.rs2_3, instr.rs2_4, instr.rs1_0, instr.func3_2, instr.rd_0, instr.opcode_]
lemma Instruction.toList_def {instr : Instruction} : 
  instr.toList =  [instr.f7_01, instr.f7_45, instr.rs2_12, instr.rs1_12, instr.rs1_34, instr.func3_01, instr.rd_12, instr.rd_34, instr.f7_2, instr.f7_3, instr.f7_6, instr.rs2_0, instr.rs2_3, instr.rs2_4, instr.rs1_0, instr.func3_2, instr.rd_0, instr.opcode_] := by rfl


def Instruction.fromList (l : List Felt) : Instruction :=
  Instruction.mk 
    (l.get! 10)
    (l.get! 1)
    (l.get! 9)
    (l.get! 8)
    (l.get! 0)
    (l.get! 13)
    (l.get! 12)
    (l.get! 2)
    (l.get! 11)
    (l.get! 4)
    (l.get! 3)
    (l.get! 14)
    (l.get! 15)
    (l.get! 5)
    (l.get! 7)
    (l.get! 6)
    (l.get! 16)
    (l.get! 17)

lemma Instruction.fromList_def {l : List Felt} :
  Instruction.fromList l = Instruction.mk 
    (l.get! 10)
    (l.get! 1)
    (l.get! 9)
    (l.get! 8)
    (l.get! 0)
    (l.get! 13)
    (l.get! 12)
    (l.get! 2)
    (l.get! 11)
    (l.get! 4)
    (l.get! 3)
    (l.get! 14)
    (l.get! 15)
    (l.get! 5)
    (l.get! 7)
    (l.get! 6)
    (l.get! 16)
    (l.get! 17) := by rfl

def Instruction.toWords (instr : Instruction) : List Felt :=
  [ instr.rd_0 * 0x80 + instr.opcode_
  , instr.rs1_0 * 0x80 + (instr.func3_2 * 0x04 + instr.func3_01) * 0x10 + instr.rd_34 * 0x04 + instr.rd_12
  , (instr.rs2_3 * 0x08 + instr.rs2_12 * 0x02 + instr.rs2_0) * 0x10 + instr.rs1_34 * 0x04 + instr.rs1_12
  , (instr.f7_6 * 0x40 + (instr.f7_45 * 0x10 + instr.f7_3 * 0x08 + instr.f7_2 * 0x04 + instr.f7_01)) * 0x02 + instr.rs2_4]

def Instruction.fromWords (words : BufferAtTime) : Instruction :=
  let word0 := Bitvec.ofNat 32 (words.get! 0).get!.val
  let word1 := Bitvec.ofNat 32 (words.get! 1).get!.val
  let word2 := Bitvec.ofNat 32 (words.get! 2).get!.val
  let word3 := Bitvec.ofNat 32 (words.get! 3).get!.val
  Instruction.mk 
    (Bitvec.ushr (Bitvec.and word3 (Bitvec.ofNat 32 0x80)) 7).toNat
    (Bitvec.ushr (Bitvec.and word3 (Bitvec.ofNat 32 0x60)) 5).toNat
    (Bitvec.ushr (Bitvec.and word3 (Bitvec.ofNat 32 0x10)) 4).toNat
    (Bitvec.ushr (Bitvec.and word3 (Bitvec.ofNat 32 0x08)) 3).toNat
    (Bitvec.ushr (Bitvec.and word3 (Bitvec.ofNat 32 0x06)) 1).toNat
    (Bitvec.ushr (Bitvec.and word3 (Bitvec.ofNat 32 0x01)) 0).toNat
    (Bitvec.ushr (Bitvec.and word2 (Bitvec.ofNat 32 0x80)) 7).toNat
    (Bitvec.ushr (Bitvec.and word2 (Bitvec.ofNat 32 0x60)) 5).toNat
    (Bitvec.ushr (Bitvec.and word2 (Bitvec.ofNat 32 0x10)) 4).toNat
    (Bitvec.ushr (Bitvec.and word2 (Bitvec.ofNat 32 0x0C)) 2).toNat
    (Bitvec.ushr (Bitvec.and word2 (Bitvec.ofNat 32 0x03)) 0).toNat
    (Bitvec.ushr (Bitvec.and word1 (Bitvec.ofNat 32 0x80)) 7).toNat
    (Bitvec.ushr (Bitvec.and word1 (Bitvec.ofNat 32 0x40)) 6).toNat
    (Bitvec.ushr (Bitvec.and word1 (Bitvec.ofNat 32 0x30)) 4).toNat
    (Bitvec.ushr (Bitvec.and word1 (Bitvec.ofNat 32 0x0C)) 2).toNat
    (Bitvec.ushr (Bitvec.and word1 (Bitvec.ofNat 32 0x03)) 0).toNat
    (Bitvec.ushr (Bitvec.and word0 (Bitvec.ofNat 32 0x80)) 7).toNat
    (Bitvec.and word0 (Bitvec.ofNat 32 0x7f)).toNat

def instr_equality (instr : Instruction) (input : BufferAtTime) : Prop :=
  input = instr.toWords

def decoder_direct_spec (input : BufferAtTime) (output : BufferAtTime) : Prop :=
  input.length = 4  
  ∧ output = (Instruction.fromWords input).toList.map some

def isByte (x : Felt) := x.val ≤ 255

lemma byte_destruct₁ {x : ℕ} (h : x < 256):
  (Bitvec.toNat (Bitvec.ofNat 32 x) / 128 % 2) * 128 +
      (Bitvec.toNat
          (Bitvec.and (Bitvec.ofNat 32 x) (Bitvec.ofNat 32 (allOnes 7)))) = x := by 
  have h' : 128 = 2 ^ 7 := by rfl
  rw [h', Bitvec.ushr_toNat,
      ←Bitvec.lastBit (by linarith)]
  have h' : Bitvec.ofNat (32 : ℕ) (allOnes (1 : ℕ)) = (Bitvec.ofNat (32 : ℕ) (allOnes (8 : ℕ))).ushr 7 := by
    rw [Bitvec.allOnes_ushr (by linarith) (by linarith)]
  rw [h', Bitvec.toNat_and_allOnes,
      ←Bitvec.ushr_and_commute,
      Nat.mul_comm,
      ←Bitvec.ushr_toNat,
      ←Bitvec.and_ofNat_allOnes (by {
        have h'' : 256 = 2^8 := by simp
        rw [h''] at h
        exact h
      }) (by linarith),
      Nat.div_add_mod,
      Bitvec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_trans h (by linarith))]
  
lemma toe_lemma {x : ℕ}:
  (4 : ℕ) * (x / (4 : ℕ) % (4 : ℕ)) + x % (4 : ℕ) = x % 16 := by
  apply @Nat.add_left_cancel (16 * (x /16))
  rw [Nat.div_add_mod]
  have h : 16 * (x / 16) = 4 * (4 * ((x/4)/4)) := by
    rw [Nat.div_div_eq_div_mul]
    ring_nf
  rw [h]
  have h : (4 : ℕ) * (4* (x / 4 / 4)) +
    ((4 : ℕ) * (x / 4 % 4)) = 4 * (x / 4) := by
    rw [←Nat.mul_add,
        Nat.div_add_mod]
  rw [←Nat.add_assoc, h, Nat.div_add_mod]

lemma toe_lemma₁ {x : ℕ}:
  ((4 : ℕ) * (x / (64 : ℕ) % (2 : ℕ)) + x / (16 : ℕ) % (4 : ℕ)) = x/16 % 8 := by
  apply @Nat.add_left_cancel (8 * (x /16/8))
  rw [Nat.div_add_mod, Nat.div_div_eq_div_mul]
  norm_num
  have h : (8 : ℕ) * (x / (128 : ℕ)) = 4 * (2 * ((x/64)/2)) := by
    rw [Nat.div_div_eq_div_mul]
    ring_nf
  rw [h]
  have h : (4 : ℕ) * ((2 : ℕ) * (x / (64 : ℕ) / (2 : ℕ))) + ((4 : ℕ) * (x / (64 : ℕ) % (2 : ℕ))) = 
    4 * (x / 16 / 4) := by
    rw [←Nat.mul_add,
        Nat.div_add_mod,
        Nat.div_div_eq_div_mul]
  rw [←Nat.add_assoc, h, Nat.div_add_mod]

lemma toe_lemma₂ {x : ℕ}:
  x / (128 : ℕ) * (128 : ℕ) + x / (16 : ℕ) % (8 : ℕ) * (16 : ℕ) = 16 * (x / 16) := by
  rw [Nat.mul_comm _ 16, Nat.mul_comm _ 128]
  have h : 128 = 16 * 8 := by rfl
  rw [h, Nat.mul_assoc 16, ←Nat.mul_add 16, ←Nat.div_div_eq_div_mul, Nat.div_add_mod]

lemma toe_lemma₃ {x : ℕ}:
  x / (32 : ℕ) % (4 : ℕ) * (2 : ℕ) + x / (16 : ℕ) % (2 : ℕ) = (x / 16) % 8 := by
  apply @Nat.add_left_cancel (8 * (x /16/8))
  rw [Nat.div_add_mod, Nat.div_div_eq_div_mul]
  norm_num
  have h : (8 : ℕ) * (x / (128 : ℕ)) = 2 * (4 * ((x/32)/4)) := by
    rw [Nat.div_div_eq_div_mul]
    ring_nf
  rw [h, Nat.mul_comm _ 2]
  have h : (2 : ℕ) * ((4 : ℕ) * (x / (32 : ℕ) / (4 : ℕ))) + ((2 : ℕ) * (x / (32 : ℕ) % (4 : ℕ))) = 
    2 * (x / 32 ) := by
    rw [←Nat.mul_add,
        Nat.div_add_mod]
  have h' : 32 = 16 * 2 := by rfl
  rw [←Nat.add_assoc, h, h', ←Nat.div_div_eq_div_mul, Nat.div_add_mod]

lemma toe_lemma₄ {x : ℕ}:
  (4 : ℕ) * (x / (8 : ℕ) % (2 : ℕ)) + x / (2 : ℕ) % (4 : ℕ) = (x / 2) % 8 := by
  apply @Nat.add_left_cancel (8 * (x /2/8))
  rw [Nat.div_add_mod, Nat.div_div_eq_div_mul]
  norm_num
  have h : (8 : ℕ) * (x / (16 : ℕ)) = 4 * (2 * ((x/8)/2)) := by
    rw [Nat.div_div_eq_div_mul]
    ring_nf
  rw [h]
  have h : (4 : ℕ) * ((2 : ℕ) * (x / (8 : ℕ) / (2 : ℕ))) + ((4 : ℕ) * (x / (8 : ℕ) % (2 : ℕ))) = 
    4 * (x / 8 ) := by
    rw [←Nat.mul_add,
        Nat.div_add_mod]
  have h' : 8 = 2 * 4 := by rfl
  rw [←Nat.add_assoc, h, h', ←Nat.div_div_eq_div_mul, Nat.div_add_mod]

lemma toe_lemma₅ {x : ℕ}:
  (2 : ℕ) * (x / (2 : ℕ) % (8 : ℕ)) + x % (2 : ℕ) = x % 16 := by
  apply @Nat.add_left_cancel (16 * (x / 16))
  rw [Nat.div_add_mod]
  norm_num
  have h : (16 : ℕ) * (x / (16 : ℕ)) = 2 * (8 * ((x/2)/8)) := by
    rw [Nat.div_div_eq_div_mul]
    ring_nf
  rw [h]
  have h : (2 : ℕ) * ((8 : ℕ) * (x / (2 : ℕ) / (8 : ℕ))) + ((2 : ℕ) * (x / (2 : ℕ) % (8 : ℕ))) = 
    2 * (x / 2) := by
    rw [←Nat.mul_add,
        Nat.div_add_mod]
  rw [←Nat.add_assoc, h, Nat.div_add_mod]

lemma byte_destruct₂ {x : ℕ} (h : x < 256):
  (Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x) (Bitvec.ofNat 32 128)) 7) * 128 +
          (Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x) (Bitvec.ofNat 32 64)) 6) * 4 +
              Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x) (Bitvec.ofNat 32 48)) 4)) *
            16 +
        Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x) (Bitvec.ofNat 32 12)) 2) * 4 +
      Bitvec.toNat (Bitvec.and (Bitvec.ofNat 32 x) (Bitvec.ofNat 32 3))) = x := by 
  rw [Bitvec.ushr_and_commute,
      Bitvec.ushr_ofNat (Nat.lt_trans h (by linarith))]
  have h' : (Bitvec.ushr (Bitvec.ofNat (32 : ℕ) (128 : ℕ)) (7 : ℕ)) = Bitvec.ofNat 32 (allOnes 1) := by rfl
  rw [h',
      Bitvec.lastBit (by {
        linarith
      }),
      Bitvec.toNat_ofNat]
  have h' : x / (2 : ℕ) ^ (7 : ℕ) % (2 : ℕ) ^ (32 : ℕ) = x / (2 : ℕ) ^ (7 : ℕ) := by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_of_le_of_lt
      apply Nat.div_le_self
      apply Nat.lt_trans
      exact h
      linarith
    })]
  rw [h',
      Bitvec.ushr_and_commute,
      Bitvec.ushr_ofNat (Nat.lt_trans h (by linarith))]
  have h' : (Bitvec.ushr (Bitvec.ofNat (32 : ℕ) (64 : ℕ)) (6 : ℕ)) = Bitvec.ofNat 32 (allOnes 1) := by rfl
  rw [h',
      Bitvec.lastBit (by {
        linarith
      }),
      Bitvec.toNat_ofNat]
  have h' : x / (2 : ℕ) ^ (6 : ℕ) % (2 : ℕ) ^ (32 : ℕ) = x / 2 ^ 6 := by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_of_le_of_lt
      apply Nat.div_le_self
      apply Nat.lt_trans
      exact h
      linarith
    })]
  rw [h', Bitvec.ushr_and_commute,
      Bitvec.ushr_ofNat (Nat.lt_trans h (by linarith))]
  have h' : (Bitvec.ushr (Bitvec.ofNat (32 : ℕ) (48 : ℕ)) (4 : ℕ)) = Bitvec.ofNat 32 (allOnes 2) := by rfl
  rw [h',
      Bitvec.toNat_and_allOnes,
      Bitvec.toNat_ofNat]
  have h' : x / (2 : ℕ) ^ (4 : ℕ) % (2 : ℕ) ^ (32 : ℕ) = x / (2 : ℕ) ^ (4 : ℕ) := by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_of_le_of_lt
      apply Nat.div_le_self
      apply Nat.lt_trans
      exact h
      linarith
    })]
  rw [h', Bitvec.ushr_and_commute, Bitvec.ushr_ofNat (Nat.lt_trans h (by linarith))]
  have h' : (Bitvec.ushr (Bitvec.ofNat (32 : ℕ) (12 : ℕ)) (2 : ℕ)) = Bitvec.ofNat 32 (allOnes 2) := by rfl
  rw [h',
      Bitvec.toNat_and_allOnes,
      Bitvec.toNat_ofNat]
  have h' : x / (2 : ℕ) ^ (2 : ℕ) % (2 : ℕ) ^ (32 : ℕ)  = x / 2^2 := by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_of_le_of_lt
      apply Nat.div_le_self
      apply Nat.lt_trans
      exact h
      linarith
    })]
  rw [h']
  have h' : (Bitvec.ofNat (32 : ℕ) (3 : ℕ)) = Bitvec.ofNat 32 (allOnes 2) := by rfl
  rw [h', 
      Bitvec.toNat_and_allOnes,
      Bitvec.toNat_ofNat]
  have h' : x % (2 : ℕ) ^ (32 : ℕ) = x := by
    rw [Nat.mod_eq_of_lt (Nat.lt_trans h (by linarith))]
  rw [h']
  norm_num
  have h' : x / 128 % (2 : ℕ) = x / 128 := by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_of_le_of_lt
      apply Nat.div_le_div
      exact Nat.le_of_lt_succ h
      apply Nat.le_refl
      simp
      simp
    })]
  rw [h', Nat.add_assoc, Nat.mul_comm _ 4, Nat.mul_comm _ 4, toe_lemma, toe_lemma₁, toe_lemma₂, Nat.div_add_mod]


lemma byte_destruct₃ {x : ℕ} (h : x < 256):
  ((Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x) (Bitvec.ofNat 32 128)) 7) * 8 +
              Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x) (Bitvec.ofNat 32 96)) 5) * 2 +
            Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x) (Bitvec.ofNat 32 16)) 4)) *
          16 +
        Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x) (Bitvec.ofNat 32 12)) 2) * 4 +
      Bitvec.toNat (Bitvec.and (Bitvec.ofNat 32 x) (Bitvec.ofNat 32 3))) = x := by 
  rw [Bitvec.ushr_and_commute,
      Bitvec.ushr_ofNat (Nat.lt_trans h (by linarith))]
  have h' : (Bitvec.ushr (Bitvec.ofNat (32 : ℕ) (128 : ℕ)) (7 : ℕ)) = Bitvec.ofNat 32 (allOnes 1) := by rfl
  rw [h',
      Bitvec.lastBit (by {
        linarith
      }),
      Bitvec.toNat_ofNat]
  have h' : x / (2 : ℕ) ^ (7 : ℕ) % (2 : ℕ) ^ (32 : ℕ) = x / (2 : ℕ) ^ (7 : ℕ) := by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_of_le_of_lt
      apply Nat.div_le_self
      apply Nat.lt_trans
      exact h
      linarith
    })]
  rw [h',
      Bitvec.ushr_and_commute,
      Bitvec.ushr_ofNat (Nat.lt_trans h (by linarith))]
  have h' : (Bitvec.ushr (Bitvec.ofNat (32 : ℕ) (96 : ℕ)) (5 : ℕ)) = Bitvec.ofNat 32 (allOnes 2) := by rfl
  rw [h',
      Bitvec.toNat_and_allOnes,
      Bitvec.toNat_ofNat]
  have h' : x / (2 : ℕ) ^ (5 : ℕ) % (2 : ℕ) ^ (32 : ℕ) = x / 2 ^ 5 := by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_of_le_of_lt
      apply Nat.div_le_self
      apply Nat.lt_trans
      exact h
      linarith
    })]
  rw [h', Bitvec.ushr_and_commute,
      Bitvec.ushr_ofNat (Nat.lt_trans h (by linarith))]
  have h' : (Bitvec.ushr (Bitvec.ofNat (32 : ℕ) (16 : ℕ)) (4 : ℕ)) = Bitvec.ofNat 32 (allOnes 1) := by rfl
  rw [h',
      Bitvec.toNat_and_allOnes,
      Bitvec.toNat_ofNat]
  have h' : x / (2 : ℕ) ^ (4 : ℕ) % (2 : ℕ) ^ (32 : ℕ) = x / (2 : ℕ) ^ (4 : ℕ) := by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_of_le_of_lt
      apply Nat.div_le_self
      apply Nat.lt_trans
      exact h
      linarith
    })]
  rw [h', Bitvec.ushr_and_commute, Bitvec.ushr_ofNat (Nat.lt_trans h (by linarith))]
  have h' : (Bitvec.ushr (Bitvec.ofNat (32 : ℕ) (12 : ℕ)) (2 : ℕ)) = Bitvec.ofNat 32 (allOnes 2) := by rfl
  rw [h',
      Bitvec.toNat_and_allOnes,
      Bitvec.toNat_ofNat]
  have h' : x / (2 : ℕ) ^ (2 : ℕ) % (2 : ℕ) ^ (32 : ℕ)  = x / 2^2 := by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_of_le_of_lt
      apply Nat.div_le_self
      apply Nat.lt_trans
      exact h
      linarith
    })]
  rw [h']
  have h' : (Bitvec.ofNat (32 : ℕ) (3 : ℕ)) = Bitvec.ofNat 32 (allOnes 2) := by rfl
  rw [h', 
      Bitvec.toNat_and_allOnes,
      Bitvec.toNat_ofNat]
  have h' : x % (2 : ℕ) ^ (32 : ℕ) = x := by
    rw [Nat.mod_eq_of_lt (Nat.lt_trans h (by linarith))]
  rw [h']
  norm_num
  have h' : x / 128 % (2 : ℕ) = x / 128 := by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_of_le_of_lt
      apply Nat.div_le_div
      exact Nat.le_of_lt_succ h
      apply Nat.le_refl
      simp
      simp
    })]
  rw [h', Nat.add_assoc, Nat.mul_comm _ 4, toe_lemma, Nat.add_assoc, toe_lemma₃, Nat.add_mul, Nat.mul_assoc]
  norm_num
  rw [toe_lemma₂, Nat.div_add_mod]


lemma byte_destruct₄ {x : ℕ} (h : x < 256):
  ((Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x) (Bitvec.ofNat 32 128)) 7) * 64 +
          (Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x) (Bitvec.ofNat 32 96)) 5) * 16 +
                Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x) (Bitvec.ofNat 32 16)) 4) * 8 +
              Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x) (Bitvec.ofNat 32 8)) 3) * 4 +
            Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x) (Bitvec.ofNat 32 6)) 1))) *
        2 +
      Bitvec.toNat (Bitvec.and (Bitvec.ofNat 32 x) (Bitvec.ofNat 32 1))) = x := by 
  rw [Bitvec.ushr_and_commute,
      Bitvec.ushr_ofNat (Nat.lt_trans h (by linarith))]
  have h' : (Bitvec.ushr (Bitvec.ofNat (32 : ℕ) (128 : ℕ)) (7 : ℕ)) = Bitvec.ofNat 32 (allOnes 1) := by rfl
  rw [h',
      Bitvec.lastBit (by {
        linarith
      }),
      Bitvec.toNat_ofNat]
  have h' : x / (2 : ℕ) ^ (7 : ℕ) % (2 : ℕ) ^ (32 : ℕ) = x / (2 : ℕ) ^ (7 : ℕ) := by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_of_le_of_lt
      apply Nat.div_le_self
      apply Nat.lt_trans
      exact h
      linarith
    })]
  rw [h',
      Bitvec.ushr_and_commute,
      Bitvec.ushr_ofNat (Nat.lt_trans h (by linarith))]
  have h' : (Bitvec.ushr (Bitvec.ofNat (32 : ℕ) (96 : ℕ)) (5 : ℕ)) = Bitvec.ofNat 32 (allOnes 2) := by rfl
  rw [h',
      Bitvec.toNat_and_allOnes,
      Bitvec.toNat_ofNat]
  have h' : x / (2 : ℕ) ^ (5 : ℕ) % (2 : ℕ) ^ (32 : ℕ) = x / 2 ^ 5 := by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_of_le_of_lt
      apply Nat.div_le_self
      apply Nat.lt_trans
      exact h
      linarith
    })]
  rw [h', Bitvec.ushr_and_commute,
      Bitvec.ushr_ofNat (Nat.lt_trans h (by linarith))]
  have h' : (Bitvec.ushr (Bitvec.ofNat (32 : ℕ) (16 : ℕ)) (4 : ℕ)) = Bitvec.ofNat 32 (allOnes 1) := by rfl
  rw [h',
      Bitvec.toNat_and_allOnes,
      Bitvec.toNat_ofNat]
  have h' : x / (2 : ℕ) ^ (4 : ℕ) % (2 : ℕ) ^ (32 : ℕ) = x / (2 : ℕ) ^ (4 : ℕ) := by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_of_le_of_lt
      apply Nat.div_le_self
      apply Nat.lt_trans
      exact h
      linarith
    })]
  rw [h', Bitvec.ushr_and_commute, Bitvec.ushr_ofNat (Nat.lt_trans h (by linarith))]
  have h' : (Bitvec.ushr (Bitvec.ofNat (32 : ℕ) (8 : ℕ)) (3 : ℕ)) = Bitvec.ofNat 32 (allOnes 1) := by rfl
  rw [h',
      Bitvec.toNat_and_allOnes,
      Bitvec.toNat_ofNat]
  have h' : x / (2 : ℕ) ^ (3 : ℕ) % (2 : ℕ) ^ (32 : ℕ)  = x / 2^3 := by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_of_le_of_lt
      apply Nat.div_le_self
      apply Nat.lt_trans
      exact h
      linarith
    })]
  rw [h', Bitvec.ushr_and_commute, Bitvec.ushr_ofNat (Nat.lt_trans h (by linarith))]
  have h' : (Bitvec.ushr (Bitvec.ofNat (32 : ℕ) (6 : ℕ)) (1 : ℕ)) = Bitvec.ofNat 32 (allOnes 2) := by rfl
  rw [h', 
      Bitvec.toNat_and_allOnes,
      Bitvec.toNat_ofNat]
  have h' :  x / (2 : ℕ) ^ (1 : ℕ) % (2 : ℕ) ^ (32 : ℕ) = x / (2 : ℕ) ^ (1 : ℕ) := by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_of_le_of_lt
      apply Nat.div_le_self
      apply Nat.lt_trans
      exact h
      linarith
    })]
  have h'' : (Bitvec.ofNat (32 : ℕ) (1 : ℕ)) = Bitvec.ofNat 32 (allOnes 1) := by rfl
  rw [h', h'',
      Bitvec.lastBit (by {
        linarith
      }),
      Bitvec.toNat_ofNat]
  have h' : x % (2 : ℕ) ^ (32 : ℕ) = x :=by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_trans
      exact h
      linarith
    })]
  rw [h']
  norm_num
  have h' : x / 128 % (2 : ℕ) = x / 128 := by
    rw [Nat.mod_eq_of_lt (by {
      apply Nat.lt_of_le_of_lt
      apply Nat.div_le_div
      exact Nat.le_of_lt_succ h
      apply Nat.le_refl
      simp
      simp
    })]
  rw [h', Nat.add_assoc, Nat.mul_comm _ 4, toe_lemma₄]
  have h' : x / (32 : ℕ) % (4 : ℕ) * (16 : ℕ) + x / (16 : ℕ) % (2 : ℕ) * (8 : ℕ) = (x / (32 : ℕ) % (4 : ℕ) * (2 : ℕ) + x / (16 : ℕ) % (2 : ℕ)) * (8 : ℕ) := by ring_nf
  rw [h', toe_lemma₃, Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
  norm_num
  rw [←Nat.add_assoc, toe_lemma₂, Nat.add_assoc, Nat.mul_comm _ 2, toe_lemma₅, Nat.div_add_mod]
  

theorem toWords_fromWords {words : BufferAtTime} (h : words.length = 4) (h_isBytes : (∀ i, i < 4 → isByte (Option.get! (words.get! i)))) (h_isSome : (∀ i, i < 4 → ∃ x, words.get! i = some x)):
  (Instruction.fromWords words).toWords.map some = words := by
  unfold Instruction.toWords Instruction.fromWords
  simp
  apply List.ext
  intros n
  rcases n with _ | ⟨_ | ⟨_ | ⟨_ | n ⟩⟩⟩; simp
  · rw [List.get!_eq_get? (by simp [h])]
    simp
    --have h' : 128 = allOnes 7 + 1 := by simp
    rw [Bitvec.ushr_and_commute]
    have h' : (Bitvec.ushr (Bitvec.ofNat 32 128) 7) = Bitvec.ofNat 32 1 := by
      rw [Bitvec.ushr_ofNat (by linarith)]
      have h : (128 : ℕ) / (2 : ℕ) ^ (7 : ℕ) = 1 := by rfl
      rw [h]
    have h'' : allOnes 1 = 1 := by simp
    rw [←h''] at h'
    rw [h']
    rw [Bitvec.lastBit (by {
      apply Nat.succ_le_succ
      exact Nat.zero_le 31
    })]
    rw [←Bitvec.ushr_toNat]
    have h_2 : 2 ^ 7 = 128 := by simp
    rw [h_2]
    have h_3 : 127 = allOnes 7 := by simp
    rw [h_3]
    have h_4 : (↑(Bitvec.toNat (Bitvec.ofNat 32 (ZMod.val (Option.get! (List.get! words 0)))) / 128 % 2) * 128 : Felt) = ↑(Bitvec.toNat (Bitvec.ofNat 32 (ZMod.val (Option.get! (List.get! words 0)))) / 128 % 2 * 128) := by simp
    rw [h_4]
    have h_5 : (↑(Bitvec.toNat (Bitvec.ofNat 32 (ZMod.val (Option.get! (List.get! words 0)))) / 128 % 2 * 128) + ↑(Bitvec.toNat
      (Bitvec.and (Bitvec.ofNat 32 (ZMod.val (Option.get! (List.get! words 0)))) (Bitvec.ofNat 32 (allOnes 7))))) = (↑((Bitvec.toNat (Bitvec.ofNat 32 (ZMod.val (Option.get! (List.get! words 0)))) / 128 % 2 * 128) + (Bitvec.toNat
      (Bitvec.and (Bitvec.ofNat 32 (ZMod.val (Option.get! (List.get! words 0)))) (Bitvec.ofNat 32 (allOnes 7))))) : Felt) := by simp
    rw [h_5]
    rw [byte_destruct₁ (by {
      have h := h_isBytes 0 (by simp)
      unfold isByte at h
      exact Nat.lt_succ_of_le h
    })]
    rcases (h_isSome 0 (by simp)) with ⟨x, h'''⟩
    rw [h''']
    simp
  · simp
    rw [List.get!_eq_get? (by simp [h])]
    rcases (h_isSome 1 (by simp)) with ⟨x, h_isSome⟩ 
    rw [h_isSome]
    simp
    have h' : ↑(Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 128)) 7)) * 128 +
        (↑(Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 64)) 6)) * 4 +
            ↑(Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 48)) 4))) *
          16 +
      ↑(Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 12)) 2)) * 4 +
    ↑(Bitvec.toNat (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 3))) = (↑((Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 128)) 7)) * 128 +
        ((Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 64)) 6)) * 4 +
            (Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 48)) 4))) *
          16 +
      (Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 12)) 2)) * 4 +
    (Bitvec.toNat (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 3)))) : Felt) := by simp
    rw [h']
    rw [byte_destruct₂ (by {
      have h := h_isBytes 1 (by simp)
      unfold isByte at h
      rw [h_isSome] at h
      exact Nat.lt_succ_of_le h
    })]
    simp
  · simp
    rw [List.get!_eq_get? (by simp[h])]
    simp
    rcases (h_isSome 2 (by simp)) with ⟨x, h_isSome⟩ 
    rw [h_isSome]
    simp
    have h' : (↑(Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 128)) 7)) * 8 +
            ↑(Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 96)) 5)) * 2 +
          ↑(Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 16)) 4))) *
        16 +
      ↑(Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 12)) 2)) * 4 +
    ↑(Bitvec.toNat (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 3))) = (↑(((Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 128)) 7)) * 8 +
            (Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 96)) 5)) * 2 +
          (Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 16)) 4))) *
        16 +
      (Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 12)) 2)) * 4 +
    (Bitvec.toNat (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 3)))) : Felt) := by simp
    rw [h']
    rw [byte_destruct₃ (by {
      have h := h_isBytes 2 (by simp)
      unfold isByte at h
      rw [h_isSome] at h
      exact Nat.lt_succ_of_le h
    })]
    simp
  · simp
    rw [List.get!_eq_get? (by simp[h])]
    simp
    rcases (h_isSome 3 (by simp)) with ⟨x, h_isSome⟩ 
    rw [h_isSome]
    simp
    have h' : (↑(Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 128)) 7)) * 64 +
        (↑(Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 96)) 5)) * 16 +
              ↑(Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 16)) 4)) * 8 +
            ↑(Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 8)) 3)) * 4 +
          ↑(Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 6)) 1)))) *
      2 +
    ↑(Bitvec.toNat (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 1))) = (↑(((Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 128)) 7)) * 64 +
        ((Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 96)) 5)) * 16 +
              (Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 16)) 4)) * 8 +
            (Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 8)) 3)) * 4 +
          (Bitvec.toNat (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 6)) 1)))) *
      2 +
    (Bitvec.toNat (Bitvec.and (Bitvec.ofNat 32 (ZMod.val x)) (Bitvec.ofNat 32 1)))) : Felt) := by simp
    rw [h']
    rw [byte_destruct₄ (by {
      have h := h_isBytes 3 (by simp)
      unfold isByte at h
      rw [h_isSome] at h
      exact Nat.lt_succ_of_le h
    })]
    simp
  · simp
    symm
    rw [List.get?_eq_none]
    rw [h]
    linarith

lemma leg_128 {x : Felt} :
  feltBitAnd x (128 : Felt) * (1997537281 : Felt) = (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x.val) (Bitvec.ofNat 32 128)) 7).toNat := by
  unfold feltBitAnd
  have h₁ : ∀ {x}, x * (1997537281 : Felt) = x / (128 : Felt) := by
    intros x
    ring_nf
    simp
    left
    rfl
  rw [h₁]
  have h_eq : (Bitvec.ofNat (32 : ℕ) (ZMod.val (128 : Felt))) = oneBitSetVec 32 24 := by
    have h : ZMod.val (128 : Felt) = oneBitSet 7 := by rfl
    rw [h]
    rw [@Bitvec.ofNat_oneBitSet_eq_oneBitSetVec 32 ⟨7, by linarith⟩]
    simp
  rw [h_eq]

  have h := (@oneSetBit_and _ 24 (Bitvec.ofNat (32 : ℕ) (ZMod.val x))) 
  rcases h with h | h
  · rw [h]
    have h_ : (128 : Felt) = (2 ^ 7 : Felt) := by rfl
    rw [h_]
    simp
    rw [←Bitvec.ushr_toNat]
    have h_128 : 128 = ZMod.val (128 : Felt) := rfl
    rw [h_128]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_replicate_false_eq_zero]
    simp
  · rw [h]
    rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    have h_128 : 128 = ZMod.val (128 : Felt) := rfl
    rw [h_128]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    simp
    have h_128 : (2 : Felt) ^ (7 : ℕ) = 128 := rfl
    rw [h_128]
  
lemma leg_64 {x : Felt} :
  feltBitAnd x (64 : Felt) * (1981808641 : Felt) = (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x.val) (Bitvec.ofNat 32 64)) 6).toNat := by
  unfold feltBitAnd
  have h₁ : ∀ {x}, x * (1981808641 : Felt) = x / (64 : Felt) := by
    intros x
    ring_nf
    simp
    left
    rfl
  rw [h₁]
  have h_eq : (Bitvec.ofNat (32 : ℕ) (ZMod.val (64 : Felt))) = oneBitSetVec 32 25 := by
    have h : ZMod.val (64 : Felt) = oneBitSet 6 := by rfl
    rw [h]
    rw [@Bitvec.ofNat_oneBitSet_eq_oneBitSetVec 32 ⟨6, by linarith⟩]
    simp
  rw [h_eq]
  have h := (@oneSetBit_and _ 25 (Bitvec.ofNat (32 : ℕ) (ZMod.val x))) 
  rcases h with h | h
  · rw [h]
    rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_replicate_false_eq_zero]
    have h_64 : 64 = ZMod.val (64 : Felt) := rfl
    rw [h_64]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_replicate_false_eq_zero]
    simp
  · rw [h]
    rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    have h_64 : 64 = ZMod.val (64 : Felt) := rfl
    rw [h_64]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    simp
    have h_64 : (2 : Felt) ^ (6 : ℕ) = 64 := rfl
    rw [h_64]

lemma leg_16 {x : Felt} :
  feltBitAnd x (16 : Felt) * (1887436801 : Felt) = (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x.val) (Bitvec.ofNat 32 16)) 4).toNat := by
  unfold feltBitAnd
  have h₁ : ∀ {x}, x * (1887436801 : Felt) = x / (16 : Felt) := by
    intros x
    ring_nf
    simp
    left
    rfl
  rw [h₁]
  have h_eq : (Bitvec.ofNat (32 : ℕ) (ZMod.val (16 : Felt))) = oneBitSetVec 32 27 := by
    have h : ZMod.val (16 : Felt) = oneBitSet 4 := by rfl
    rw [h]
    rw [@Bitvec.ofNat_oneBitSet_eq_oneBitSetVec 32 ⟨4, by linarith⟩]
    simp
  rw [h_eq]
  have h := (@oneSetBit_and _ 27 (Bitvec.ofNat (32 : ℕ) (ZMod.val x))) 
  rcases h with h | h
  · rw [h]
    rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_replicate_false_eq_zero]
    have h_16 : 16 = ZMod.val (16 : Felt) := rfl
    rw [h_16]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_replicate_false_eq_zero]
    simp
  · rw [h]
    rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    have h_16 : 16 = ZMod.val (16 : Felt) := rfl
    rw [h_16]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    simp
    have h_16 : (2 : Felt) ^ (4 : ℕ) = 16 := rfl
    rw [h_16]

lemma leg_8 {x : Felt} :
  feltBitAnd x (8 : Felt) * (1761607681 : Felt) = (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x.val) (Bitvec.ofNat 32 8)) 3).toNat := by
  unfold feltBitAnd
  have h₁ : ∀ {x}, x * (1761607681 : Felt) = x / (8 : Felt) := by
    intros x
    ring_nf
    simp
    left
    rfl
  rw [h₁]
  have h_eq : (Bitvec.ofNat (32 : ℕ) (ZMod.val (8 : Felt))) = oneBitSetVec 32 28 := by
    have h : ZMod.val (8 : Felt) = oneBitSet 3 := by rfl
    rw [h]
    rw [@Bitvec.ofNat_oneBitSet_eq_oneBitSetVec 32 ⟨3, by linarith⟩]
    simp
  rw [h_eq]
  have h := (@oneSetBit_and _ 28 (Bitvec.ofNat (32 : ℕ) (ZMod.val x))) 
  rcases h with h | h
  · rw [h]
    rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_replicate_false_eq_zero]
    have h_8 : 8 = ZMod.val (8 : Felt) := rfl
    rw [h_8]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_replicate_false_eq_zero]
    simp
  · rw [h]
    rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    have h_8 : 8 = ZMod.val (8 : Felt) := rfl
    rw [h_8]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    simp
    have h_8 : (2 : Felt) ^ (3 : ℕ) = 8 := rfl
    rw [h_8]


lemma leg_96 {x : Felt} :
  feltBitAnd x (96 : Felt) * (1950351361 : Felt) = (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x.val) (Bitvec.ofNat 32 0x60)) 5).toNat := by
  unfold feltBitAnd
  have h₁ : ∀ {x}, x * (1950351361 : Felt) = x / (32 : Felt) := by
    intros x
    ring_nf
    simp
    left
    rfl
  rw [h₁]
  have h_eq : (Bitvec.ofNat (32 : ℕ) (ZMod.val (96 : Felt))) = Bitvec.or (oneBitSetVec 32 26) (oneBitSetVec 32 25) := by
    have h : ZMod.val (96 : Felt) = oneBitSet 5 + oneBitSet 6 := by rfl
    rw [h]
    have h' := @Bitvec.two_bits_set' 32 5 6 (by simp)
    have h'' : (oneBitSet ↑(5 : Fin (32 : ℕ)) + oneBitSet ↑(6 : Fin (32 : ℕ))) = (oneBitSet 5 + oneBitSet 6) := by simp
    rw [←h'', ←h']
    simp
  rw [h_eq]
  have h := (@Bitvec.twoBitSet_and _ 26 25 (Bitvec.ofNat (32 : ℕ) (ZMod.val x))) 
  rcases h with h | h | h | h; rw [h]
  · rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_replicate_false_eq_zero]
    simp
    have h_96 : 96 = ZMod.val (96 : Felt) := rfl
    rw [h_96]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_replicate_false_eq_zero]
    simp
  · rw [h]
    rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    have h_96 : 96 = ZMod.val (96 : Felt) := rfl
    rw [h_96]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    simp
    have h_32 : (2 : Felt) ^ (5 : ℕ) = 32 := rfl
    rw [h_32]
  · rw [h]
    rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    have h_96 : 96 = ZMod.val (96 : Felt) := rfl
    rw [h_96]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    simp
    have h_32 : (2 : Felt) ^ (5 : ℕ) = 32 := rfl
    rw [h_32]
  · rw [h, ←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_twoBitSetVec_eq_oneBitSet (by simp)]
    have h_96 : 96 = ZMod.val (96 : Felt) := rfl
    rw [h_96]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_twoBitSetVec_eq_oneBitSet (by simp)]
    simp
    have h_32 : (2 : Felt) ^ (5 : ℕ) = 32 := rfl
    rw [h_32]

lemma leg_48 {x : Felt} :
  feltBitAnd x (48 : Felt) * (1887436801 : Felt) = (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x.val) (Bitvec.ofNat 32 0x30)) 4).toNat := by
  unfold feltBitAnd
  have h₁ : ∀ {x}, x * (1887436801 : Felt) = x / (16 : Felt) := by
    intros x
    ring_nf
    simp
    left
    rfl
  rw [h₁]
  have h_eq : (Bitvec.ofNat (32 : ℕ) (ZMod.val (48 : Felt))) = Bitvec.or (oneBitSetVec 32 26) (oneBitSetVec 32 27) := by
    have h : ZMod.val (48 : Felt) = oneBitSet 4 + oneBitSet 5 := by rfl
    rw [h]
    have h' := @Bitvec.two_bits_set' 32 4 5 (by simp)
    have h'' : (oneBitSet ↑(4 : Fin (32 : ℕ)) + oneBitSet ↑(5 : Fin (32 : ℕ))) = (oneBitSet 4 + oneBitSet 5) := by simp
    rw [←h'', ←h']
    simp
  rw [h_eq]
  have h := (@Bitvec.twoBitSet_and _ 26 27 (Bitvec.ofNat (32 : ℕ) (ZMod.val x))) 
  rcases h with h | h | h | h; rw [h]
  · rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_replicate_false_eq_zero]
    simp
    have h_48 : 48 = ZMod.val (48 : Felt) := rfl
    rw [h_48]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_replicate_false_eq_zero]
    simp
  · rw [h]
    rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    have h_48 : 48 = ZMod.val (48 : Felt) := rfl
    rw [h_48]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    simp 
    have h_16 : (2 : Felt) ^ (4 : ℕ) = 16 := by simp
    rw [h_16]
  · rw [h]
    rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    have h_48 : 48 = ZMod.val (48 : Felt) := rfl
    rw [h_48]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    simp
    have h_16 : (2 : Felt) ^ (4 : ℕ) = 16 := by simp
    rw [h_16]
  · rw [h, ←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_twoBitSetVec_eq_oneBitSet (by simp)]
    have h_48 : 48 = ZMod.val (48 : Felt) := rfl
    rw [h_48]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_twoBitSetVec_eq_oneBitSet (by simp)]
    simp
    have h_48 : (2 : Felt) ^ (4 : ℕ) = 16 := by simp
    rw [h_48]

lemma leg_6 {x : Felt} :
  feltBitAnd x (6 : Felt) * (1006632961 : Felt) = (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x.val) (Bitvec.ofNat 32 0x06)) 1).toNat := by
  unfold feltBitAnd
  have h₁ : ∀ {x}, x * (1006632961 : Felt) = x / (2 : Felt) := by
    intros x
    ring_nf
    simp
    left
    rfl
  rw [h₁]
  have h_eq : (Bitvec.ofNat (32 : ℕ) (ZMod.val (6 : Felt))) = Bitvec.or (oneBitSetVec 32 30) (oneBitSetVec 32 29) := by
    have h : ZMod.val (6 : Felt) = oneBitSet 1 + oneBitSet 2 := by rfl
    rw [h]
    have h' := @Bitvec.two_bits_set' 32 1 2 (by simp)
    have h'' : (oneBitSet ↑(1 : Fin (32 : ℕ)) + oneBitSet ↑(2 : Fin (32 : ℕ))) = (oneBitSet 1 + oneBitSet 2) := by simp
    rw [←h'', ←h']
    simp
  rw [h_eq]
  have h := (@Bitvec.twoBitSet_and _ 30 29 (Bitvec.ofNat (32 : ℕ) (ZMod.val x))) 
  rcases h with h | h | h | h; rw [h]
  · rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_replicate_false_eq_zero]
    simp
    have h_6 : 6 = ZMod.val (6 : Felt) := rfl
    rw [h_6]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_replicate_false_eq_zero]
    simp
  · rw [h]
    rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    have h_6 : 6 = ZMod.val (6 : Felt) := rfl
    rw [h_6]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    simp 
  · rw [h]
    rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    have h_6 : 6 = ZMod.val (6 : Felt) := rfl
    rw [h_6]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    simp
  · rw [h, ←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_twoBitSetVec_eq_oneBitSet (by simp)]
    have h_6 : 6 = ZMod.val (6 : Felt) := rfl
    rw [h_6]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_twoBitSetVec_eq_oneBitSet (by simp)]
    simp

lemma leg_12 {x : Felt} :
  feltBitAnd x (12 : Felt) * (1509949441 : Felt) = (Bitvec.ushr (Bitvec.and (Bitvec.ofNat 32 x.val) (Bitvec.ofNat 32 0x0C)) 2).toNat := by
  unfold feltBitAnd
  have h₁ : ∀ {x}, x * (1509949441 : Felt) = x / (4 : Felt) := by
    intros x
    ring_nf
    simp
    left
    rfl
  rw [h₁]
  have h_eq : (Bitvec.ofNat (32 : ℕ) (ZMod.val (12 : Felt))) = Bitvec.or (oneBitSetVec 32 29) (oneBitSetVec 32 28) := by
    have h : ZMod.val (12 : Felt) = oneBitSet 2 + oneBitSet 3 := by rfl
    rw [h]
    have h' := @Bitvec.two_bits_set' 32 2 3 (by simp)
    have h'' : (oneBitSet ↑(2 : Fin (32 : ℕ)) + oneBitSet ↑(3 : Fin (32 : ℕ))) = (oneBitSet 2 + oneBitSet 3) := by simp
    rw [←h'', ←h']
    simp
  rw [h_eq]
  have h := (@Bitvec.twoBitSet_and _ 29 28 (Bitvec.ofNat (32 : ℕ) (ZMod.val x))) 
  rcases h with h | h | h | h; rw [h]
  · rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_replicate_false_eq_zero]
    simp
    have h_12 : 12 = ZMod.val (12 : Felt) := rfl
    rw [h_12]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_replicate_false_eq_zero]
    simp
  · rw [h]
    rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    have h_12 : 12 = ZMod.val (12 : Felt) := rfl
    rw [h_12]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    simp 
    have h_4 : (2 : Felt) ^ (2 : ℕ) = 4 := by simp
    rw [h_4]
  · rw [h]
    rw [←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    have h_12 : 12 = ZMod.val (12 : Felt) := rfl
    rw [h_12]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_oneBitSetVec_eq_oneBitSet]
    simp
    have h_4 : (2 : Felt) ^ (2 : ℕ) = 4 := by simp
    rw [h_4]
  · rw [h, ←Bitvec.ushr_toNat]
    rw [Bitvec.toNat_twoBitSetVec_eq_oneBitSet (by simp)]
    have h_12 : 12 = ZMod.val (12 : Felt) := rfl
    rw [h_12]
    rw [h_eq]
    rw [h]
    rw [Bitvec.toNat_twoBitSetVec_eq_oneBitSet (by simp)]
    simp
    have h_4 : (2 : Felt) ^ (2 : ℕ) = 4 := by simp
    rw [h_4]


theorem decoder_closed_form_entails_spec : 
  some (feltBitAnd x3 (6 : Felt) * (1006632961 : Felt)) = y0 ∧
      some (feltBitAnd x3 (96 : Felt) * (1950351361 : Felt)) = y1 ∧
        some (feltBitAnd x2 (96 : Felt) * (1950351361 : Felt)) = y2 ∧
          some (feltBitAnd x2 (3 : Felt)) = y3 ∧
            some (feltBitAnd x2 (12 : Felt) * (1509949441 : Felt)) = y4 ∧
              some (feltBitAnd x1 (48 : Felt) * (1887436801 : Felt)) = y5 ∧
                some (feltBitAnd x1 (3 : Felt)) = y6 ∧
                  some (feltBitAnd x1 (12 : Felt) * (1509949441 : Felt)) = y7 ∧
                    some (feltBitAnd x3 (8 : Felt) * (1761607681 : Felt)) = y8 ∧
                      some (feltBitAnd x3 (16 : Felt) * (1887436801 : Felt)) = y9 ∧
                        some (feltBitAnd x3 (128 : Felt) * (1997537281 : Felt)) = y10 ∧
                          some (feltBitAnd x2 (16 : Felt) * (1887436801 : Felt)) = y11 ∧
                            some (feltBitAnd x2 (128 : Felt) * (1997537281 : Felt)) = y12 ∧
                              some (feltBitAnd x3 (1 : Felt)) = y13 ∧
                                some (feltBitAnd x1 (128 : Felt) * (1997537281 : Felt)) = y14 ∧
                                  some (feltBitAnd x1 (64 : Felt) * (1981808641 : Felt)) = y15 ∧
                                    some (feltBitAnd x0 (128 : Felt) * (1997537281 : Felt)) = y16 ∧
                                      some (feltBitAnd x0 (127 : Felt)) = y17 ↔ 
  decoder_direct_spec [x0, x1, x2, x3] [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17] := by
  rw [leg_6, leg_8, leg_12, leg_12, leg_16, leg_16, leg_48, leg_64, leg_96, leg_96, leg_128, leg_128, leg_128, leg_128]
  unfold decoder_direct_spec Instruction.fromWords feltBitAnd
  have h' :(ZMod.val (1 : Felt)) = 1 := by simp
  simp [h']
  have h' :(ZMod.val (3 : Felt)) = 3 := by simp
  simp [h']
  have h' :(ZMod.val (127 : Felt)) = 127 := by simp
  simp [h']
  aesop