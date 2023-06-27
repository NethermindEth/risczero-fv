import Risc0.Basic

open Risc0

def ith_hot (n : ℕ) (i : ℕ) : BufferAtTime :=
  ((List.range n).map (Nat.cast ∘ Bool.toNat ∘ (Nat.beq i))).map some

def one_hot_spec (n : ℕ) (input : Felt) (output: BufferAtTime) := 
  ∃ (i : ℕ), i < n ∧ input = i ∧ output = ith_hot n i