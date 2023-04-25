-- This file contains the MLIR program labeled `ORIGINAL` in the `nonzero-example` output.
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Is0.Basic
import Is0.Lemmas

namespace Risc0

lemma one_sub_z {z : Felt} : 1 - z = 0 ↔ z = 1 := by
  apply Iff.intro
  · rw [← @add_left_inj _ _ _ z (1 - z) 0]
    simp
    intros hg
    rw [← hg]
  · intros hg
    rw [hg]
    decide

lemma ending {x y₁ y₂ : Felt} :
  (if x = 0 then 1 else 0) = y₁ ∧ (if x = 0 then 0 else x⁻¹) = y₂ ↔
    List.foldr And True
      (List.map (fun e => e = 0)
        (if y₁ = 0 then if 1 - y₁ = 0 then [] else [x * y₂ - 1] else if 1 - y₁ = 0 then [x] else [x * y₂ - 1, x])) := by
  by_cases hx : x = 0
  · rw [hx]
    by_cases hy₁ : y₁ = 0
    · rw [hy₁]
      by_cases hy₂ : y₂ = 0
      · rw [hy₂]
        simp only [List.foldr, and_true]
      · simp only [inv_zero, ite_self, false_and, List.foldr, zero_mul, zero_sub, neg_eq_zero, and_true]
    · rw [if_neg hy₁]
      by_cases hy₂ : y₂ = 0
      · rw [hy₂]
        simp only [ite_true, and_true, mul_zero, zero_sub]
        apply Iff.intro
        · intros h
          rw [← h]
          simp only [List.foldr, and_self]
        · simp [one_sub_z]
          by_cases hy1 : y₁ = 1
          · rw [hy1]
            simp only [List.foldr, and_self, forall_true_left]
          · rw [if_neg hy1]
            simp only [List.foldr, and_self, and_true, IsEmpty.forall_iff]
      · simp only [ite_true, inv_zero, ite_self, zero_mul, zero_sub]
        simp [one_sub_z]
        sorry
  · rw [if_neg hx]
    by_cases hy₁ : y₁ = 0
    · rw [hy₁]
      by_cases hy₂ : y₂ = 0
      · rw [hy₂]
        sorry
      · sorry
    · rw [if_neg hy₁]
      by_cases hy₂ : y₂ = 0
      · rw [hy₂]
        sorry
      · sorry

end Risc0
