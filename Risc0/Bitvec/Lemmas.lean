/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Risc0.Bitvec.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

-- All credit to: https://github.com/leanprover-community/mathlib4/blob/ab52fda385ddaebb1db141149631dbcc08f69e26/Mathlib/Data/Bitvec/Lemmas.lean
-- Small changes only.

open Mathlib

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors and their coercions to
`Nat` and `Fin`.
-/
namespace Bitvec

open Nat

theorem bitsToNat_toList {n : ℕ} (x : Bitvec n) : Bitvec.toNat x = bitsToNat (Vector.toList x) :=
  rfl


attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

attribute [local simp] Nat.zero_add Nat.add_zero Nat.one_mul Nat.mul_one Nat.zero_mul Nat.mul_zero

local infixl:65 "++ₜ" => Vector.append

-- mul_left_comm
theorem toNat_append {m : ℕ} (xs : Bitvec m) (b : Bool) :
    Bitvec.toNat (xs++ₜb ::ᵥ Vector.nil) =
      Bitvec.toNat xs * 2 + Bitvec.toNat (b ::ᵥ Vector.nil) := by
  cases' xs with xs P
  simp [bitsToNat_toList]; clear P
  unfold bitsToNat
  -- porting note: was `unfold List.foldl`, which now unfolds to an ugly match
  rw [List.foldl, List.foldl]
  -- generalize the accumulator of foldl
  generalize h : 0 = x
  conv in addLsb x b =>
    rw [← h]
  clear h
  simp
  induction' xs with x xs xs_ih generalizing x
  · simp
    unfold addLsb
    simp [Nat.mul_succ]
  · simp
    apply xs_ih


-- Porting Note: the mathlib3port version of the proof was :
--  simp [bits_to_nat_to_list]
--  unfold bits_to_nat add_lsb List.foldl cond
--  simp [cond_to_bool_mod_two]
theorem bits_toNat_decide (n : ℕ) : Bitvec.toNat (decide (n % 2 = 1) ::ᵥ Vector.nil) = n % 2 := by
  simp [bitsToNat_toList]
  unfold bitsToNat addLsb List.foldl
  simp [Nat.cond_decide_mod_two]


theorem ofNat_succ {k n : ℕ} :
    Bitvec.ofNat k.succ n = Bitvec.ofNat k (n / 2)++ₜdecide (n % 2 = 1) ::ᵥ Vector.nil :=
  rfl

/--
I am sorry, I did a 'follow my nose' proof in 3 minutes.
-/
theorem toNat_ofNat {k n : ℕ} : Bitvec.toNat (Bitvec.ofNat k n) = n % 2 ^ k := by
  induction' k with k ih generalizing n
  · simp [Nat.mod_one]
    rfl
  · rw [ofNat_succ, toNat_append, ih, bits_toNat_decide, Nat.mod_pow_succ, Nat.mul_comm]; clear ih
    generalize eq : 2^k = x; clear eq
    rw [add_comm]
    clear k
    have : 2 * (x * (n / 2 / x)) = x * (2 * (n / x / 2)) := by
      rw [Nat.div_div_eq_div_mul]
      rw [Nat.div_div_eq_div_mul]
      rw [←Nat.mul_assoc]
      rw [←Nat.mul_assoc]
      ring_nf
    rw [Nat.mod_def (k := x)]
    rw [Nat.mod_def (m := n / x)]
    rw [Nat.mod_def]
    rw [Nat.mod_def]
    rw [Nat.mul_sub]
    rw [Nat.mul_sub]
    rw [←Nat.add_sub_assoc]
    rw [←Nat.add_sub_assoc]
    rw [Nat.sub_add_cancel]
    rw [Nat.sub_add_cancel]
    rw [this]
    apply Nat.mul_div_le
    apply Nat.mul_div_le
    apply Nat.mul_le_mul_left
    omega
    rw [←Nat.mul_assoc]
    rw [Nat.div_div_eq_div_mul]
    field_simp
    rw [←Nat.div_div_eq_div_mul]
    rw [←this]
    apply Nat.mul_le_mul_left
    exact mul_div_le (n / 2) x

theorem ofFin_val {n : ℕ} (i : Fin <| 2 ^ n) : (ofFin i).toNat = i.val := by
  rw [ofFin, toNat_ofNat, Nat.mod_eq_of_lt]
  apply i.is_lt


theorem addLsb_eq_twice_add_one {x b} : addLsb x b = 2 * x + cond b 1 0 := by
  simp [addLsb, two_mul]


theorem toNat_eq_foldr_reverse {n : ℕ} (v : Bitvec n) :
    v.toNat = v.toList.reverse.foldr (flip addLsb) 0 := by rw [List.foldr_reverse]; rfl


theorem toNat_lt {n : ℕ} (v : Bitvec n) : v.toNat < 2 ^ n := by
  suffices : v.toNat + 1 ≤ 2 ^ n; simpa
  rw [toNat_eq_foldr_reverse]
  cases' v with xs h
  dsimp [Bitvec.toNat, bitsToNat]
  rw [← List.length_reverse] at h
  generalize xs.reverse = ys at h
  induction' ys with head tail ih generalizing n
  · simp [← h]
  · simp only [← h, pow_add, flip, List.length, List.foldr, pow_one]
    rw [addLsb_eq_twice_add_one]
    trans 2 * List.foldr (fun (x : Bool) (y : ℕ) => addLsb y x) 0 tail + 2 * 1
    · rw [add_assoc]
      apply Nat.add_le_add_left
      cases head <;> simp
    · rw [← left_distrib]
      rw [mul_comm _ 2]
      apply Nat.mul_le_mul_left
      exact ih rfl


theorem addLsb_div_two {x b} : addLsb x b / 2 = x := by
  cases b <;>
      simp only [Nat.add_mul_div_left, addLsb, ← two_mul, add_comm, Nat.succ_pos',
        Nat.mul_div_right, gt_iff_lt, zero_add, cond]
  norm_num
  omega

theorem decide_addLsb_mod_two {x b} : decide (addLsb x b % 2 = 1) = b := by
  cases b <;>
      simp only [Bool.decide_iff, Nat.add_mul_mod_self_left, addLsb, ← two_mul, add_comm,
        decide_false_eq_false, Nat.mul_mod_right, zero_add, cond, zero_ne_one]
  rfl

theorem ofNat_toNat {n : ℕ} (v : Bitvec n) : Bitvec.ofNat n v.toNat = v := by
  cases' v with xs h
  -- Porting note: was `ext1`, but that now applies `Vector.ext` rather than `Subtype.ext`.
  apply Subtype.ext
  change Vector.toList _ = xs
  dsimp [Bitvec.toNat, bitsToNat]
  rw [← List.length_reverse] at h
  rw [← List.reverse_reverse xs, List.foldl_reverse]
  generalize xs.reverse = ys at h ⊢; clear xs
  induction' ys with ys_head ys_tail ys_ih generalizing n
  · cases h
    simp [Bitvec.ofNat]
  · simp only [← Nat.succ_eq_add_one, List.length] at h
    subst n
    simp only [Bitvec.ofNat, Vector.toList_cons, Vector.toList_nil, List.reverse_cons,
      Vector.toList_append, List.foldr]
    erw [addLsb_div_two, decide_addLsb_mod_two]
    congr
    apply ys_ih
    rfl

theorem toFin_val {n : ℕ} (v : Bitvec n) : (toFin v : ℕ) = v.toNat := by
  dsimp [toFin, Fin.val]
  rw [Nat.mod_eq_of_lt]
  exact toNat_lt _

theorem toFin_le_toFin_of_le {n} {v₀ v₁ : Bitvec n} (h : v₀ ≤ v₁) : v₀.toFin ≤ v₁.toFin :=
  show (v₀.toFin : ℕ) ≤ v₁.toFin by
    rw [toFin_val, toFin_val]
    exact h


theorem ofFin_le_ofFin_of_le {n : ℕ} {i j : Fin (2 ^ n)} (h : i ≤ j) : ofFin i ≤ ofFin j :=
  show (Bitvec.ofNat n i).toNat ≤ (Bitvec.ofNat n j).toNat by
    simp only [toNat_ofNat, Nat.mod_eq_of_lt, Fin.is_lt]
    exact h


theorem toFin_ofFin {n} (i : Fin <| 2 ^ n) : (ofFin i).toFin = i :=
  Fin.eq_of_val_eq (by simp [toFin_val, ofFin, toNat_ofNat, Nat.mod_eq_of_lt, i.is_lt])


theorem ofFin_toFin {n} (v : Bitvec n) : ofFin (toFin v) = v := by
  dsimp [ofFin]
  rw [toFin_val, ofNat_toNat]


end Bitvec
