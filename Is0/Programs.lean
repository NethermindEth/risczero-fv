-- This file contains the MLIR program labeled `ORIGINAL` in the `nonzero-example` output.
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Is0.Basic
import Is0.Lemmas

namespace Risc0

open MLIRNotation in
def is0_witness (input : List Felt) : List Felt :=
  let state' :=
    MLIR.run { felts := Map.empty
             , props := Map.empty
             , input := input
             , output := [42, 42]
             , constraints := []
             } <|
    "x"         ←ₐ input[0];
    "isZeroBit" ←ₐ ??₀⟨"x"⟩;
    output[0]   ←ₐ ⟨"isZeroBit"⟩;
    "invVal"    ←ₐ Inv ⟨"x"⟩;
    output[1]   ←ₐ ⟨"invVal"⟩
  state'.output

open MLIRNotation in
def is0_constraints (input : List Felt) (output : List Felt) : Prop :=
  let state' :=
    MLIR.run { felts := Map.empty
             , props := Map.empty
             , input := input
             , output := output
             , constraints := []
             } <|
    "1"         ←ₐ 1;
    "x"         ←ₐ input[0];
    "out[0]"    ←ₐ output[0];
    guard ⟨"out[0]"⟩ then
      ?₀⟨"x"⟩;
    "1 - out[0]" ←ₐ ⟨"1"⟩ - ⟨"out[0]"⟩;
    guard ⟨"1 - out[0]"⟩ then (
      "out[1]"         ←ₐ output[1];
      "x * out[1]"     ←ₐ ⟨"x"⟩ * ⟨"out[1]"⟩;
      "x * out[1] - 1" ←ₐ ⟨"x * out[1]"⟩ - ⟨"1"⟩;
      ?₀ ⟨"x * out[1] - 1"⟩
    )
  (List.foldr And True) $ List.map (λ e ↦ e = 0) state'.constraints

theorem is0_original_nondet_iff_constraints : ∀ input output : List Felt,
    (input.length = 1 ∧ output.length = 2)
  → (is0_witness input = output ↔ is0_constraints input output) := by
  intros input output h
  have hin := h.1
  have hout := h.2
  clear h
  have h : List.length input > 0 := by rw [hin] ; decide
  have h₁ := List.exists_cons_of_ne_nil (List.length_pos_iff_ne_nil.1 h)
  have ⟨x, ⟨xs, hx⟩⟩ := h₁ 
  rw [hx]
  clear hx h₁ h
  have h : List.length output > 0 := by rw [hout] ; decide
  have h₁ := List.exists_cons_of_ne_nil (List.length_pos_iff_ne_nil.1 h)
  have ⟨y₁, ⟨ys', hy⟩⟩ := h₁
  clear h₁ h
  have h₂ : ∀ (z : Felt) (zs : List Felt), List.length (z :: zs) = 2 → List.length zs = 1 := by
    exact fun z zs a => (fun {n m} => Nat.succ_inj'.mp) a
  have h₃ : List.length (y₁ :: ys') = 2 := by
    rw [hy] at hout
    exact hout
  have h₄ := h₂ y₁ ys' h₃
  have h : List.length ys' > 0 := by rw [h₄] ; decide
  have h₁ := List.exists_cons_of_ne_nil (List.length_pos_iff_ne_nil.1 h)
  have ⟨y₂, ⟨ys, hy'⟩⟩ := h₁
  rw [hy'] at hy
  clear hy' h h₁ h₂ h₃ h₄
  rw [hy]
  rw [hy] at hout
  rw [List.length_cons, List.length_cons, Nat.succ_inj', Nat.succ_inj'] at hout
  have hys := List.eq_nil_of_length_eq_zero hout
  unfold is0_witness
  rw [MLIR.run_Sequence_Assign_collapsible]
  unfold Op.eval
  simp only [State.update, Map.update, beq_iff_eq, List.getD_cons_zero, Map.empty]
  rw [MLIR.run_Sequence_Assign_collapsible]
  unfold Op.eval
  simp only [State.update, ite_true, beq_iff_eq, Map.update]
  rw [MLIR.run_Sequence_Set_collapsible (if x = 0 then 1 else 0)]
  simp only
  rw [MLIR.run_Sequence_Assign_collapsible]
  unfold Op.eval
  simp only [State.update, ite_true, ite_false, beq_iff_eq, Map.update]
  unfold MLIR.run
  simp only [ite_false, ite_true]
  unfold List.set
  unfold List.set
  simp only
  unfold is0_constraints
  rw [MLIR.run_Sequence_Assign_collapsible]
  unfold Op.eval
  simp only [State.update, Map.update, beq_iff_eq, List.getD_cons_zero, Map.empty]
  rw [MLIR.run_Sequence_Assign_collapsible]
  unfold Op.eval
  simp only [State.update, Map.update, beq_iff_eq, List.getD_cons_zero, Map.empty]
  rw [MLIR.run_Sequence_Assign_collapsible]
  unfold Op.eval
  simp only [State.update, Map.update, beq_iff_eq, Nat.cast_one]
  unfold List.getD ; unfold Option.getD ; unfold List.get?
  simp only [List.cons.injEq]
  rw [MLIR.run_Sequence_If_collapsible y₁]
  simp only [beq_iff_eq]
  by_cases y₁ = 0
  rw [h]
  simp only [ite_eq_right_iff, List.foldr]
  unfold MLIR.run
  simp only
  unfold Op.assign
  unfold Op.eval
  simp only [Map.update, ite_true, ite_false, Option.some.injEq]
  unfold MLIR.run
  unfold Op.assign
  unfold Op.eval
  simp only [Map.update, ite_false, ite_true, Option.some.injEq, forall_apply_eq_imp_iff']
  unfold MLIR.run
  unfold Op.assign
  unfold Op.eval
  simp only [Map.update, ite_true, ite_false, sub_zero, List.getD_cons_succ, List.getD_cons_zero, ite_self]
  by_cases x = 0
  rw [h]
  simp only [inv_zero, ite_self, false_and, zero_mul, zero_sub, neg_eq_zero]
  rw [←ite_not]
  have x_inv_ne_zero := inv_ne_zero h
  rw [(@Ne.ite_eq_left_iff Felt (¬x = 0) _ x⁻¹ 0 x_inv_ne_zero).2 h]
  rw [hys]
  simp only [and_true]
  have haa : ∀ x : Felt, x = 0 → False ↔ ¬x = 0 := by exact fun x => iff_of_eq rfl
  rw [haa]
  have ht := iff_true (¬x = 0)
  have h' := h
  rw [← ht] at h
  rw [h]
  simp only [true_and]
  conv =>
    rhs
    rw [← Fin.succ_inj]
  by_cases y₂ = 0
  rw [h]
  simp only [inv_eq_zero, mul_zero, zero_sub, Fin.succ_inj, iff_false]
  exact h'
  -- rw [Fin.succ_pred (x * y₂)]
  { 
    simp 
    apply Iff.intro
    intro h_inv
    rw [←h_inv]
    rw [mul_inv_cancel]
    ring_nf
    exact h'
    intro h_minus_1
    rw [←mul_inv_cancel h', ←mul_sub] at h_minus_1
    rw [
      ←sub_left_inj, 
      sub_self x⁻¹, 
      ←one_mul (y₂ - x⁻¹), 
      ←mul_inv_cancel h',
      mul_comm x,
      mul_assoc,
      h_minus_1]
    simp
  }
  {
    rw [List.foldr_map]
    apply Iff.intro
    rintro ⟨h_if₁, h_if₂, h_if₃⟩ 
    rw [←h_if₃]
    have h' := h
    by_cases (x = 0)
    rw [h] at h_if₁
    simp at h_if₁
    rw [←h_if₁]
    simp
    exact h
    have hf := iff_false (x = 0)
    rw [←hf] at h
    simp at h_if₁
    exfalso
    apply h'
    rw [←h_if₁]
    simp
    exact h.1
    intro h_comp
    apply And.intro
    have h' := h
    by_cases (x = 0)
    rw [h]
    unfold List.foldr at h_comp
    -- simp only [State.update, Map.update, beq_iff_eq, List.getD_cons_zero, Map.empty] at h_comp
    -- rw [MLIR.run_Sequence_Assign_collapsible] at h_comp
    -- simp at h_comp
    -- unfold Op.eval at h_comp
    -- simp at h_comp
    -- unfold MLIR.run at h_comp
    -- simp at h_comp
    -- rw [MLIR.run_Sequence_Assign_collapsible] at h_comp
    -- unfold Op.eval at h_comp
    -- simp at h_comp
    -- rw [MLIR.run_Sequence_Assign_collapsible] at h_comp
    -- unfold Op.eval at h_comp
    -- simp at h_comp
    -- rw [MLIR.run_Sequence_Assign_collapsible] at h_comp
    -- unfold Op.eval at h_comp
    -- simp at h_comp
    -- rw [MLIR.run_Sequence_Assign_collapsible] at h_comp
    -- unfold Op.eval at h_comp
    -- simp at h_comp
    -- rw [MLIR.run_Eqz_collapsible] at h_comp
    -- simp at h_comp
    -- unfold Op.assign at h_comp

  }
  sorry
  sorry

end Risc0
