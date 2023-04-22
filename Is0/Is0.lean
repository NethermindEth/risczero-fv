import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Is0.Basic
import Is0.Programs

namespace Risc0

lemma Cirgen.step_Sequence_Assign_collapsible :
  ∀ (state : State) (name : String) (op : Op) (program : Cirgen),
  Cirgen.step state (.Sequence (.Assign name op) program) = Cirgen.step (state.update name (Op.eval state op)) program := by
  intros state name op program
  cases op <;> {
    conv =>
      lhs
      unfold Cirgen.step
      simp only [State.update, Map.update, beq_iff_eq]
  }

lemma Cirgen.step_Sequence_Set_collapsible
    {state : State}
    {name : String}
    {nameₓ : String}
    {program : Cirgen}
    (buffer : List Felt)
    (x : Felt)
    (h : state.buffers name = some buffer)
    (h₁ : state.felts nameₓ = some x) :
    Cirgen.step state (.Sequence (.Set (Variable.mk name) i (Variable.mk nameₓ)) program)
  = let buffers' := state.buffers.update name (buffer.set i x)
    Cirgen.step ({ state with buffers := buffers' }) program := by
  conv =>
    lhs
    unfold step
  unfold step
  simp only [Map.update, beq_iff_eq]
  rw [h]
  rw [h₁]
  done

lemma Cirgen.step_Sequence_If_collapsible
    {state : State}
    {name : String}
    {branch : Cirgen}
    {program : Cirgen}
    (x : Felt)
    (h₁ : state.felts name = some x)
    (hab : step state program ≠ step state (Sequence branch program))
    (hhh : (state, none) ≠ step state branch) :
    Cirgen.step state (.Sequence (.If (Variable.mk name) branch) program)
  = if (x == 0)
      then Cirgen.step state program
      else Cirgen.step state (.Sequence branch program) := by
  simp only [beq_iff_eq]
  let a := step state program
  let b := step state (Sequence branch program)
  have ha : a = step state program := by simp only
  have hb : b = step state (Sequence branch program) := by simp only
  rw [← ha]
  rw [← hb]
  by_cases x = 0
  have hh := (@Ne.ite_eq_left_iff (State × Option Prop) (x = 0) _ a b hab).2 h
  rw [hh]
  conv =>
    lhs
    unfold step
    unfold step
  simp only [beq_iff_eq, Map.update]
  rw [h₁]
  simp only
  have hh₁ := (@Ne.ite_eq_left_iff (State × Option Prop) (x = 0) _ (state, none) (step state branch) hhh).2 h
  rw [hh₁]
  simp only
  conv =>
    rhs
    unfold step
  simp only [beq_iff_eq, Map.update]
  rw [←ite_not]
  have hba : b ≠ a := by
    rw [ha]
    rw [hb]
    rw [ne_comm]
    exact hab
  have hh := (@Ne.ite_eq_left_iff (State × Option Prop) (¬x = 0) _ b a hba).2 h
  rw [hh]
  conv =>
    lhs
    unfold step
    unfold step
  simp only [beq_iff_eq, Map.update]
  rw [h₁]
  simp only
  rw [←ite_not]
  have hhhh : step state branch ≠ (state, none) := by
    rw [ne_comm]
    exact hhh
  have hh₁ := (@Ne.ite_eq_left_iff (State × Option Prop) (¬x = 0) _ (step state branch) (state, none) hhhh).2 h
  rw [hh₁]
  simp only
  conv =>
    rhs
    unfold step
  simp only [beq_iff_eq, Map.update]
  conv in (step (step state branch).fst program) =>
    unfold step
  simp only [beq_iff_eq, Map.update]

lemma Cirgen.step_If_collapsible
    {state : State}
    {name : String}
    {branch : Cirgen}
    (x : Felt)
    (h₁ : state.felts name = some x) :
    Cirgen.step state (.If (Variable.mk name) branch)
  = if (x == 0)
      then (state, none)
      else Cirgen.step state branch := by
  sorry

theorem is0OriginalProgram_constraints_are_what_we_expect :
  ∀ x y z : Felt, (is0OriginalProgram x y z).1.constraints.foldr And _root_.True ↔ (x = 0 ∧ x * x⁻¹ - 1 = 0) := by
  intros x y z
  unfold is0OriginalProgram
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq]
  unfold Op.eval
  simp only
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq]
  unfold Op.eval
  simp only
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq]
  unfold Op.eval
  simp only [List.getD_cons_zero, ite_false, ite_true, beq_iff_eq, ne_eq]
  rw [Cirgen.step_Sequence_Set_collapsible [y, z] (if x = 0 then 1 else 0)]
  simp only
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq]
  unfold Op.eval
  simp only
  rw [Cirgen.step_Sequence_Set_collapsible [y, z] (if (x == 0) = true then 0 else x⁻¹)]
  simp only [beq_iff_eq, Map.update, List.set_succ, ne_eq]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq]
  unfold Op.eval
  simp only [ite_true, ite_false, List.getD_cons_zero, ne_eq]
  rw [Cirgen.step_Sequence_If_collapsible y]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq]
  unfold Op.eval
  simp only
  rw [Cirgen.step_If_collapsible (1 - y)]
  simp only [beq_iff_eq, ne_eq]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq]
  unfold Op.eval
  simp only
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq]
  unfold Op.eval
  simp only
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq]
  unfold Op.eval
  simp only
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry

end Risc0
