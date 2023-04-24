import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Is0.Basic
import Is0.Lemmas
import Is0.Programs

namespace Risc0

theorem is0OriginalProgram_constraints_are_what_we_expect :
  ∀ x y z : Felt, (is0OriginalProgram x y z).1.constraints.foldr And _root_.True ↔ (if x == 0 then x = 0 else x * x⁻¹ - 1 = 0) := by
  intros x y z
  unfold is0OriginalProgram
  by_cases x = 0
  rw [h]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [List.foldr, and_self]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq, ne_eq]
  unfold Op.eval ; simp only
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq, ne_eq]
  unfold Op.eval ; simp only
  unfold List.getD ; unfold List.get? ; unfold Option.getD ; simp only
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq, ne_eq]
  unfold Op.eval ; simp only
  simp only [beq_iff_eq, ne_eq]
  rw [if_neg h]
  rw [if_neg h]
  rw [Cirgen.step_Sequence_Set_collapsible [y, z] 0]
  simp only [Map.update, beq_iff_eq, ne_eq]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.update, beq_iff_eq, ne_eq]
  unfold Op.eval ; simp only
  unfold List.set
  simp only [beq_iff_eq, ne_eq]
  rw [if_neg h]
  rw [Cirgen.step_Sequence_Set_collapsible [0, z] x⁻¹]
  simp only [Map.update, beq_iff_eq, List.set_succ, and_true, ne_eq]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq, and_true, ne_eq]
  unfold Op.eval ; simp only
  unfold List.getD ; unfold List.get? ; unfold Option.getD ; simp only
  rw [Cirgen.step_Sequence_If_collapsible 0]
  unfold List.set
  simp only [and_true, ne_eq]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  unfold Op.eval ; simp only
  simp only [State.update, Map.update, beq_iff_eq, sub_zero, and_true, ne_eq]
  rw [ite_true]
  rw [Cirgen.step_If_collapsible 1]
  simp only [List.foldr, and_true, ne_eq]
  nth_rewrite 1 [Op.assign]
  nth_rewrite 1 [Op.eval]
  simp only [Map.update, ite_true, Option.some.injEq, ne_eq]
  nth_rewrite 1 [Op.assign]
  nth_rewrite 1 [Op.eval]
  simp only [ite_true, ite_false, List.getD_cons_succ, List.getD_cons_zero, Map.update, beq_iff_eq, Option.some.injEq, ne_eq]
  nth_rewrite 1 [Op.assign]
  nth_rewrite 1 [Op.eval]
  simp only [ite_true, ite_false, List.getD_cons_succ, List.getD_cons_zero, Map.update, beq_iff_eq, ne_eq, Option.some.injEq]
  nth_rewrite 1 [Op.assign]
  nth_rewrite 1 [Op.eval]
  simp only [ne_eq, Map.update, ite_false, Option.some.injEq]
  nth_rewrite 1 [Op.assign]
  nth_rewrite 1 [Op.eval]
  simp only [ne_eq, ite_true, ite_false, List.getD_cons_succ, List.getD_cons_zero, Map.update, beq_iff_eq, ite_self]
  simp only [ite_false, ite_true]
  simp only [ite_false, ite_true]
  apply @hab x y z
  rw [Cirgen.step_Eqz_collapsible x]
  simp only [ne_eq, Prod.mk.injEq, State.mk.injEq, and_false, and_true, not_false_iff]
  simp only [ite_false, ite_true]
  simp only [ite_false, ite_true]
  simp only [ite_false, ite_true]
  simp only [ite_false, ite_true]
  simp only [ite_false, ite_true]

end Risc0
