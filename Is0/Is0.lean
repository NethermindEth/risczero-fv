import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Is0.Basic
import Is0.Lemmas
import Is0.Programs

namespace Risc0

-- Looks like we need to give `y` and `z` some meaning in this case.
theorem is0ConstraintsProgram_constraints_are_what_we_expect {result : Prop} :
  ∀ x y z : Felt, (is0ConstraintsProgram x y z).2 = some (if x == 0 then x = 0 else x * x⁻¹ - 1 = 0) := by
  intros x y z
  unfold is0ConstraintsProgram
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
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq, ne_eq]
  unfold Op.eval ; simp only
  simp only [beq_iff_eq, ite_self]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq, ne_eq]
  unfold Op.eval ; simp only
  simp only [beq_iff_eq, ite_self]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq, ne_eq]
  unfold Op.eval ; simp only
  simp only [beq_iff_eq, ite_self]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq, ne_eq]
  unfold Op.eval ; simp only
  simp only [beq_iff_eq, ite_self]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq, ne_eq]
  unfold List.getD ; unfold Option.getD ; unfold List.get? ; unfold List.get?; simp only
  unfold Op.eval ; simp only
  simp only [beq_iff_eq, ite_self]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq, ne_eq]
  unfold Op.eval ; simp only
  simp only [beq_iff_eq, ite_self]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.empty, Map.fromList, Map.update, beq_iff_eq, ne_eq]
  unfold Op.eval ; simp only
  simp only [beq_iff_eq, ite_self]
  unfold Cirgen.step
  nth_rewrite 1 [Cirgen.step]
  nth_rewrite 1 [Op.assign]
  nth_rewrite 1 [Op.eval]
  simp only [zero_mul, zero_sub, neg_eq_zero, and_false, ite_false, ite_true, beq_iff_eq, Map.update]
  nth_rewrite 1 [Cirgen.step]
  simp only [ite_false, ite_true, Option.some.injEq, ite_eq_left_iff]
  sorry
  sorry

end Risc0
