import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Is0.Basic
import Is0.Programs

namespace Risc0

lemma step_of_sequence_of_assign_eq_state_change :
  ∀ (state : State) (name : String) (op : Op) (program : Cirgen),
  Cirgen.step state (.Sequence (.Assign name op) program) = Cirgen.step (state.update name (Op.eval state op)) program := by
  intros state name op program
  cases op <;> {
    conv =>
      lhs
      unfold Cirgen.step
      simp only [State.update, Map.update, beq_iff_eq]
  }

theorem is0OriginalProgram_constraints_are_what_we_expect :
  ∀ x y z : Felt, (is0OriginalProgram x y z).1.constraints.foldr And _root_.True ↔ (x = 0 ∧ x * x⁻¹ - 1 = 0) := by
  intros x y z
  apply Iff.intro
  intros h
  unfold is0OriginalProgram at h
  sorry
  sorry

end Risc0
