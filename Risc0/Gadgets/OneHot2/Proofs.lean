import Risc0.Gadgets.OneHot2.Constraints.WeakestPresPart3
import Risc0.Gadgets.OneHot2.Witness.WeakestPresPart5

namespace Risc0

theorem constraints_of_witness {x0 y0 y1 : Risc0.Felt} :
    Risc0.OneHot2.Witness.Code.run (Risc0.OneHot2.Witness.start_state [some x0]) [some y0, some y1] →
      Risc0.OneHot2.Constraints.Code.run (Risc0.OneHot2.Constraints.start_state [some x0] [some y0, some y1])
      := by
  rw [
      Risc0.OneHot2.Witness.WP.closed_form,
      Risc0.OneHot2.Constraints.WP.closed_form
    ]
  aesop

theorem spec_of_constraints {x0 y0 y1 : Risc0.Felt} :
  Risc0.OneHot2.Constraints.Code.run (Risc0.OneHot2.Constraints.start_state [some x0] [some y0, some y1]) →
    (x0 = 0 ∧ y0 = 1 ∧ y1 = 0) ∨ (x0 = 1 ∧ y0 = 0 ∧ y1 = 1) := by
  rw [Risc0.OneHot2.Constraints.WP.closed_form]
  rintro ⟨⟨⟨_, _ | _⟩, _ | _⟩, _⟩ <;> simp_all [sub_eq_zero]

end Risc0

