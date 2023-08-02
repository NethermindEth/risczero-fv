import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart39
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart54

namespace Risc0

theorem constraints_of_witness : 
    Risc0.OneHot20.Witness.Code.run (Risc0.OneHot20.Witness.start_state [some x0]) [some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7, some y8, some y9, some y10, some y11, some y12, some y13, some y14, some y15, some y16, some y17, some y18, some y19] →
      Risc0.OneHot20.Constraints.Code.run (Risc0.OneHot20.Constraints.start_state [some x0] [some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7, some y8, some y9, some y10, some y11, some y12, some y13, some y14, some y15, some y16, some y17, some y18, some y19])
      := by
  rw [
    Risc0.OneHot20.Witness.WP.closed_form, 
    Risc0.OneHot20.Constraints.WP.closed_form
  ] 
  rintro ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀⟩, h₂₁⟩
  simp at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆ h₁₇ h₁₈ h₁₉ h₂₀
  simp [←h₁, ← h₂, ← h₃, ← h₄, ← h₅, ← h₆, ← h₇, ← h₈, ← h₉, ← h₁₀, ← h₁₁, ← h₁₂, ← h₁₃, ← h₁₄, ← h₁₅, ← h₁₆, ← h₁₇, ← h₁₈, ← h₁₉, ← h₂₀] at *
  save
  simp [not_or] at h₂₁
  -- fincases





-- theorem spec_of_constraints {x0 y0 y1 : Risc0.Felt} : 
--   Risc0.OneHot2.Constraints.Code.run (Risc0.OneHot2.Constraints.start_state [some x0] [some y0, some y1]) →
--     x0 = 0 ∨ x0 = 1 := by 
--   rw [Risc0.OneHot2.Constraints.WP.closed_form]
--   rintro ⟨⟨⟨_, _ | _⟩, _ | _⟩, _⟩ <;> simp_all [sub_eq_zero]

end Risc0

