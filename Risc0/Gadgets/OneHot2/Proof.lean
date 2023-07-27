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
    x0 = 0 ∨ x0 = 1 := by
  have arith₁ {a b : Risc0.Felt} (h : a - b = (0 : Risc0.Felt)) : a = b := by
    rw [sub_eq_iff_eq_add, zero_add] at h
    exact h
  rw [
      Risc0.OneHot2.Constraints.WP.closed_form
  ]
  intro h 
  rcases h.1.1.2 with h₀ | h₀; rcases h.1.2 with h₁ | h₁
  {
    aesop
  }
  {
    right
    rw [←arith₁ h.1.1.1]
    exact Eq.symm (arith₁ h₁)
  }
  rcases h.1.2 with h₁ | h₁
  {
    left
    rw [←arith₁ h.1.1.1]
    exact h₁
  }
  {
    have h₀ := Eq.symm (arith₁ h₀)
    have h₁ := Eq.symm (arith₁ h₁)
    have contra := h.2
    rw [h₀, h₁] at contra
    simp at contra
  }

end Risc0

