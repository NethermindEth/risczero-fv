import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Vector.Basic

import Risc0.BasicTypes
import Risc0.Gadgets.ComputeDecode.Lemmas.Lemmas
import Risc0.Gadgets.ComputeDecode.Lemmas.Spec
import Risc0.Cirgen
import Risc0.Lemmas
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart16
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart31

namespace Risc0.ComputeDecode

theorem constraints_of_witness
  {x₀ x₁ x₂ x₃ : Felt}
  {output : BufferAtTime}
  (h : output.length = 18) 
  (h₁ : output.all Option.isSome) 
  (h_isBytes: ∀ (i : ℕ), i < (4 : ℕ) → isByte (Option.get! (List.get! [some x₀, some x₁, some x₂, some x₃] i))):
  (Witness.Code.run (Witness.start_state [x₀, x₁, x₂, x₃])) output →
    (Constraints.Code.run (Constraints.start_state [x₀, x₁, x₂, x₃] output)) := by
  rcases output with _ | ⟨y0, output⟩ <;> simp at *
  rcases output with _ | ⟨y1, output⟩ <;> simp at *
  rcases output with _ | ⟨y2, output⟩ <;> simp at *
  rcases output with _ | ⟨y3, output⟩ <;> simp at *
  rcases output with _ | ⟨y4, output⟩ <;> simp at *
  rcases output with _ | ⟨y5, output⟩ <;> simp at *
  rcases output with _ | ⟨y6, output⟩ <;> simp at *
  rcases output with _ | ⟨y7, output⟩ <;> simp at *
  rcases output with _ | ⟨y8, output⟩ <;> simp at *
  rcases output with _ | ⟨y9, output⟩ <;> simp at *
  rcases output with _ | ⟨y10, output⟩ <;> simp at *
  rcases output with _ | ⟨y11, output⟩ <;> simp at *
  rcases output with _ | ⟨y12, output⟩ <;> simp at *
  rcases output with _ | ⟨y13, output⟩ <;> simp at *
  rcases output with _ | ⟨y14, output⟩ <;> simp at *
  rcases output with _ | ⟨y15, output⟩ <;> simp at *
  rcases output with _ | ⟨y16, output⟩ <;> simp at *
  rcases output with _ | ⟨y17, output⟩ <;> simp at *
  rcases output with _ | ⟨_, output⟩ <;> simp at *
  rw [Witness.WP.closed_form, decoder_closed_form_equiv_decoder_direct_spec]
  unfold decoder_direct_spec
  simp [Instruction.fromWords]
  intro h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  subst h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  rw [Constraints.WP.closed_form]
  have h_toWords := @toWords_fromWords [x₀, x₁, x₂, x₃] (by simp) h_isBytes (by {
    intros i h_i
    rcases i with _ | i <;> simp at *
    rcases i with _ | i <;> simp at *
    rcases i with _ | i <;> simp at *
    rcases i with _ | i <;> simp at *
    tauto
  })
  unfold Instruction.toWords Instruction.fromWords at h_toWords
  simp at h_toWords
  rcases h_toWords with ⟨h_toWords₀, h_toWords₁, h_toWords₂, h_toWords₃⟩
  rw [←h_toWords₀, ←h_toWords₁, ←h_toWords₂, ←h_toWords₃] 
  aesop

theorem spec_of_constraints {x₀ x₁ x₂ x₃ : Felt}
  {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Felt} :
  Constraints.Code.run (Constraints.start_state [x₀, x₁, x₂, x₃] [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17]) → 
    [x₀, x₁, x₂, x₃] = (Instruction.fromList [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17]).toWords := by
  intros h_
  rw [Constraints.WP.closed_form] at h_
  have h_ := constraints_closed_form_entails_spec h_
  unfold constraints_spec at h_
  simp at h_
  rw [h_]