import Risc0.Lemmas
import Risc0.MlirTactics

namespace Risc0

open MLIRNotation

section

variable {α : IsNondet} {name name' : String} {x : Felt}
         {lhs rhs : FeltVar}

-- Section-wide obvious assumptions.
variable (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) (h₂ : ⟨name'⟩ ≠ rhs)

lemma drop_assign_const_swap :
  Γ st ⟦name ←ₐ C x; @MLIR.DropFelt α ⟨name'⟩⟧ =
  Γ st ⟦@MLIR.DropFelt α ⟨name'⟩; name ←ₐ C x⟧ := by
  MLIR
  simp [State.drop_update_swap, h]

-- lemma drop_assign_true_swap {α : IsNondet} {name name' : String} {x : Felt}
--   (h : name ≠ name') :
--   Γ st ⟦name ←ₐ ⊤; @MLIR.DropFelt α ⟨name'⟩⟧ =
--   Γ st ⟦@MLIR.DropFelt α ⟨name'⟩; name ←ₐ ⊤⟧ := by
--   MLIR
--   simp [State.drop_update_swap, h]

lemma drop_assign_add_swap :
  Γ st ⟦name ←ₐ .Add lhs rhs; @MLIR.DropFelt α ⟨name'⟩⟧ =
  Γ st ⟦@MLIR.DropFelt α ⟨name'⟩; name ←ₐ .Add lhs rhs⟧ := by
  MLIR
  simp [State.drop_update_swap, h]
  unfold State.dropFelts Map.drop State.updateFelts
  aesop

lemma drop_assign_sub_swap :
  Γ st ⟦name ←ₐ .Sub lhs rhs; @MLIR.DropFelt α ⟨name'⟩⟧ =
  Γ st ⟦@MLIR.DropFelt α ⟨name'⟩; name ←ₐ .Sub lhs rhs⟧ := by
  MLIR
  simp [State.drop_update_swap, h]
  unfold State.dropFelts Map.drop State.updateFelts
  aesop

lemma drop_assign_neg_swap :
  Γ st ⟦name ←ₐ .Neg lhs; @MLIR.DropFelt α ⟨name'⟩⟧ =
  Γ st ⟦@MLIR.DropFelt α ⟨name'⟩; name ←ₐ .Neg lhs⟧ := by
  MLIR
  simp [State.drop_update_swap, h]
  unfold State.dropFelts Map.drop
  aesop

lemma drop_assign_mul_swap :
  Γ st ⟦name ←ₐ .Mul lhs rhs; @MLIR.DropFelt α ⟨name'⟩⟧ =
  Γ st ⟦@MLIR.DropFelt α ⟨name'⟩; name ←ₐ .Mul lhs rhs⟧ := by
  MLIR
  simp [State.drop_update_swap, h]
  unfold State.dropFelts Map.drop State.updateFelts
  aesop

lemma drop_assign_pow_swap {n : ℕ} :
  Γ st ⟦name ←ₐ .Pow lhs n; @MLIR.DropFelt α ⟨name'⟩⟧ =
  Γ st ⟦@MLIR.DropFelt α ⟨name'⟩; name ←ₐ .Pow lhs n⟧ := by
  MLIR
  simp [State.drop_update_swap, h, State.get_dropFelts_of_ne h₁]

lemma drop_assign_bitand_swap :
  Γ st ⟦name ←ₐ .BitAnd lhs rhs; @MLIR.DropFelt α ⟨name'⟩⟧ =
  Γ st ⟦@MLIR.DropFelt α ⟨name'⟩; name ←ₐ .BitAnd lhs rhs⟧ := by
  MLIR
  simp [State.drop_update_swap, h, feltBitAnd, State.get_dropFelts_of_ne h₁]
  aesop

lemma drop_assign_inv_swap :
  Γ st ⟦name ←ₐ .Inv lhs; dropfelt ⟨name'⟩⟧ =
  Γ st ⟦dropfelt ⟨name'⟩; name ←ₐ .Inv lhs⟧ := by
  MLIR
  simp [State.drop_update_swap, h, State.get_dropFelts_of_ne h₁]

lemma drop_assign_isz_swap :
  Γ st ⟦name ←ₐ .Isz lhs; dropfelt ⟨name'⟩⟧ =
  Γ st ⟦dropfelt ⟨name'⟩; name ←ₐ .Isz lhs⟧ := by
  MLIR
  simp [State.drop_update_swap, h]
  unfold State.dropFelts Map.drop State.updateFelts
  aesop

end

end Risc0