import Risc0.Lemmas
import Risc0.MlirTactics

namespace Risc0

open MLIRNotation

lemma drop_assign_const_swap {α : IsNondet} {name name' : String} {x : Felt}
  (h : name ≠ name') :
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

lemma drop_assign_add_swap
  {lhs rhs : FeltVar}
  {α : IsNondet} {name name' : String}
  (h : name ≠ name') :
  Γ st ⟦name ←ₐ .Add lhs rhs; @MLIR.DropFelt α ⟨name'⟩⟧ =
  Γ st ⟦@MLIR.DropFelt α ⟨name'⟩; name ←ₐ .Add lhs rhs⟧ := by
  MLIR
  simp [State.drop_update_swap, h]
  generalize eq₁ :
    ((State.dropFelts st ({ name := name' } : FeltVar))[felts][
      ({ name := name } : FeltVar)] ← (Option.get! (State.felts st lhs) + Option.get! (State.felts st rhs))) = l
  
  -- unfold State.dropFelts Map.drop State.updateFelts
  -- aesop
  -- funext y
  -- unfold Option.get! Map.update
  -- aesop

-- | Add : FeltVar → FeltVar → Op x
--   | Sub : FeltVar → FeltVar → Op x
--   | Neg : FeltVar           → Op x
--   | Mul : FeltVar → FeltVar → Op x
--   | Pow : FeltVar → ℕ       → Op x
--   | BitAnd : FeltVar → FeltVar → Op x
--   | Inv : FeltVar           → Op InNondet

end Risc0