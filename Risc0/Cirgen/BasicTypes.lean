import Risc0.BasicTypes

namespace Risc0

inductive IsNondet :=
  | InNondet
  | NotInNondet

open IsNondet

@[simp]
lemma IsNondet.sizeOf {x : IsNondet} : sizeOf x = 1 := by
  cases x <;> simp only

@[reducible]
def lub (x₁ x₂ : IsNondet): IsNondet :=
  match x₁ with
    | .InNondet => .InNondet
    | _ => x₂

def Back := ℕ 

def Back.toNat (n : Back) : ℕ := n

instance : LinearOrderedCommSemiring Back := by unfold Back; exact inferInstance

end Risc0
