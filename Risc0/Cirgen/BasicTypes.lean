import Risc0.State

namespace Risc0

inductive IsNondet :=
  | InNondet
  | NotInNondet

open IsNondet

@[reducible]
def lub (x₁ x₂ : IsNondet): IsNondet :=
  match x₁ with
    | .InNondet => .InNondet
    | _ => x₂

def Back := ℕ 

def Back.toNat (n : Back) : ℕ := n

instance : LinearOrderedCommSemiring Back := by unfold Back; exact inferInstance

end Risc0
