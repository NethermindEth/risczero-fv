import Mathlib.Data.Vector.Basic

namespace Option

@[simp]
lemma get!_of_some {α : Type} [Inhabited α] (x : α) : (some x).get! = x := rfl

end Option

namespace List

def push {α : Type} (x : α) (l : List α) : List α :=
  l ++ [x]

end List

namespace Vector

def push {α : Type} {k : ℕ} (x : α) : Vector α k → Vector α (k + 1)
  | ⟨l, h⟩ => ⟨l.push x, by simp [List.push, h]⟩

end Vector

namespace Risc0

namespace Wheels

end Wheels

register_option pp.explicitOfNat : Bool := {
  defValue := false
  group    := "pp"
  descr    := "(pretty printer) display implicit arguments of ofNat"
}

end Risc0