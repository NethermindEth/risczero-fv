import Mathlib.Data.Vector.Basic

namespace Option

end Option

namespace Vector

def push {α : Type} {k : ℕ} (x : α) : Vector α k → Vector α (k + 1)
  | ⟨l, h⟩ => ⟨l ++ [x], by simp [h]⟩

end Vector

namespace Risc0

namespace Wheels

end Wheels

end Risc0