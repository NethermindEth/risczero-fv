import Risc0.State.Defs

namespace Risc0.State

  notation:61 st:max "[felts][" n:61 "]" " ← " x:49 => State.updateFelts st n x
  notation:61 st:max "[props][" n:61 "]" " ← " x:49 => State.updateProps st n x
  notation:61 st:max "[" n:61 "]" " ←ₛ " x:49 => State.update st n x

end Risc0.State
