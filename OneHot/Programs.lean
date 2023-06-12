import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp

import Risc0.Basic
import Risc0.Lemmas
import Risc0.Wheels

namespace Risc0.OneHot

open MLIRNotation

def initial_state (input : Felt) : State :=
  State.empty
  |>.addBuffer "input" (Buffer.init_values ([input]))
  |>.addBuffer "output" (Buffer.init_unset 3)


end Risc0.OneHot
