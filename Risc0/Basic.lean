import Mathlib.Data.Nat.Prime
import Mathlib.Data.Finmap
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Risc0.Map
import Risc0.Wheels

namespace Risc0

@[inline]
def P: ℕ := 15 * 2^27 + 1

axiom P_prime: Nat.Prime P 
instance : Fact (Nat.Prime P) := ⟨P_prime⟩

inductive VarType := | FeltTag | PropTag | BufferTag deriving DecidableEq

open VarType

structure Variable (tag : VarType) :=
  name : String
deriving DecidableEq

abbrev BufferVar := Variable BufferTag
abbrev FeltVar := Variable FeltTag
abbrev PropVar := Variable PropTag

abbrev Felt := ZMod P

instance : Inhabited Felt := ⟨-42⟩

end Risc0
