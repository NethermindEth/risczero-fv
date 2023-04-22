import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Is0.Basic

namespace Risc0

-- The MLIR program labeled `ORIGINAL` in the `nonzero-example` output.
def is0OriginalProgram (x : Felt) (y : Felt) (z : Felt) : State × Option Prop :=
  Cirgen.step { felts := Map.empty
              , props := Map.empty
              , buffers := Map.fromList [("in", [x]), ("out", [y, z])]
              , constraints := []
              }
    (.Sequence
    (.Assign "1" (Op.Const 1))
    (.Sequence
    (.Assign "x" (Op.Get ⟨"in"⟩ 0 0))
    (.Sequence
    (.Assign "isZeroBit" (Op.Isz ⟨"x"⟩))
    (.Sequence
    (.Set ⟨"out"⟩ 0 ⟨"isZeroBit"⟩)
    (.Sequence
    (.Assign "invVal" (Op.Inv ⟨"x"⟩))
    (.Sequence
    (.Set ⟨"out"⟩ 1 ⟨"invVal"⟩)
    (.Sequence
    (.Assign "out[0]" (Op.Get ⟨"out"⟩ 0 0))
    (.Sequence
    (.If ⟨"out[0]"⟩
      (.Eqz ⟨"x"⟩))
    (.Sequence
    (.Assign "1 - out[0]" (Op.Sub ⟨"1"⟩ ⟨"out[0]"⟩))
    (.If ⟨"1 - out[0]"⟩
      (.Sequence
      (.Assign "out[1]" (Op.Get ⟨"out"⟩ 1 0))
      (.Sequence
      (.Assign "x * out[1]" (Op.Mul ⟨"x"⟩ ⟨"out[1]"⟩))
      (.Sequence
        (.Assign "x * out[1] - 1" (Op.Sub ⟨"x * out[1]"⟩ ⟨"1"⟩))
        (.Eqz ⟨"x * out[1] - 1"⟩))))))))))))))

-- The MLIR program labeled `CONSTAINTS` in the `nonzero-example` output.
def is0ConstraintsProgram (x : Felt) (y : Felt) (z : Felt) : State × Option Prop :=
  Cirgen.step { felts := Map.empty
              , props := Map.empty
              , buffers := Map.fromList [("in", [x]), ("out", [y, z])]
              , constraints := []
              }
  (.Sequence
    (.Sequence
      (.Sequence
        (.Sequence
          (.Sequence
            (.Sequence
              (.Sequence
                (.Sequence
                  (.Sequence
                    (.Sequence
                      (.Sequence
                        (.Sequence
                          (.Assign "1" (Op.Const 1))
                          (.Assign "true" Op.True))
                          (.Assign "x" (Op.Get ⟨"in"⟩ 0 0)))
                          (.Assign "isZeroBit" (Op.Get ⟨"out"⟩ 0 0)))
                          (.Assign "x = 0" (Op.AndEqz ⟨"true"⟩ ⟨"x"⟩)))
                          (.Assign "IF isZeroBit THEN (x = 0) ELSE true" (Op.AndCond ⟨"true"⟩ ⟨"isZeroBit"⟩ ⟨"x = 0"⟩)))
                          (.Assign "1 - isZeroBit" (Op.Sub ⟨"1"⟩ ⟨"isZeroBit"⟩)))
                          (.Assign "invVal" (Op.Get ⟨"out"⟩ 1 0)))
                          (.Assign "x * invVal" (Op.Mul ⟨"x"⟩ ⟨"invVal"⟩)))
                          (.Assign "x * invVal - 1" (Op.Sub ⟨"x * invVal"⟩ ⟨"1"⟩)))
                          (.Assign "x * invVal - 1 = 0" (Op.AndEqz ⟨"true"⟩ ⟨"x * invVal - 1"⟩)))
                          (.Assign "result"
                            (Op.AndCond
                              ⟨"IF isZeroBit THEN (x = 0) ELSE true"⟩
                              ⟨"1 - isZeroBit"⟩
                              ⟨"x * invVal - 1 = 0"⟩)))
                          (.Return "result"))

end Risc0
