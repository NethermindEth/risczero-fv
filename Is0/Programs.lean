import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Is0.Basic

namespace Risc0

-- The MLIR program labeled `ORIGINAL` in the `nonzero-example` output.
open CirgenNotation in
def is0OriginalProgram (x : Felt) (y : Felt) (z : Felt) : State × Option Prop :=
  Cirgen.step { felts := Map.empty
              , props := Map.empty
              , buffers := Map.fromList [("in", [x]), ("out", [y, z])]
              , constraints := []
              } <|
  "1"         ←ₐ 1;
  "x"         ←ₐ input[0];
  "isZeroBit" ←ₐ ??₀⟨"x"⟩;
  [0]         ←ₐ ⟨"isZeroBit"⟩;
  "invVal"    ←ₐ Inv ⟨"x"⟩;
  [1]         ←ₐ ⟨"invVal"⟩;
  "out[0]"    ←ₐ output[0];
  guard ⟨"out[0]"⟩ then
    ?₀⟨"x"⟩;
  "1 - out[0]" ←ₐ ⟨"1"⟩ - ⟨"out[0]"⟩;
  guard ⟨"1 - out[0]"⟩ then (
    "out[1]"         ←ₐ output[1];
    "x * out[1]"     ←ₐ ⟨"x"⟩ * ⟨"out[1]"⟩;
    "x * out[1] - 1" ←ₐ ⟨"x * out[1]"⟩ - ⟨"1"⟩;
    ?₀ ⟨"x * out[1] - 1"⟩
  )

-- The MLIR program labeled `CONSTAINTS` in the `nonzero-example` output.
open CirgenNotation in
def is0ConstraintsProgram (x : Felt) (y : Felt) (z : Felt) : State × Option Prop :=
  Cirgen.step { felts := Map.empty
              , props := Map.empty
              , buffers := Map.fromList [("in", [x]), ("out", [y, z])]
              , constraints := []
              } <| 
  "1"                                   ←ₐ 1;
  "true"                                ←ₐ ⊤;
  "x"                                   ←ₐ input[0];
  "isZeroBit"                           ←ₐ output[0];
  "x = 0"                               ←ₐ ⟨"true"⟩ &₀ ⟨"x"⟩;
  "IF isZeroBit THEN (x = 0) ELSE true" ←ₐ ⟨"true"⟩ guard ⟨"isZeroBit"⟩ & ⟨"x = 0"⟩;
  "1 - isZeroBit"                       ←ₐ ⟨"1"⟩ - ⟨"isZeroBit"⟩;
  "invVal"                              ←ₐ output[1];
  "x * invVal"                          ←ₐ ⟨"x"⟩ * ⟨"invVal"⟩;
  "x * invVal - 1"                      ←ₐ ⟨"x * invVal"⟩ - ⟨"1"⟩;
  "x * invVal - 1 = 0"                  ←ₐ ⟨"true"⟩ &₀ ⟨"x * invVal - 1"⟩;
  "result"                              ←ₐ ⟨"IF isZeroBit THEN (x = 0) ELSE true"⟩ guard ⟨"1 - isZeroBit"⟩ & ⟨"x * invVal - 1 = 0"⟩;
  ret ["result"]

end Risc0
