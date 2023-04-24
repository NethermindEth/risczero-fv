-- This file contains the MLIR program labeled `ORIGINAL` in the `nonzero-example` output.
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Is0.Basic

namespace Risc0

open CirgenNotation in
def is0OriginalNondet (x : Felt) (y : Felt) (z : Felt) : State × Option (Felt × Felt) :=
  Cirgen.run { felts := Map.empty
              , props := Map.empty
              , buffers := Map.fromList [("in", [x]), ("out", [y, z])]
              , constraints := []
              } <|
  "x"         ←ₐ input[0];
  "isZeroBit" ←ₐ ??₀⟨"x"⟩;
  [0]         ←ₐ ⟨"isZeroBit"⟩;
  "invVal"    ←ₐ Inv ⟨"x"⟩;
  [1]         ←ₐ ⟨"invVal"⟩;
  "out[0]"    ←ₐ output[0];
  ret ["out[0]", "out[1]"]

open CirgenNotation in
def is0OriginalConstraints (x : Felt) (isZeroBit : Felt) (invVal : Felt) : State × Option (Felt × Felt) :=
  Cirgen.run { felts := Map.empty
              , props := Map.empty
              , buffers := Map.fromList [("in", [x]), ("out", [isZeroBit, invVal])]
              , constraints := []
              } <|
  "1"         ←ₐ 1;
  "x"         ←ₐ input[0];
  "isZeroBit" ←ₐ isZeroBit;
  [0]         ←ₐ ⟨"isZeroBit"⟩;
  "invVal"    ←ₐ invVal;
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

end Risc0
