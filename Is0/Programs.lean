-- This file contains the MLIR program labeled `ORIGINAL` in the `nonzero-example` output.
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Is0.Basic

namespace Risc0

open MLIRNotation in
def is0_witness (input : List Felt) : List Felt :=
  let state' :=
    MLIR.run { felts := Map.empty
             , props := Map.empty
             , input := input
             , output := [42, 42]
             , constraints := []
             } <|
    "x"         ←ₐ input[0];
    "isZeroBit" ←ₐ ??₀⟨"x"⟩;
    output[0]   ←ₐ ⟨"isZeroBit"⟩;
    "invVal"    ←ₐ Inv ⟨"x"⟩;
    output[1]   ←ₐ ⟨"invVal"⟩
  state'.output

open MLIRNotation in
def is0_constraints (input : List Felt) (output : List Felt) : Prop :=
  let state' :=
    MLIR.run { felts := Map.empty
             , props := Map.empty
             , input := input
             , output := output
             , constraints := []
             } <|
    "1"         ←ₐ 1;
    "x"         ←ₐ input[0];
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
  (List.foldr And True) $ List.map (λ e ↦ e = 0) state'.constraints

theorem is0_original_nondet_iff_constraints : ∀ input output : List Felt,
    input.length = 1 ∧ output.length = 2
  → is0_witness input = output ↔ is0_constraints input output := by sorry

end Risc0
