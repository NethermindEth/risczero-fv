import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart0

namespace Risc0.OneHot.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part₁ on st
def part₁_state (st: State) : State :=
  (State.set!
              (st[felts][{ name := "input == 0" }] ←
                if Option.get! (State.felts st { name := "input" }) = 0 then 1 else 0)
              { name := "output" } 0
              (if Option.get! (State.felts st { name := "input" }) = 0 then 1 else 0)[felts][{ name := "input - 1" }] ←
            Option.get!
                ((st.felts[{ name := "input == 0" }] ←ₘ
                    if Option.get! (State.felts st { name := "input" }) = 0 then 1 else 0)
                  { name := "input" }) -
              Option.get!
                ((st.felts[{ name := "input == 0" }] ←ₘ
                    if Option.get! (State.felts st { name := "input" }) = 0 then 1 else 0)
                  { name := "1" }))[felts][{ name := "input == 1" }] ←
          if
              Option.get!
                    ((st.felts[{ name := "input == 0" }] ←ₘ
                        if Option.get! (State.felts st { name := "input" }) = 0 then 1 else 0)
                      { name := "input" }) -
                  Option.get!
                    ((st.felts[{ name := "input == 0" }] ←ₘ
                        if Option.get! (State.felts st { name := "input" }) = 0 then 1 else 0)
                      { name := "1" }) =
                0 then
            1
          else 0

-- Run the program from part₁ onwards by using part₁_state rather than Code.part₁
def part₁_state_update (st: State): State :=
  Γ (part₁_state st) ⟦Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈⟧

-- Prove that substituting part₁_state for Code.part₁ produces the same result
-- ****************************** WEAKEST PRE - Part₁ ******************************
lemma part₁_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram (Code.part₁; Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₁_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈) = prog
  unfold Code.part₁
  MLIR
  rewrite [←eq]
  unfold part₁_state_update part₁_state
  rfl
-- ****************************** WEAKEST PRE - Part₁ ******************************

lemma part₁_updates_opaque {st : State} : 
  (part₀_state_update st).lastOutput = [y₁, y₂, y₃] ↔
  (part₁_state_update (part₀_state st)).lastOutput = [y₁, y₂, y₃] := by
  simp [part₀_state_update, part₁_wp]

end Risc0.OneHot.Witness.WP
