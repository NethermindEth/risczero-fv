import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart21

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part22 on st
def part22_state (st: State) : State :=
  
          (withEqZero
            (Option.get! (State.felts st { name := "%23" }) -
              (Option.get! (State.felts st { name := "%37" }) * Option.get! (State.felts st { name := "%11" }) +
                Option.get! (State.felts st { name := "%24" })))
            (((st[felts][{ name := "%38" }] ←
                  Option.get! (State.felts st { name := "%37" }) *
                    Option.get! (State.felts st { name := "%11" }))[felts][{ name := "%39" }] ←
                Option.get! (State.felts st { name := "%37" }) * Option.get! (State.felts st { name := "%11" }) +
                  Option.get! (State.felts st { name := "%24" }))[felts][{ name := "%40" }] ←
              Option.get! (State.felts st { name := "%23" }) -
                (Option.get! (State.felts st { name := "%37" }) * Option.get! (State.felts st { name := "%11" }) +
                  Option.get!
                    (State.felts st
                      {
                        name :=
                          "%24" })))) 

-- Run the program from part22 onwards by using part22_state rather than Code.part22
def part22_state_update (st: State): State :=
  Γ (part22_state st) ⟦Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part22_state for Code.part22 produces the same result
lemma part22_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part22_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part22
  MLIR
  rewrite [←eq]
  unfold part22_state_update part22_state
  rfl

lemma part22_updates_opaque {st : State} : 
  Code.getReturn (part21_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part22_state_update (part21_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part21_state_update, part22_wp]

end Risc0.ComputeDecode.Witness.WP