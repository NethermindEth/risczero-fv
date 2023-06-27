import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart30

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part31 on st
def part31_state (st: State) : State := 
  
        (withEqZero
          (Option.get! (State.felts st { name := "%20" }) -
            (Option.get! (State.felts st { name := "%70" }) * Option.get! (State.felts st { name := "%19" }) +
              Option.get! (State.felts st { name := "%69" })))
          (((st[felts][{ name := "%71" }] ←
                Option.get! (State.felts st { name := "%70" }) *
                  Option.get! (State.felts st { name := "%19" }))[felts][{ name := "%72" }] ←
              Option.get! (State.felts st { name := "%70" }) * Option.get! (State.felts st { name := "%19" }) +
                Option.get! (State.felts st { name := "%69" }))[felts][{ name := "%73" }] ←
            Option.get! (State.felts st { name := "%20" }) -
              (Option.get! (State.felts st { name := "%70" }) * Option.get! (State.felts st { name := "%19" }) +
                Option.get! (State.felts st { name := "%69" })))) 

-- Prove that substituting part31_state for Code.part31 produces the same result
lemma part31_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram Code.part31 st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part31_state st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  unfold Code.part31
  MLIR
  unfold part31_state
  rfl

lemma part31_updates_opaque {st : State} : 
  Code.getReturn (part30_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part31_state (part30_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part30_state_update, part31_wp]

end Risc0.ComputeDecode.Witness.WP