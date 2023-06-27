import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart28

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part29 on st
def part29_state (st: State) : State :=
  
          ((((st[felts][{ name := "%64" }] ←
                  Option.get! (State.felts st { name := "%63" }) *
                    Option.get! (State.felts st { name := "%19" }))[felts][{ name := "%65" }] ←
                Option.get! (State.felts st { name := "%63" }) * Option.get! (State.felts st { name := "%19" }) +
                  Option.get! (State.felts st { name := "%62" }))[felts][{ name := "%66" }] ←
              Option.get! (State.felts st { name := "%63" }) * Option.get! (State.felts st { name := "%19" }) +
                  Option.get! (State.felts st { name := "%62" }) +
                Option.get! (State.felts st { name := "%57" }))[felts][{ name := "%67" }] ←
            Option.get! (State.felts st { name := "%63" }) * Option.get! (State.felts st { name := "%19" }) +
                  Option.get! (State.felts st { name := "%62" }) +
                Option.get! (State.felts st { name := "%57" }) +
              Option.get! (State.felts st { name := "%55" })) 

-- Run the program from part29 onwards by using part29_state rather than Code.part29
def part29_state_update (st: State): State :=
  Γ (part29_state st) ⟦Code.part30; Code.part31⟧

-- Prove that substituting part29_state for Code.part29 produces the same result
lemma part29_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part29_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part30; Code.part31) = prog
  unfold Code.part29
  MLIR
  rewrite [←eq]
  unfold part29_state_update part29_state
  rfl

lemma part29_updates_opaque {st : State} : 
  Code.getReturn (part28_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part29_state_update (part28_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part28_state_update, part29_wp]

end Risc0.ComputeDecode.Witness.WP