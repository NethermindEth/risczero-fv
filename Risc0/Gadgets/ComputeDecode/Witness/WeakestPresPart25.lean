import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart24

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part25 on st
def part25_state (st: State) : State :=
  
          ((((st[felts][{ name := "%49" }] ←
                  Option.get! (State.felts st { name := "%48" }) +
                    Option.get! (State.felts st { name := "%46" }))[felts][{ name := "%50" }] ←
                Option.get! (State.felts st { name := "%48" }) + Option.get! (State.felts st { name := "%46" }) +
                  Option.get! (State.felts st { name := "%44" }))[felts][{ name := "%51" }] ←
              (Option.get! (State.felts st { name := "%48" }) + Option.get! (State.felts st { name := "%46" }) +
                  Option.get! (State.felts st { name := "%44" })) *
                Option.get! (State.felts st { name := "%15" }))[felts][{ name := "%52" }] ←
            (Option.get! (State.felts st { name := "%48" }) + Option.get! (State.felts st { name := "%46" }) +
                  Option.get! (State.felts st { name := "%44" })) *
                Option.get! (State.felts st { name := "%15" }) +
              Option.get!
                (State.felts st
                  { name := "%43" })) 

-- Run the program from part25 onwards by using part25_state rather than Code.part25
def part25_state_update (st: State): State :=
  Γ (part25_state st) ⟦Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part25_state for Code.part25 produces the same result
lemma part25_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part25_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part25
  MLIR
  rewrite [←eq]
  unfold part25_state_update part25_state
  rfl

lemma part25_updates_opaque {st : State} : 
  Code.getReturn (part24_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part25_state_update (part24_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part24_state_update, part25_wp]

end Risc0.ComputeDecode.Witness.WP