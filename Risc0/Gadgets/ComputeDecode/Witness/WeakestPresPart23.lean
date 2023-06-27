import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart22

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part23 on st
def part23_state (st: State) : State :=
  
          ((((st["%41"] ←ₛ getImpl st { name := "data" } 0 3)["%42"] ←ₛ
                getImpl st { name := "data" } 0 4)[felts][{ name := "%43" }] ←
              Option.get! (State.felts (st["%42"] ←ₛ getImpl st { name := "data" } 0 4) { name := "%42" }) *
                Option.get! (State.felts st { name := "%7" }))["%44"] ←ₛ
            getImpl st { name := "data" } 0
              11) 

-- Run the program from part23 onwards by using part23_state rather than Code.part23
def part23_state_update (st: State): State :=
  Γ (part23_state st) ⟦Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part23_state for Code.part23 produces the same result
lemma part23_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part23_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part23
  MLIR
  rewrite [←eq]
  unfold part23_state_update part23_state
  rfl

lemma part23_updates_opaque {st : State} : 
  Code.getReturn (part22_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part23_state_update (part22_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part22_state_update, part23_wp]

end Risc0.ComputeDecode.Witness.WP