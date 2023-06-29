import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart26

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part27 on st
def part27_state (st: State) : State :=
  
          ((((st["%56"] ←ₛ getImpl st { name := "data" } 0 7)[felts][{ name := "%57" }] ←
                Option.get! (State.felts (st["%56"] ←ₛ getImpl st { name := "data" } 0 7) { name := "%56" }) *
                  Option.get! (State.felts st { name := "%7" }))["%58"] ←ₛ
              getImpl st { name := "data" } 0 5)["%59"] ←ₛ
            getImpl
              ((st["%56"] ←ₛ getImpl st { name := "data" } 0 7)[felts][{ name := "%57" }] ←
                Option.get! (State.felts (st["%56"] ←ₛ getImpl st { name := "data" } 0 7) { name := "%56" }) *
                  Option.get! (State.felts st { name := "%7" }))
              { name := "data" } 0 15) 

-- Run the program from part27 onwards by using part27_state rather than Code.part27
def part27_state_update (st: State): State :=
  Γ (part27_state st) ⟦Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part27_state for Code.part27 produces the same result
lemma part27_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part27_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part27
  MLIR
  rewrite [←eq]
  unfold part27_state_update part27_state
  rfl

lemma part27_updates_opaque {st : State} : 
  Code.getReturn (part26_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part27_state_update (part26_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part26_state_update, part27_wp]

end Risc0.ComputeDecode.Witness.WP