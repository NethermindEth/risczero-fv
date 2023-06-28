import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart27

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part28 on st
def part28_state (st: State) : State :=
  
          ((((st[felts][{ name := "%60" }] ←
                  Option.get! (State.felts st { name := "%59" }) *
                    Option.get! (State.felts st { name := "%7" }))[felts][{ name := "%61" }] ←
                Option.get! (State.felts st { name := "%59" }) * Option.get! (State.felts st { name := "%7" }) +
                  Option.get! (State.felts st { name := "%58" }))[felts][{ name := "%62" }] ←
              (Option.get! (State.felts st { name := "%59" }) * Option.get! (State.felts st { name := "%7" }) +
                  Option.get! (State.felts st { name := "%58" })) *
                Option.get! (State.felts st { name := "%15" }))["%63"] ←ₛ
            getImpl st { name := "data" } 0 14) 

-- Run the program from part28 onwards by using part28_state rather than Code.part28
def part28_state_update (st: State): State :=
  Γ (part28_state st) ⟦Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part28_state for Code.part28 produces the same result
lemma part28_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part28_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part28
  MLIR
  rewrite [←eq]
  unfold part28_state_update part28_state
  rfl

lemma part28_updates_opaque {st : State} : 
  Code.getReturn (part27_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part28_state_update (part27_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part27_state_update, part28_wp]

end Risc0.ComputeDecode.Witness.WP