import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart25

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part26 on st
def part26_state (st: State) : State :=
  
          ((withEqZero
              (Option.get! (State.felts st { name := "%22" }) -
                (Option.get! (State.felts st { name := "%52" }) + Option.get! (State.felts st { name := "%41" })))
              ((st[felts][{ name := "%53" }] ←
                  Option.get! (State.felts st { name := "%52" }) +
                    Option.get! (State.felts st { name := "%41" }))[felts][{ name := "%54" }] ←
                Option.get! (State.felts st { name := "%22" }) -
                  (Option.get! (State.felts st { name := "%52" }) +
                    Option.get! (State.felts st { name := "%41" }))))["%55"] ←ₛ
            getImpl st { name := "data" } 0 6) 

-- Run the program from part26 onwards by using part26_state rather than Code.part26
def part26_state_update (st: State): State :=
  Γ (part26_state st) ⟦Code.part27; Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part26_state for Code.part26 produces the same result
lemma part26_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part26_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part26
  MLIR
  rewrite [←eq]
  unfold part26_state_update part26_state
  rfl

lemma part26_updates_opaque {st : State} : 
  Code.getReturn (part25_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part26_state_update (part25_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part25_state_update, part26_wp]

end Risc0.ComputeDecode.Witness.WP