import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart23

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part24 on st
def part24_state (st: State) : State :=
  
          ((((st["%45"] ←ₛ getImpl st { name := "data" } 0 2)[felts][{ name := "%46" }] ←
                Option.get! (State.felts (st["%45"] ←ₛ getImpl st { name := "data" } 0 2) { name := "%45" }) *
                  Option.get! (State.felts st { name := "%11" }))["%47"] ←ₛ
              getImpl st { name := "data" } 0 12)[felts][{ name := "%48" }] ←
            Option.get!
                (State.felts
                  (((st["%45"] ←ₛ getImpl st { name := "data" } 0 2)[felts][{ name := "%46" }] ←
                      Option.get! (State.felts (st["%45"] ←ₛ getImpl st { name := "data" } 0 2) { name := "%45" }) *
                        Option.get! (State.felts st { name := "%11" }))["%47"] ←ₛ
                    getImpl st { name := "data" } 0 12)
                  { name := "%47" }) *
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%13" })) 

-- Run the program from part24 onwards by using part24_state rather than Code.part24
def part24_state_update (st: State): State :=
  Γ (part24_state st) ⟦Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part24_state for Code.part24 produces the same result
lemma part24_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part24_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part24
  MLIR
  rewrite [←eq]
  unfold part24_state_update part24_state
  rfl

lemma part24_updates_opaque {st : State} : 
  Code.getReturn (part23_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part24_state_update (part23_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part23_state_update, part24_wp]

end Risc0.ComputeDecode.Witness.WP