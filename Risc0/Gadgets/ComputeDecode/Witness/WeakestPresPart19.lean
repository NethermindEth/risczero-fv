import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart18

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part19 on st
def part19_state (st: State) : State :=
  
          ((((st["%26"] ←ₛ getImpl st { name := "data" } 0 8)[felts][{ name := "%27" }] ←
                Option.get! (State.felts (st["%26"] ←ₛ getImpl st { name := "data" } 0 8) { name := "%26" }) *
                  Option.get! (State.felts st { name := "%7" }))["%28"] ←ₛ
              getImpl st { name := "data" } 0 9)[felts][{ name := "%29" }] ←
            Option.get!
                (State.felts
                  (((st["%26"] ←ₛ getImpl st { name := "data" } 0 8)[felts][{ name := "%27" }] ←
                      Option.get! (State.felts (st["%26"] ←ₛ getImpl st { name := "data" } 0 8) { name := "%26" }) *
                        Option.get! (State.felts st { name := "%7" }))["%28"] ←ₛ
                    getImpl st { name := "data" } 0 9)
                  { name := "%28" }) *
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%13" })) 

-- Run the program from part19 onwards by using part19_state rather than Code.part19
def part19_state_update (st: State): State :=
  Γ (part19_state st) ⟦Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part19_state for Code.part19 produces the same result
lemma part19_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part19_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part19
  MLIR
  rewrite [←eq]
  unfold part19_state_update part19_state
  rfl

lemma part19_updates_opaque {st : State} : 
  Code.getReturn (part18_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part19_state_update (part18_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part18_state_update, part19_wp]

end Risc0.ComputeDecode.Witness.WP