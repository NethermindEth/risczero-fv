import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart19

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part20 on st
def part20_state (st: State) : State :=
  
          ((((st["%30"] ←ₛ getImpl st { name := "data" } 0 1)[felts][{ name := "%31" }] ←
                Option.get! (State.felts (st["%30"] ←ₛ getImpl st { name := "data" } 0 1) { name := "%30" }) *
                  Option.get! (State.felts st { name := "%15" }))[felts][{ name := "%32" }] ←
              Option.get! (State.felts (st["%30"] ←ₛ getImpl st { name := "data" } 0 1) { name := "%30" }) *
                  Option.get! (State.felts st { name := "%15" }) +
                Option.get! (State.felts st { name := "%29" }))[felts][{ name := "%33" }] ←
            Option.get! (State.felts (st["%30"] ←ₛ getImpl st { name := "data" } 0 1) { name := "%30" }) *
                  Option.get! (State.felts st { name := "%15" }) +
                Option.get! (State.felts st { name := "%29" }) +
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%27" })) 

-- Run the program from part20 onwards by using part20_state rather than Code.part20
def part20_state_update (st: State): State :=
  Γ (part20_state st) ⟦Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part20_state for Code.part20 produces the same result
lemma part20_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part20_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part20
  MLIR
  rewrite [←eq]
  unfold part20_state_update part20_state
  rfl

lemma part20_updates_opaque {st : State} : 
  Code.getReturn (part19_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part20_state_update (part19_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part19_state_update, part20_wp]

end Risc0.ComputeDecode.Witness.WP