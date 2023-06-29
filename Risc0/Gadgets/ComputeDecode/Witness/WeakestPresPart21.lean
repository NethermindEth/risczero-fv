import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart20

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part21 on st
def part21_state (st: State) : State :=
  
          ((((st[felts][{ name := "%34" }] ←
                  Option.get! (State.felts st { name := "%33" }) +
                    Option.get! (State.felts st { name := "%25" }))["%35"] ←ₛ
                getImpl st { name := "data" } 0 10)[felts][{ name := "%36" }] ←
              Option.get!
                  (State.felts
                    ((st[felts][{ name := "%34" }] ←
                        Option.get! (State.felts st { name := "%33" }) +
                          Option.get! (State.felts st { name := "%25" }))["%35"] ←ₛ
                      getImpl st { name := "data" } 0 10)
                    { name := "%35" }) *
                Option.get! (State.felts st { name := "%3" }))[felts][{ name := "%37" }] ←
            Option.get!
                  (State.felts
                    ((st[felts][{ name := "%34" }] ←
                        Option.get! (State.felts st { name := "%33" }) +
                          Option.get! (State.felts st { name := "%25" }))["%35"] ←ₛ
                      getImpl st { name := "data" } 0 10)
                    { name := "%35" }) *
                Option.get! (State.felts st { name := "%3" }) +
              (Option.get! (State.felts st { name := "%33" }) +
                Option.get!
                  (State.felts st
                    {
                      name :=
                        "%25" }))) 

-- Run the program from part21 onwards by using part21_state rather than Code.part21
def part21_state_update (st: State): State :=
  Γ (part21_state st) ⟦Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31⟧

-- Prove that substituting part21_state for Code.part21 produces the same result
lemma part21_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part21_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31) = prog
  unfold Code.part21
  MLIR
  rewrite [←eq]
  unfold part21_state_update part21_state
  rfl

lemma part21_updates_opaque {st : State} : 
  Code.getReturn (part20_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part21_state_update (part20_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part20_state_update, part21_wp]

end Risc0.ComputeDecode.Witness.WP