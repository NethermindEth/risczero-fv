import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart47

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part48 on st
def part48_state (st: State) : State :=
  
          (withEqZero
            (Option.get! (State.felts st { name := "%58" }) *
              (Option.get! (State.felts st { name := "%18" }) - Option.get! (State.felts st { name := "%58" })))
            (((st[felts][{ name := "%118" }] ←
                  Option.get! (State.felts st { name := "%115" }) +
                    Option.get! (State.felts st { name := "%55" }))[felts][{ name := "%119" }] ←
                Option.get! (State.felts st { name := "%18" }) -
                  Option.get! (State.felts st { name := "%58" }))[felts][{ name := "%120" }] ←
              Option.get! (State.felts st { name := "%58" }) *
                (Option.get! (State.felts st { name := "%18" }) -
                  Option.get!
                    (State.felts st
                      {
                        name :=
                          "%58" })))) 

-- Run the program from part48 onwards by using part48_state rather than Code.part48
def part48_state_update (st: State): State :=
  Γ (part48_state st) ⟦Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part48_state for Code.part48 produces the same result
lemma part48_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part48_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part48
  MLIR
  rewrite [←eq]
  unfold part48_state_update part48_state
  rfl

lemma part48_updates_opaque {st : State} : 
  Code.getReturn (part47_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part48_state_update (part47_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part47_state_update, part48_wp]

end Risc0.OneHot20.Witness.WP