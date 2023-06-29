import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart49

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part50 on st
def part50_state (st: State) : State :=
  
          (withEqZero
            (Option.get! (State.felts st { name := "%64" }) *
              (Option.get! (State.felts st { name := "%18" }) - Option.get! (State.felts st { name := "%64" })))
            (((st[felts][{ name := "%124" }] ←
                  Option.get! (State.felts st { name := "%121" }) +
                    Option.get! (State.felts st { name := "%61" }))[felts][{ name := "%125" }] ←
                Option.get! (State.felts st { name := "%18" }) -
                  Option.get! (State.felts st { name := "%64" }))[felts][{ name := "%126" }] ←
              Option.get! (State.felts st { name := "%64" }) *
                (Option.get! (State.felts st { name := "%18" }) -
                  Option.get!
                    (State.felts st { name := "%64" })))) 

-- Run the program from part50 onwards by using part50_state rather than Code.part50
def part50_state_update (st: State): State :=
  Γ (part50_state st) ⟦Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part50_state for Code.part50 produces the same result
lemma part50_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part50_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part50
  MLIR
  rewrite [←eq]
  unfold part50_state_update part50_state
  rfl

lemma part50_updates_opaque {st : State} : 
  Code.getReturn (part49_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part50_state_update (part49_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part49_state_update, part50_wp]

end Risc0.OneHot20.Witness.WP