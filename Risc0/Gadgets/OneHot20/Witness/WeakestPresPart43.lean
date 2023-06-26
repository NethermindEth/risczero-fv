import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart42

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part43 on st
def part43_state (st: State) : State :=
  
          (withEqZero
            (Option.get! (State.felts st { name := "%43" }) *
              (Option.get! (State.felts st { name := "%18" }) - Option.get! (State.felts st { name := "%43" })))
            (((st[felts][{ name := "%103" }] ←
                  Option.get! (State.felts st { name := "%100" }) +
                    Option.get! (State.felts st { name := "%40" }))[felts][{ name := "%104" }] ←
                Option.get! (State.felts st { name := "%18" }) -
                  Option.get! (State.felts st { name := "%43" }))[felts][{ name := "%105" }] ←
              Option.get! (State.felts st { name := "%43" }) *
                (Option.get! (State.felts st { name := "%18" }) -
                  Option.get!
                    (State.felts st
                      {
                        name :=
                          "%43" })))) 

-- Run the program from part43 onwards by using part43_state rather than Code.part43
def part43_state_update (st: State): State :=
  Γ (part43_state st) ⟦Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part43_state for Code.part43 produces the same result
lemma part43_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part43_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part43
  MLIR
  rewrite [←eq]
  unfold part43_state_update part43_state
  rfl

lemma part43_updates_opaque {st : State} : 
  Code.getReturn (part42_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part43_state_update (part42_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part42_state_update, part43_wp]

end Risc0.OneHot20.Witness.WP