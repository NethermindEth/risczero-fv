import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart38

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part39 on st
def part39_state (st: State) : State :=
  
          (withEqZero
            (Option.get! (State.felts st { name := "%31" }) *
              (Option.get! (State.felts st { name := "%18" }) - Option.get! (State.felts st { name := "%31" })))
            (((st[felts][{ name := "%91" }] ←
                  Option.get! (State.felts st { name := "%88" }) +
                    Option.get! (State.felts st { name := "%28" }))[felts][{ name := "%92" }] ←
                Option.get! (State.felts st { name := "%18" }) -
                  Option.get! (State.felts st { name := "%31" }))[felts][{ name := "%93" }] ←
              Option.get! (State.felts st { name := "%31" }) *
                (Option.get! (State.felts st { name := "%18" }) -
                  Option.get!
                    (State.felts st
                      {
                        name :=
                          "%31" })))) 

-- Run the program from part39 onwards by using part39_state rather than Code.part39
def part39_state_update (st: State): State :=
  Γ (part39_state st) ⟦Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part39_state for Code.part39 produces the same result
lemma part39_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part39_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part39
  MLIR
  rewrite [←eq]
  unfold part39_state_update part39_state
  rfl

lemma part39_updates_opaque {st : State} : 
  Code.getReturn (part38_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part39_state_update (part38_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part38_state_update, part39_wp]

end Risc0.OneHot20.Witness.WP