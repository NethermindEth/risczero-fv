import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart40

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part41 on st
def part41_state (st: State) : State :=
  
          (withEqZero
            (Option.get! (State.felts st { name := "%37" }) *
              (Option.get! (State.felts st { name := "%18" }) - Option.get! (State.felts st { name := "%37" })))
            (((st[felts][{ name := "%97" }] ←
                  Option.get! (State.felts st { name := "%94" }) +
                    Option.get! (State.felts st { name := "%34" }))[felts][{ name := "%98" }] ←
                Option.get! (State.felts st { name := "%18" }) -
                  Option.get! (State.felts st { name := "%37" }))[felts][{ name := "%99" }] ←
              Option.get! (State.felts st { name := "%37" }) *
                (Option.get! (State.felts st { name := "%18" }) -
                  Option.get!
                    (State.felts st
                      {
                        name :=
                          "%37" })))) 

-- Run the program from part41 onwards by using part41_state rather than Code.part41
def part41_state_update (st: State): State :=
  Γ (part41_state st) ⟦Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part41_state for Code.part41 produces the same result
lemma part41_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part41_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part41
  MLIR
  rewrite [←eq]
  unfold part41_state_update part41_state
  rfl

lemma part41_updates_opaque {st : State} : 
  Code.getReturn (part40_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part41_state_update (part40_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part40_state_update, part41_wp]

end Risc0.OneHot20.Witness.WP