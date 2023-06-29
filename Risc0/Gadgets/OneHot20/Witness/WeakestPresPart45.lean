import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart44

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part45 on st
def part45_state (st: State) : State :=
  
          (withEqZero
            (Option.get! (State.felts st { name := "%49" }) *
              (Option.get! (State.felts st { name := "%18" }) - Option.get! (State.felts st { name := "%49" })))
            (((st[felts][{ name := "%109" }] ←
                  Option.get! (State.felts st { name := "%106" }) +
                    Option.get! (State.felts st { name := "%46" }))[felts][{ name := "%110" }] ←
                Option.get! (State.felts st { name := "%18" }) -
                  Option.get! (State.felts st { name := "%49" }))[felts][{ name := "%111" }] ←
              Option.get! (State.felts st { name := "%49" }) *
                (Option.get! (State.felts st { name := "%18" }) -
                  Option.get!
                    (State.felts st
                      {
                        name :=
                          "%49" })))) 

-- Run the program from part45 onwards by using part45_state rather than Code.part45
def part45_state_update (st: State): State :=
  Γ (part45_state st) ⟦Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part45_state for Code.part45 produces the same result
lemma part45_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part45_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part45
  MLIR
  rewrite [←eq]
  unfold part45_state_update part45_state
  rfl

lemma part45_updates_opaque {st : State} : 
  Code.getReturn (part44_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part45_state_update (part44_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part44_state_update, part45_wp]

end Risc0.OneHot20.Witness.WP