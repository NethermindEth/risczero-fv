import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart34

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part35 on st
def part35_state (st: State) : State :=
  
          (withEqZero
            (Option.get!
                ((st.felts[{ name := "%80" }] ←ₘ
                    Option.get! (State.felts st { name := "%18" }) - Option.get! (State.felts st { name := "%21" }))
                  { name := "%21" }) *
              (Option.get! (State.felts st { name := "%18" }) - Option.get! (State.felts st { name := "%21" })))
            ((withEqZero (Option.get! st.felts[({ name := "%79" }: FeltVar)]!) st[felts][{ name := "%80" }] ←
                Option.get! (State.felts st { name := "%18" }) -
                  Option.get! (State.felts st { name := "%21" }))[felts][{ name := "%81" }] ←
              Option.get!
                  ((st.felts[{ name := "%80" }] ←ₘ
                      Option.get! (State.felts st { name := "%18" }) - Option.get! (State.felts st { name := "%21" }))
                    { name := "%21" }) *
                (Option.get! (State.felts st { name := "%18" }) -
                  Option.get!
                    (State.felts st
                      {
                        name :=
                          "%21" })))) 

-- Run the program from part35 onwards by using part35_state rather than Code.part35
def part35_state_update (st: State): State :=
  Γ (part35_state st) ⟦Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part35_state for Code.part35 produces the same result
lemma part35_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part35_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part35
  MLIR
  rewrite [←eq]
  unfold part35_state_update part35_state
  rfl

lemma part35_updates_opaque {st : State} : 
  Code.getReturn (part34_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part35_state_update (part34_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part34_state_update, part35_wp]

end Risc0.OneHot20.Witness.WP