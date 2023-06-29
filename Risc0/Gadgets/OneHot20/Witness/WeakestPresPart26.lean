import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart25

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part26 on st
def part26_state (st: State) : State :=
  
          ((((st[felts][{ name := "%45" }] ←
                  Option.get! (State.felts st { name := "%42" }) +
                    Option.get! (State.felts st { name := "%44" }))["%46"] ←ₛ
                getImpl st { name := "data" } 0 10)[felts][{ name := "%47" }] ←
              Option.get!
                  (State.felts
                    ((st[felts][{ name := "%45" }] ←
                        Option.get! (State.felts st { name := "%42" }) +
                          Option.get! (State.felts st { name := "%44" }))["%46"] ←ₛ
                      getImpl st { name := "data" } 0 10)
                    { name := "%46" }) *
                Option.get! (State.felts st { name := "%9" }))[felts][{ name := "%48" }] ←
            Option.get! (State.felts st { name := "%42" }) + Option.get! (State.felts st { name := "%44" }) +
              Option.get!
                  (State.felts
                    ((st[felts][{ name := "%45" }] ←
                        Option.get! (State.felts st { name := "%42" }) +
                          Option.get! (State.felts st { name := "%44" }))["%46"] ←ₛ
                      getImpl st { name := "data" } 0 10)
                    { name := "%46" }) *
                Option.get!
                  (State.felts st
                    {
                      name :=
                        "%9" })) 

-- Run the program from part26 onwards by using part26_state rather than Code.part26
def part26_state_update (st: State): State :=
  Γ (part26_state st) ⟦Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part26_state for Code.part26 produces the same result
lemma part26_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part26_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part26
  MLIR
  rewrite [←eq]
  unfold part26_state_update part26_state
  rfl

lemma part26_updates_opaque {st : State} : 
  Code.getReturn (part25_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part26_state_update (part25_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part25_state_update, part26_wp]

end Risc0.OneHot20.Witness.WP