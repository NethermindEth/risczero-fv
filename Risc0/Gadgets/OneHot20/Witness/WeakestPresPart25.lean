import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart24

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part25 on st
def part25_state (st: State) : State :=
  
          ((((st[felts][{ name := "%41" }] ←
                  Option.get! (State.felts st { name := "%40" }) *
                    Option.get! (State.felts st { name := "%11" }))[felts][{ name := "%42" }] ←
                Option.get!
                    ((st.felts[{ name := "%41" }] ←ₘ
                        Option.get! (State.felts st { name := "%40" }) * Option.get! (State.felts st { name := "%11" }))
                      { name := "%39" }) +
                  Option.get! (State.felts st { name := "%40" }) *
                    Option.get! (State.felts st { name := "%11" }))["%43"] ←ₛ
              getImpl st { name := "data" } 0 9)[felts][{ name := "%44" }] ←
            Option.get!
                (State.felts
                  (((st[felts][{ name := "%41" }] ←
                        Option.get! (State.felts st { name := "%40" }) *
                          Option.get! (State.felts st { name := "%11" }))[felts][{ name := "%42" }] ←
                      Option.get!
                          ((st.felts[{ name := "%41" }] ←ₘ
                              Option.get! (State.felts st { name := "%40" }) *
                                Option.get! (State.felts st { name := "%11" }))
                            { name := "%39" }) +
                        Option.get! (State.felts st { name := "%40" }) *
                          Option.get! (State.felts st { name := "%11" }))["%43"] ←ₛ
                    getImpl st { name := "data" } 0 9)
                  { name := "%43" }) *
              Option.get!
                (State.felts
                  (((st[felts][{ name := "%41" }] ←
                        Option.get! (State.felts st { name := "%40" }) *
                          Option.get! (State.felts st { name := "%11" }))[felts][{ name := "%42" }] ←
                      Option.get!
                          ((st.felts[{ name := "%41" }] ←ₘ
                              Option.get! (State.felts st { name := "%40" }) *
                                Option.get! (State.felts st { name := "%11" }))
                            { name := "%39" }) +
                        Option.get! (State.felts st { name := "%40" }) *
                          Option.get! (State.felts st { name := "%11" }))["%43"] ←ₛ
                    getImpl st { name := "data" } 0 9)
                  {
                    name :=
                      "%10" })) 

-- Run the program from part25 onwards by using part25_state rather than Code.part25
def part25_state_update (st: State): State :=
  Γ (part25_state st) ⟦Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part25_state for Code.part25 produces the same result
lemma part25_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part25_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part25
  MLIR
  rewrite [←eq]
  unfold part25_state_update part25_state
  rfl

lemma part25_updates_opaque {st : State} : 
  Code.getReturn (part24_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part25_state_update (part24_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part24_state_update, part25_wp]

end Risc0.OneHot20.Witness.WP