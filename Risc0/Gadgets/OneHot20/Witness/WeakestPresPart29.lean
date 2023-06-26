import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart28

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part29 on st
def part29_state (st: State) : State :=
  
          ((((st[felts][{ name := "%57" }] ←
                  Option.get! (State.felts st { name := "%54" }) +
                    Option.get! (State.felts st { name := "%56" }))["%58"] ←ₛ
                getImpl st { name := "data" } 0 14)[felts][{ name := "%59" }] ←
              Option.get!
                  (State.felts
                    ((st[felts][{ name := "%57" }] ←
                        Option.get! (State.felts st { name := "%54" }) +
                          Option.get! (State.felts st { name := "%56" }))["%58"] ←ₛ
                      getImpl st { name := "data" } 0 14)
                    { name := "%58" }) *
                Option.get!
                  (State.felts
                    ((st[felts][{ name := "%57" }] ←
                        Option.get! (State.felts st { name := "%54" }) +
                          Option.get! (State.felts st { name := "%56" }))["%58"] ←ₛ
                      getImpl st { name := "data" } 0 14)
                    { name := "%5" }))[felts][{ name := "%60" }] ←
            Option.get!
                ((((st[felts][{ name := "%57" }] ←
                          Option.get! (State.felts st { name := "%54" }) +
                            Option.get! (State.felts st { name := "%56" }))["%58"] ←ₛ
                        getImpl st { name := "data" } 0 14).felts[{ name := "%59" }] ←ₘ
                    Option.get!
                        (State.felts
                          ((st[felts][{ name := "%57" }] ←
                              Option.get! (State.felts st { name := "%54" }) +
                                Option.get! (State.felts st { name := "%56" }))["%58"] ←ₛ
                            getImpl st { name := "data" } 0 14)
                          { name := "%58" }) *
                      Option.get!
                        (State.felts
                          ((st[felts][{ name := "%57" }] ←
                              Option.get! (State.felts st { name := "%54" }) +
                                Option.get! (State.felts st { name := "%56" }))["%58"] ←ₛ
                            getImpl st { name := "data" } 0 14)
                          { name := "%5" }))
                  { name := "%57" }) +
              Option.get!
                  (State.felts
                    ((st[felts][{ name := "%57" }] ←
                        Option.get! (State.felts st { name := "%54" }) +
                          Option.get! (State.felts st { name := "%56" }))["%58"] ←ₛ
                      getImpl st { name := "data" } 0 14)
                    { name := "%58" }) *
                Option.get!
                  (State.felts
                    ((st[felts][{ name := "%57" }] ←
                        Option.get! (State.felts st { name := "%54" }) +
                          Option.get! (State.felts st { name := "%56" }))["%58"] ←ₛ
                      getImpl st { name := "data" } 0 14)
                    {
                      name :=
                        "%5" })) 

-- Run the program from part29 onwards by using part29_state rather than Code.part29
def part29_state_update (st: State): State :=
  Γ (part29_state st) ⟦Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part29_state for Code.part29 produces the same result
lemma part29_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part29_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part29
  MLIR
  rewrite [←eq]
  unfold part29_state_update part29_state
  rfl

lemma part29_updates_opaque {st : State} : 
  Code.getReturn (part28_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part29_state_update (part28_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part28_state_update, part29_wp]

end Risc0.OneHot20.Witness.WP