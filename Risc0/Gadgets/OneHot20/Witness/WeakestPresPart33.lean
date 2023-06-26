import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart32

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part33 on st
def part33_state (st: State) : State :=
  
          ((((st["%73"] ←ₛ getImpl st { name := "data" } 0 19)[felts][{ name := "%74" }] ←
                Option.get! (State.felts (st["%73"] ←ₛ getImpl st { name := "data" } 0 19) { name := "%73" }) *
                  Option.get!
                    (State.felts (st["%73"] ←ₛ getImpl st { name := "data" } 0 19)
                      { name := "%0" }))[felts][{ name := "%75" }] ←
              Option.get!
                  (((st["%73"] ←ₛ getImpl st { name := "data" } 0 19).felts[{ name := "%74" }] ←ₘ
                      Option.get! (State.felts (st["%73"] ←ₛ getImpl st { name := "data" } 0 19) { name := "%73" }) *
                        Option.get! (State.felts (st["%73"] ←ₛ getImpl st { name := "data" } 0 19) { name := "%0" }))
                    { name := "%72" }) +
                Option.get! (State.felts (st["%73"] ←ₛ getImpl st { name := "data" } 0 19) { name := "%73" }) *
                  Option.get!
                    (State.felts (st["%73"] ←ₛ getImpl st { name := "data" } 0 19)
                      { name := "%0" }))[felts][{ name := "%76" }] ←
            Option.get!
                  (((st["%73"] ←ₛ getImpl st { name := "data" } 0 19).felts[{ name := "%74" }] ←ₘ
                      Option.get! (State.felts (st["%73"] ←ₛ getImpl st { name := "data" } 0 19) { name := "%73" }) *
                        Option.get! (State.felts (st["%73"] ←ₛ getImpl st { name := "data" } 0 19) { name := "%0" }))
                    { name := "%72" }) +
                Option.get! (State.felts (st["%73"] ←ₛ getImpl st { name := "data" } 0 19) { name := "%73" }) *
                  Option.get! (State.felts (st["%73"] ←ₛ getImpl st { name := "data" } 0 19) { name := "%0" }) -
              Option.get!
                ((((st["%73"] ←ₛ getImpl st { name := "data" } 0 19).felts[{ name := "%74" }] ←ₘ
                      Option.get! (State.felts (st["%73"] ←ₛ getImpl st { name := "data" } 0 19) { name := "%73" }) *
                        Option.get!
                          (State.felts (st["%73"] ←ₛ getImpl st { name := "data" } 0 19)
                            { name := "%0" }))[{ name := "%75" }] ←ₘ
                    Option.get!
                        (((st["%73"] ←ₛ getImpl st { name := "data" } 0 19).felts[{ name := "%74" }] ←ₘ
                            Option.get!
                                (State.felts (st["%73"] ←ₛ getImpl st { name := "data" } 0 19) { name := "%73" }) *
                              Option.get!
                                (State.felts (st["%73"] ←ₛ getImpl st { name := "data" } 0 19) { name := "%0" }))
                          { name := "%72" }) +
                      Option.get! (State.felts (st["%73"] ←ₛ getImpl st { name := "data" } 0 19) { name := "%73" }) *
                        Option.get! (State.felts (st["%73"] ←ₛ getImpl st { name := "data" } 0 19) { name := "%0" }))
                  {
                    name :=
                      "%20" })) 

-- Run the program from part33 onwards by using part33_state rather than Code.part33
def part33_state_update (st: State): State :=
  Γ (part33_state st) ⟦Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part33_state for Code.part33 produces the same result
lemma part33_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part33_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part33
  MLIR
  rewrite [←eq]
  unfold part33_state_update part33_state
  rfl

lemma part33_updates_opaque {st : State} : 
  Code.getReturn (part32_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part33_state_update (part32_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part32_state_update, part33_wp]

end Risc0.OneHot20.Witness.WP