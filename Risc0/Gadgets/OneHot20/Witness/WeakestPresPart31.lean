import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart30

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part31 on st
def part31_state (st: State) : State :=
  
          ((((st[felts][{ name := "%65" }] ←
                  Option.get! (State.felts st { name := "%64" }) *
                    Option.get! (State.felts st { name := "%3" }))[felts][{ name := "%66" }] ←
                Option.get!
                    ((st.felts[{ name := "%65" }] ←ₘ
                        Option.get! (State.felts st { name := "%64" }) * Option.get! (State.felts st { name := "%3" }))
                      { name := "%63" }) +
                  Option.get! (State.felts st { name := "%64" }) *
                    Option.get! (State.felts st { name := "%3" }))["%67"] ←ₛ
              getImpl st { name := "data" } 0 17)[felts][{ name := "%68" }] ←
            Option.get!
                (State.felts
                  (((st[felts][{ name := "%65" }] ←
                        Option.get! (State.felts st { name := "%64" }) *
                          Option.get! (State.felts st { name := "%3" }))[felts][{ name := "%66" }] ←
                      Option.get!
                          ((st.felts[{ name := "%65" }] ←ₘ
                              Option.get! (State.felts st { name := "%64" }) *
                                Option.get! (State.felts st { name := "%3" }))
                            { name := "%63" }) +
                        Option.get! (State.felts st { name := "%64" }) *
                          Option.get! (State.felts st { name := "%3" }))["%67"] ←ₛ
                    getImpl st { name := "data" } 0 17)
                  { name := "%67" }) *
              Option.get!
                (State.felts
                  (((st[felts][{ name := "%65" }] ←
                        Option.get! (State.felts st { name := "%64" }) *
                          Option.get! (State.felts st { name := "%3" }))[felts][{ name := "%66" }] ←
                      Option.get!
                          ((st.felts[{ name := "%65" }] ←ₘ
                              Option.get! (State.felts st { name := "%64" }) *
                                Option.get! (State.felts st { name := "%3" }))
                            { name := "%63" }) +
                        Option.get! (State.felts st { name := "%64" }) *
                          Option.get! (State.felts st { name := "%3" }))["%67"] ←ₛ
                    getImpl st { name := "data" } 0 17)
                  {
                    name :=
                      "%2" })) 

-- Run the program from part31 onwards by using part31_state rather than Code.part31
def part31_state_update (st: State): State :=
  Γ (part31_state st) ⟦Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part31_state for Code.part31 produces the same result
lemma part31_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part31_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part31
  MLIR
  rewrite [←eq]
  unfold part31_state_update part31_state
  rfl

lemma part31_updates_opaque {st : State} : 
  Code.getReturn (part30_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part31_state_update (part30_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part30_state_update, part31_wp]

end Risc0.OneHot20.Witness.WP