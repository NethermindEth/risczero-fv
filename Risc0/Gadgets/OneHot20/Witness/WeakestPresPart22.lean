import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart21

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part22 on st
def part22_state (st: State) : State :=
  
          ((((st[felts][{ name := "%29" }] ←
                  Option.get! (State.felts st { name := "%28" }) *
                    Option.get! (State.felts st { name := "%15" }))[felts][{ name := "%30" }] ←
                Option.get!
                    ((st.felts[{ name := "%29" }] ←ₘ
                        Option.get! (State.felts st { name := "%28" }) * Option.get! (State.felts st { name := "%15" }))
                      { name := "%27" }) +
                  Option.get! (State.felts st { name := "%28" }) *
                    Option.get! (State.felts st { name := "%15" }))["%31"] ←ₛ
              getImpl st { name := "data" } 0 5)[felts][{ name := "%32" }] ←
            Option.get!
                (State.felts
                  (((st[felts][{ name := "%29" }] ←
                        Option.get! (State.felts st { name := "%28" }) *
                          Option.get! (State.felts st { name := "%15" }))[felts][{ name := "%30" }] ←
                      Option.get!
                          ((st.felts[{ name := "%29" }] ←ₘ
                              Option.get! (State.felts st { name := "%28" }) *
                                Option.get! (State.felts st { name := "%15" }))
                            { name := "%27" }) +
                        Option.get! (State.felts st { name := "%28" }) *
                          Option.get! (State.felts st { name := "%15" }))["%31"] ←ₛ
                    getImpl st { name := "data" } 0 5)
                  { name := "%31" }) *
              Option.get!
                (State.felts
                  (((st[felts][{ name := "%29" }] ←
                        Option.get! (State.felts st { name := "%28" }) *
                          Option.get! (State.felts st { name := "%15" }))[felts][{ name := "%30" }] ←
                      Option.get!
                          ((st.felts[{ name := "%29" }] ←ₘ
                              Option.get! (State.felts st { name := "%28" }) *
                                Option.get! (State.felts st { name := "%15" }))
                            { name := "%27" }) +
                        Option.get! (State.felts st { name := "%28" }) *
                          Option.get! (State.felts st { name := "%15" }))["%31"] ←ₛ
                    getImpl st { name := "data" } 0 5)
                  {
                    name :=
                      "%14" })) 

-- Run the program from part22 onwards by using part22_state rather than Code.part22
def part22_state_update (st: State): State :=
  Γ (part22_state st) ⟦Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part22_state for Code.part22 produces the same result
lemma part22_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part22_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part22
  MLIR
  rewrite [←eq]
  unfold part22_state_update part22_state
  rfl

lemma part22_updates_opaque {st : State} : 
  Code.getReturn (part21_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part22_state_update (part21_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part21_state_update, part22_wp]

end Risc0.OneHot20.Witness.WP