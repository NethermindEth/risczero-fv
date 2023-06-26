import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart27

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part28 on st
def part28_state (st: State) : State :=
  
          ((((st[felts][{ name := "%53" }] ←
                  Option.get! (State.felts st { name := "%52" }) *
                    Option.get! (State.felts st { name := "%7" }))[felts][{ name := "%54" }] ←
                Option.get!
                    ((st.felts[{ name := "%53" }] ←ₘ
                        Option.get! (State.felts st { name := "%52" }) * Option.get! (State.felts st { name := "%7" }))
                      { name := "%51" }) +
                  Option.get! (State.felts st { name := "%52" }) *
                    Option.get! (State.felts st { name := "%7" }))["%55"] ←ₛ
              getImpl st { name := "data" } 0 13)[felts][{ name := "%56" }] ←
            Option.get!
                (State.felts
                  (((st[felts][{ name := "%53" }] ←
                        Option.get! (State.felts st { name := "%52" }) *
                          Option.get! (State.felts st { name := "%7" }))[felts][{ name := "%54" }] ←
                      Option.get!
                          ((st.felts[{ name := "%53" }] ←ₘ
                              Option.get! (State.felts st { name := "%52" }) *
                                Option.get! (State.felts st { name := "%7" }))
                            { name := "%51" }) +
                        Option.get! (State.felts st { name := "%52" }) *
                          Option.get! (State.felts st { name := "%7" }))["%55"] ←ₛ
                    getImpl st { name := "data" } 0 13)
                  { name := "%55" }) *
              Option.get!
                (State.felts
                  (((st[felts][{ name := "%53" }] ←
                        Option.get! (State.felts st { name := "%52" }) *
                          Option.get! (State.felts st { name := "%7" }))[felts][{ name := "%54" }] ←
                      Option.get!
                          ((st.felts[{ name := "%53" }] ←ₘ
                              Option.get! (State.felts st { name := "%52" }) *
                                Option.get! (State.felts st { name := "%7" }))
                            { name := "%51" }) +
                        Option.get! (State.felts st { name := "%52" }) *
                          Option.get! (State.felts st { name := "%7" }))["%55"] ←ₛ
                    getImpl st { name := "data" } 0 13)
                  {
                    name :=
                      "%6" })) 

-- Run the program from part28 onwards by using part28_state rather than Code.part28
def part28_state_update (st: State): State :=
  Γ (part28_state st) ⟦Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part28_state for Code.part28 produces the same result
lemma part28_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part28_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part28
  MLIR
  rewrite [←eq]
  unfold part28_state_update part28_state
  rfl

lemma part28_updates_opaque {st : State} : 
  Code.getReturn (part27_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part28_state_update (part27_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part27_state_update, part28_wp]

end Risc0.OneHot20.Witness.WP