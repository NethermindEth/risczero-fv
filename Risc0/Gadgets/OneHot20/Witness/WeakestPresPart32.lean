import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart31

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part32 on st
def part32_state (st: State) : State :=
  
          ((((st[felts][{ name := "%69" }] ←
                  Option.get! (State.felts st { name := "%66" }) +
                    Option.get! (State.felts st { name := "%68" }))["%70"] ←ₛ
                getImpl st { name := "data" } 0 18)[felts][{ name := "%71" }] ←
              Option.get!
                  (State.felts
                    ((st[felts][{ name := "%69" }] ←
                        Option.get! (State.felts st { name := "%66" }) +
                          Option.get! (State.felts st { name := "%68" }))["%70"] ←ₛ
                      getImpl st { name := "data" } 0 18)
                    { name := "%70" }) *
                Option.get!
                  (State.felts
                    ((st[felts][{ name := "%69" }] ←
                        Option.get! (State.felts st { name := "%66" }) +
                          Option.get! (State.felts st { name := "%68" }))["%70"] ←ₛ
                      getImpl st { name := "data" } 0 18)
                    { name := "%1" }))[felts][{ name := "%72" }] ←
            Option.get!
                ((((st[felts][{ name := "%69" }] ←
                          Option.get! (State.felts st { name := "%66" }) +
                            Option.get! (State.felts st { name := "%68" }))["%70"] ←ₛ
                        getImpl st { name := "data" } 0 18).felts[{ name := "%71" }] ←ₘ
                    Option.get!
                        (State.felts
                          ((st[felts][{ name := "%69" }] ←
                              Option.get! (State.felts st { name := "%66" }) +
                                Option.get! (State.felts st { name := "%68" }))["%70"] ←ₛ
                            getImpl st { name := "data" } 0 18)
                          { name := "%70" }) *
                      Option.get!
                        (State.felts
                          ((st[felts][{ name := "%69" }] ←
                              Option.get! (State.felts st { name := "%66" }) +
                                Option.get! (State.felts st { name := "%68" }))["%70"] ←ₛ
                            getImpl st { name := "data" } 0 18)
                          { name := "%1" }))
                  { name := "%69" }) +
              Option.get!
                  (State.felts
                    ((st[felts][{ name := "%69" }] ←
                        Option.get! (State.felts st { name := "%66" }) +
                          Option.get! (State.felts st { name := "%68" }))["%70"] ←ₛ
                      getImpl st { name := "data" } 0 18)
                    { name := "%70" }) *
                Option.get!
                  (State.felts
                    ((st[felts][{ name := "%69" }] ←
                        Option.get! (State.felts st { name := "%66" }) +
                          Option.get! (State.felts st { name := "%68" }))["%70"] ←ₛ
                      getImpl st { name := "data" } 0 18)
                    {
                      name :=
                        "%1" })) 

-- Run the program from part32 onwards by using part32_state rather than Code.part32
def part32_state_update (st: State): State :=
  Γ (part32_state st) ⟦Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part32_state for Code.part32 produces the same result
lemma part32_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part32_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part32
  MLIR
  rewrite [←eq]
  unfold part32_state_update part32_state
  rfl

lemma part32_updates_opaque {st : State} : 
  Code.getReturn (part31_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part32_state_update (part31_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part31_state_update, part32_wp]

end Risc0.OneHot20.Witness.WP