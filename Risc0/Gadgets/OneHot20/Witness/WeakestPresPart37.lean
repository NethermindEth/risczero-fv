import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart36

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part37 on st
def part37_state (st: State) : State :=
  
          (withEqZero
            (Option.get!
                (((st.felts[{ name := "%85" }] ←ₘ
                      Option.get! (State.felts st { name := "%82" }) +
                        Option.get! (State.felts st { name := "%22" }))[{ name := "%86" }] ←ₘ
                    Option.get!
                        ((st.felts[{ name := "%85" }] ←ₘ
                            Option.get! (State.felts st { name := "%82" }) +
                              Option.get! (State.felts st { name := "%22" }))
                          { name := "%18" }) -
                      Option.get!
                        ((st.felts[{ name := "%85" }] ←ₘ
                            Option.get! (State.felts st { name := "%82" }) +
                              Option.get! (State.felts st { name := "%22" }))
                          { name := "%25" }))
                  { name := "%25" }) *
              (Option.get!
                  ((st.felts[{ name := "%85" }] ←ₘ
                      Option.get! (State.felts st { name := "%82" }) + Option.get! (State.felts st { name := "%22" }))
                    { name := "%18" }) -
                Option.get!
                  ((st.felts[{ name := "%85" }] ←ₘ
                      Option.get! (State.felts st { name := "%82" }) + Option.get! (State.felts st { name := "%22" }))
                    { name := "%25" })))
            (((st[felts][{ name := "%85" }] ←
                  Option.get! (State.felts st { name := "%82" }) +
                    Option.get! (State.felts st { name := "%22" }))[felts][{ name := "%86" }] ←
                Option.get!
                    ((st.felts[{ name := "%85" }] ←ₘ
                        Option.get! (State.felts st { name := "%82" }) + Option.get! (State.felts st { name := "%22" }))
                      { name := "%18" }) -
                  Option.get!
                    ((st.felts[{ name := "%85" }] ←ₘ
                        Option.get! (State.felts st { name := "%82" }) + Option.get! (State.felts st { name := "%22" }))
                      { name := "%25" }))[felts][{ name := "%87" }] ←
              Option.get!
                  (((st.felts[{ name := "%85" }] ←ₘ
                        Option.get! (State.felts st { name := "%82" }) +
                          Option.get! (State.felts st { name := "%22" }))[{ name := "%86" }] ←ₘ
                      Option.get!
                          ((st.felts[{ name := "%85" }] ←ₘ
                              Option.get! (State.felts st { name := "%82" }) +
                                Option.get! (State.felts st { name := "%22" }))
                            { name := "%18" }) -
                        Option.get!
                          ((st.felts[{ name := "%85" }] ←ₘ
                              Option.get! (State.felts st { name := "%82" }) +
                                Option.get! (State.felts st { name := "%22" }))
                            { name := "%25" }))
                    { name := "%25" }) *
                (Option.get!
                    ((st.felts[{ name := "%85" }] ←ₘ
                        Option.get! (State.felts st { name := "%82" }) + Option.get! (State.felts st { name := "%22" }))
                      { name := "%18" }) -
                  Option.get!
                    ((st.felts[{ name := "%85" }] ←ₘ
                        Option.get! (State.felts st { name := "%82" }) + Option.get! (State.felts st { name := "%22" }))
                      {
                        name :=
                          "%25" })))) 

-- Run the program from part37 onwards by using part37_state rather than Code.part37
def part37_state_update (st: State): State :=
  Γ (part37_state st) ⟦Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part37_state for Code.part37 produces the same result
lemma part37_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part37_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part37
  MLIR
  rewrite [←eq]
  unfold part37_state_update part37_state
  rfl

lemma part37_updates_opaque {st : State} : 
  Code.getReturn (part36_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part37_state_update (part36_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part36_state_update, part37_wp]

end Risc0.OneHot20.Witness.WP