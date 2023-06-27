import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart48

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part49 on st
def part49_state (st: State) : State :=
  
          (withEqZero
            (Option.get!
                (((st.felts[{ name := "%121" }] ←ₘ
                      Option.get! (State.felts st { name := "%118" }) +
                        Option.get! (State.felts st { name := "%58" }))[{ name := "%122" }] ←ₘ
                    Option.get!
                        ((st.felts[{ name := "%121" }] ←ₘ
                            Option.get! (State.felts st { name := "%118" }) +
                              Option.get! (State.felts st { name := "%58" }))
                          { name := "%18" }) -
                      Option.get!
                        ((st.felts[{ name := "%121" }] ←ₘ
                            Option.get! (State.felts st { name := "%118" }) +
                              Option.get! (State.felts st { name := "%58" }))
                          { name := "%61" }))
                  { name := "%61" }) *
              (Option.get!
                  ((st.felts[{ name := "%121" }] ←ₘ
                      Option.get! (State.felts st { name := "%118" }) + Option.get! (State.felts st { name := "%58" }))
                    { name := "%18" }) -
                Option.get!
                  ((st.felts[{ name := "%121" }] ←ₘ
                      Option.get! (State.felts st { name := "%118" }) + Option.get! (State.felts st { name := "%58" }))
                    { name := "%61" })))
            (((st[felts][{ name := "%121" }] ←
                  Option.get! (State.felts st { name := "%118" }) +
                    Option.get! (State.felts st { name := "%58" }))[felts][{ name := "%122" }] ←
                Option.get!
                    ((st.felts[{ name := "%121" }] ←ₘ
                        Option.get! (State.felts st { name := "%118" }) +
                          Option.get! (State.felts st { name := "%58" }))
                      { name := "%18" }) -
                  Option.get!
                    ((st.felts[{ name := "%121" }] ←ₘ
                        Option.get! (State.felts st { name := "%118" }) +
                          Option.get! (State.felts st { name := "%58" }))
                      { name := "%61" }))[felts][{ name := "%123" }] ←
              Option.get!
                  (((st.felts[{ name := "%121" }] ←ₘ
                        Option.get! (State.felts st { name := "%118" }) +
                          Option.get! (State.felts st { name := "%58" }))[{ name := "%122" }] ←ₘ
                      Option.get!
                          ((st.felts[{ name := "%121" }] ←ₘ
                              Option.get! (State.felts st { name := "%118" }) +
                                Option.get! (State.felts st { name := "%58" }))
                            { name := "%18" }) -
                        Option.get!
                          ((st.felts[{ name := "%121" }] ←ₘ
                              Option.get! (State.felts st { name := "%118" }) +
                                Option.get! (State.felts st { name := "%58" }))
                            { name := "%61" }))
                    { name := "%61" }) *
                (Option.get!
                    ((st.felts[{ name := "%121" }] ←ₘ
                        Option.get! (State.felts st { name := "%118" }) +
                          Option.get! (State.felts st { name := "%58" }))
                      { name := "%18" }) -
                  Option.get!
                    ((st.felts[{ name := "%121" }] ←ₘ
                        Option.get! (State.felts st { name := "%118" }) +
                          Option.get! (State.felts st { name := "%58" }))
                      { name := "%61" })))) 

-- Run the program from part49 onwards by using part49_state rather than Code.part49
def part49_state_update (st: State): State :=
  Γ (part49_state st) ⟦Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part49_state for Code.part49 produces the same result
lemma part49_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part49_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part49
  MLIR
  rewrite [←eq]
  unfold part49_state_update part49_state
  rfl

lemma part49_updates_opaque {st : State} : 
  Code.getReturn (part48_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part49_state_update (part48_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part48_state_update, part49_wp]

end Risc0.OneHot20.Witness.WP