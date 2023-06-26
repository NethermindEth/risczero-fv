import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart35

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part36 on st
def part36_state (st: State) : State :=
  
          { buffers := st.buffers, bufferWidths := st.bufferWidths,
            constraints :=
              (Option.get!
                      (((st.felts[{ name := "%82" }] ←ₘ
                            Option.get! (State.felts st { name := "%77" }) +
                              Option.get! (State.felts st { name := "%21" }))[{ name := "%83" }] ←ₘ
                          Option.get!
                              ((st.felts[{ name := "%82" }] ←ₘ
                                  Option.get! (State.felts st { name := "%77" }) +
                                    Option.get! (State.felts st { name := "%21" }))
                                { name := "%18" }) -
                            Option.get!
                              ((st.felts[{ name := "%82" }] ←ₘ
                                  Option.get! (State.felts st { name := "%77" }) +
                                    Option.get! (State.felts st { name := "%21" }))
                                { name := "%22" }))
                        { name := "%22" }) =
                    0 ∨
                  Option.get!
                        ((st.felts[{ name := "%82" }] ←ₘ
                            Option.get! (State.felts st { name := "%77" }) +
                              Option.get! (State.felts st { name := "%21" }))
                          { name := "%18" }) -
                      Option.get!
                        ((st.felts[{ name := "%82" }] ←ₘ
                            Option.get! (State.felts st { name := "%77" }) +
                              Option.get! (State.felts st { name := "%21" }))
                          { name := "%22" }) =
                    0) ::
                st.constraints,
            cycle := st.cycle,
            felts :=
              ((st.felts[{ name := "%82" }] ←ₘ
                    Option.get! (State.felts st { name := "%77" }) +
                      Option.get! (State.felts st { name := "%21" }))[{ name := "%83" }] ←ₘ
                  Option.get!
                      ((st.felts[{ name := "%82" }] ←ₘ
                          Option.get! (State.felts st { name := "%77" }) +
                            Option.get! (State.felts st { name := "%21" }))
                        { name := "%18" }) -
                    Option.get!
                      ((st.felts[{ name := "%82" }] ←ₘ
                          Option.get! (State.felts st { name := "%77" }) +
                            Option.get! (State.felts st { name := "%21" }))
                        { name := "%22" }))[{ name := "%84" }] ←ₘ
                Option.get!
                    (((st.felts[{ name := "%82" }] ←ₘ
                          Option.get! (State.felts st { name := "%77" }) +
                            Option.get! (State.felts st { name := "%21" }))[{ name := "%83" }] ←ₘ
                        Option.get!
                            ((st.felts[{ name := "%82" }] ←ₘ
                                Option.get! (State.felts st { name := "%77" }) +
                                  Option.get! (State.felts st { name := "%21" }))
                              { name := "%18" }) -
                          Option.get!
                            ((st.felts[{ name := "%82" }] ←ₘ
                                Option.get! (State.felts st { name := "%77" }) +
                                  Option.get! (State.felts st { name := "%21" }))
                              { name := "%22" }))
                      { name := "%22" }) *
                  (Option.get!
                      ((st.felts[{ name := "%82" }] ←ₘ
                          Option.get! (State.felts st { name := "%77" }) +
                            Option.get! (State.felts st { name := "%21" }))
                        { name := "%18" }) -
                    Option.get!
                      ((st.felts[{ name := "%82" }] ←ₘ
                          Option.get! (State.felts st { name := "%77" }) +
                            Option.get! (State.felts st { name := "%21" }))
                        { name := "%22" })),
            isFailed := st.isFailed, props := st.props,
            vars :=
              st.vars } 

-- Run the program from part36 onwards by using part36_state rather than Code.part36
def part36_state_update (st: State): State :=
  Γ (part36_state st) ⟦Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part36_state for Code.part36 produces the same result
lemma part36_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part36_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part36
  MLIR
  rewrite [←eq]
  unfold part36_state_update part36_state
  rfl

lemma part36_updates_opaque {st : State} : 
  Code.getReturn (part35_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part36_state_update (part35_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part35_state_update, part36_wp]

end Risc0.OneHot20.Witness.WP