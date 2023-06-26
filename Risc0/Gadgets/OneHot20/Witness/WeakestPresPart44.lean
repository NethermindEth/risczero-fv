import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart43

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part44 on st
def part44_state (st: State) : State :=
  
          { buffers := st.buffers, bufferWidths := st.bufferWidths,
            constraints :=
              (Option.get!
                      (((st.felts[{ name := "%106" }] ←ₘ
                            Option.get! (State.felts st { name := "%103" }) +
                              Option.get! (State.felts st { name := "%43" }))[{ name := "%107" }] ←ₘ
                          Option.get!
                              ((st.felts[{ name := "%106" }] ←ₘ
                                  Option.get! (State.felts st { name := "%103" }) +
                                    Option.get! (State.felts st { name := "%43" }))
                                { name := "%18" }) -
                            Option.get!
                              ((st.felts[{ name := "%106" }] ←ₘ
                                  Option.get! (State.felts st { name := "%103" }) +
                                    Option.get! (State.felts st { name := "%43" }))
                                { name := "%46" }))
                        { name := "%46" }) =
                    0 ∨
                  Option.get!
                        ((st.felts[{ name := "%106" }] ←ₘ
                            Option.get! (State.felts st { name := "%103" }) +
                              Option.get! (State.felts st { name := "%43" }))
                          { name := "%18" }) -
                      Option.get!
                        ((st.felts[{ name := "%106" }] ←ₘ
                            Option.get! (State.felts st { name := "%103" }) +
                              Option.get! (State.felts st { name := "%43" }))
                          { name := "%46" }) =
                    0) ::
                st.constraints,
            cycle := st.cycle,
            felts :=
              ((st.felts[{ name := "%106" }] ←ₘ
                    Option.get! (State.felts st { name := "%103" }) +
                      Option.get! (State.felts st { name := "%43" }))[{ name := "%107" }] ←ₘ
                  Option.get!
                      ((st.felts[{ name := "%106" }] ←ₘ
                          Option.get! (State.felts st { name := "%103" }) +
                            Option.get! (State.felts st { name := "%43" }))
                        { name := "%18" }) -
                    Option.get!
                      ((st.felts[{ name := "%106" }] ←ₘ
                          Option.get! (State.felts st { name := "%103" }) +
                            Option.get! (State.felts st { name := "%43" }))
                        { name := "%46" }))[{ name := "%108" }] ←ₘ
                Option.get!
                    (((st.felts[{ name := "%106" }] ←ₘ
                          Option.get! (State.felts st { name := "%103" }) +
                            Option.get! (State.felts st { name := "%43" }))[{ name := "%107" }] ←ₘ
                        Option.get!
                            ((st.felts[{ name := "%106" }] ←ₘ
                                Option.get! (State.felts st { name := "%103" }) +
                                  Option.get! (State.felts st { name := "%43" }))
                              { name := "%18" }) -
                          Option.get!
                            ((st.felts[{ name := "%106" }] ←ₘ
                                Option.get! (State.felts st { name := "%103" }) +
                                  Option.get! (State.felts st { name := "%43" }))
                              { name := "%46" }))
                      { name := "%46" }) *
                  (Option.get!
                      ((st.felts[{ name := "%106" }] ←ₘ
                          Option.get! (State.felts st { name := "%103" }) +
                            Option.get! (State.felts st { name := "%43" }))
                        { name := "%18" }) -
                    Option.get!
                      ((st.felts[{ name := "%106" }] ←ₘ
                          Option.get! (State.felts st { name := "%103" }) +
                            Option.get! (State.felts st { name := "%43" }))
                        { name := "%46" })),
            isFailed := st.isFailed, props := st.props,
            vars :=
              st.vars } 

-- Run the program from part44 onwards by using part44_state rather than Code.part44
def part44_state_update (st: State): State :=
  Γ (part44_state st) ⟦Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part44_state for Code.part44 produces the same result
lemma part44_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part44_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part44
  MLIR
  rewrite [←eq]
  unfold part44_state_update part44_state
  rfl

lemma part44_updates_opaque {st : State} : 
  Code.getReturn (part43_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part44_state_update (part43_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part43_state_update, part44_wp]

end Risc0.OneHot20.Witness.WP