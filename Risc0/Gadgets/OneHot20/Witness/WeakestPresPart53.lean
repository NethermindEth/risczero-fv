import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart52

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part53 on st
def part53_state (st: State) : State :=
  
          { buffers := st.buffers, bufferWidths := st.bufferWidths,
            constraints :=
              (Option.get!
                      (((st.felts[{ name := "%133" }] ←ₘ
                            Option.get! (State.felts st { name := "%130" }) +
                              Option.get! (State.felts st { name := "%70" }))[{ name := "%134" }] ←ₘ
                          Option.get!
                              ((st.felts[{ name := "%133" }] ←ₘ
                                  Option.get! (State.felts st { name := "%130" }) +
                                    Option.get! (State.felts st { name := "%70" }))
                                { name := "%18" }) -
                            Option.get!
                              ((st.felts[{ name := "%133" }] ←ₘ
                                  Option.get! (State.felts st { name := "%130" }) +
                                    Option.get! (State.felts st { name := "%70" }))
                                { name := "%73" }))
                        { name := "%73" }) =
                    0 ∨
                  Option.get!
                        ((st.felts[{ name := "%133" }] ←ₘ
                            Option.get! (State.felts st { name := "%130" }) +
                              Option.get! (State.felts st { name := "%70" }))
                          { name := "%18" }) -
                      Option.get!
                        ((st.felts[{ name := "%133" }] ←ₘ
                            Option.get! (State.felts st { name := "%130" }) +
                              Option.get! (State.felts st { name := "%70" }))
                          { name := "%73" }) =
                    0) ::
                st.constraints,
            cycle := st.cycle,
            felts :=
              ((st.felts[{ name := "%133" }] ←ₘ
                    Option.get! (State.felts st { name := "%130" }) +
                      Option.get! (State.felts st { name := "%70" }))[{ name := "%134" }] ←ₘ
                  Option.get!
                      ((st.felts[{ name := "%133" }] ←ₘ
                          Option.get! (State.felts st { name := "%130" }) +
                            Option.get! (State.felts st { name := "%70" }))
                        { name := "%18" }) -
                    Option.get!
                      ((st.felts[{ name := "%133" }] ←ₘ
                          Option.get! (State.felts st { name := "%130" }) +
                            Option.get! (State.felts st { name := "%70" }))
                        { name := "%73" }))[{ name := "%135" }] ←ₘ
                Option.get!
                    (((st.felts[{ name := "%133" }] ←ₘ
                          Option.get! (State.felts st { name := "%130" }) +
                            Option.get! (State.felts st { name := "%70" }))[{ name := "%134" }] ←ₘ
                        Option.get!
                            ((st.felts[{ name := "%133" }] ←ₘ
                                Option.get! (State.felts st { name := "%130" }) +
                                  Option.get! (State.felts st { name := "%70" }))
                              { name := "%18" }) -
                          Option.get!
                            ((st.felts[{ name := "%133" }] ←ₘ
                                Option.get! (State.felts st { name := "%130" }) +
                                  Option.get! (State.felts st { name := "%70" }))
                              { name := "%73" }))
                      { name := "%73" }) *
                  (Option.get!
                      ((st.felts[{ name := "%133" }] ←ₘ
                          Option.get! (State.felts st { name := "%130" }) +
                            Option.get! (State.felts st { name := "%70" }))
                        { name := "%18" }) -
                    Option.get!
                      ((st.felts[{ name := "%133" }] ←ₘ
                          Option.get! (State.felts st { name := "%130" }) +
                            Option.get! (State.felts st { name := "%70" }))
                        { name := "%73" })),
            isFailed := st.isFailed, props := st.props, vars := st.vars } 

-- Run the program from part53 onwards by using part53_state rather than Code.part53
def part53_state_update (st: State): State :=
  Γ (part53_state st) ⟦Code.part54⟧

-- Prove that substituting part53_state for Code.part53 produces the same result
lemma part53_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part53_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part54) = prog
  unfold Code.part53
  MLIR
  rewrite [←eq]
  unfold part53_state_update part53_state
  rfl

lemma part53_updates_opaque {st : State} : 
  Code.getReturn (part52_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part53_state_update (part52_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part52_state_update, part53_wp]

end Risc0.OneHot20.Witness.WP