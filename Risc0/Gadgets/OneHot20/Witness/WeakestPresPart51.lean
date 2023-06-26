import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart50

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part51 on st
def part51_state (st: State) : State :=
  
          { buffers := st.buffers, bufferWidths := st.bufferWidths,
            constraints :=
              (Option.get!
                      (((st.felts[{ name := "%127" }] ←ₘ
                            Option.get! (State.felts st { name := "%124" }) +
                              Option.get! (State.felts st { name := "%64" }))[{ name := "%128" }] ←ₘ
                          Option.get!
                              ((st.felts[{ name := "%127" }] ←ₘ
                                  Option.get! (State.felts st { name := "%124" }) +
                                    Option.get! (State.felts st { name := "%64" }))
                                { name := "%18" }) -
                            Option.get!
                              ((st.felts[{ name := "%127" }] ←ₘ
                                  Option.get! (State.felts st { name := "%124" }) +
                                    Option.get! (State.felts st { name := "%64" }))
                                { name := "%67" }))
                        { name := "%67" }) =
                    0 ∨
                  Option.get!
                        ((st.felts[{ name := "%127" }] ←ₘ
                            Option.get! (State.felts st { name := "%124" }) +
                              Option.get! (State.felts st { name := "%64" }))
                          { name := "%18" }) -
                      Option.get!
                        ((st.felts[{ name := "%127" }] ←ₘ
                            Option.get! (State.felts st { name := "%124" }) +
                              Option.get! (State.felts st { name := "%64" }))
                          { name := "%67" }) =
                    0) ::
                st.constraints,
            cycle := st.cycle,
            felts :=
              ((st.felts[{ name := "%127" }] ←ₘ
                    Option.get! (State.felts st { name := "%124" }) +
                      Option.get! (State.felts st { name := "%64" }))[{ name := "%128" }] ←ₘ
                  Option.get!
                      ((st.felts[{ name := "%127" }] ←ₘ
                          Option.get! (State.felts st { name := "%124" }) +
                            Option.get! (State.felts st { name := "%64" }))
                        { name := "%18" }) -
                    Option.get!
                      ((st.felts[{ name := "%127" }] ←ₘ
                          Option.get! (State.felts st { name := "%124" }) +
                            Option.get! (State.felts st { name := "%64" }))
                        { name := "%67" }))[{ name := "%129" }] ←ₘ
                Option.get!
                    (((st.felts[{ name := "%127" }] ←ₘ
                          Option.get! (State.felts st { name := "%124" }) +
                            Option.get! (State.felts st { name := "%64" }))[{ name := "%128" }] ←ₘ
                        Option.get!
                            ((st.felts[{ name := "%127" }] ←ₘ
                                Option.get! (State.felts st { name := "%124" }) +
                                  Option.get! (State.felts st { name := "%64" }))
                              { name := "%18" }) -
                          Option.get!
                            ((st.felts[{ name := "%127" }] ←ₘ
                                Option.get! (State.felts st { name := "%124" }) +
                                  Option.get! (State.felts st { name := "%64" }))
                              { name := "%67" }))
                      { name := "%67" }) *
                  (Option.get!
                      ((st.felts[{ name := "%127" }] ←ₘ
                          Option.get! (State.felts st { name := "%124" }) +
                            Option.get! (State.felts st { name := "%64" }))
                        { name := "%18" }) -
                    Option.get!
                      ((st.felts[{ name := "%127" }] ←ₘ
                          Option.get! (State.felts st { name := "%124" }) +
                            Option.get! (State.felts st { name := "%64" }))
                        { name := "%67" })),
            isFailed := st.isFailed, props := st.props, vars := st.vars } 

-- Run the program from part51 onwards by using part51_state rather than Code.part51
def part51_state_update (st: State): State :=
  Γ (part51_state st) ⟦Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part51_state for Code.part51 produces the same result
lemma part51_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part51_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part51
  MLIR
  rewrite [←eq]
  unfold part51_state_update part51_state
  rfl

lemma part51_updates_opaque {st : State} : 
  Code.getReturn (part50_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part51_state_update (part50_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part50_state_update, part51_wp]

end Risc0.OneHot20.Witness.WP