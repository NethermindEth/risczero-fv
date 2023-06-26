import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart46

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part47 on st
def part47_state (st: State) : State :=
  
          { buffers := st.buffers, bufferWidths := st.bufferWidths,
            constraints :=
              (Option.get!
                      (((st.felts[{ name := "%115" }] ←ₘ
                            Option.get! (State.felts st { name := "%112" }) +
                              Option.get! (State.felts st { name := "%52" }))[{ name := "%116" }] ←ₘ
                          Option.get!
                              ((st.felts[{ name := "%115" }] ←ₘ
                                  Option.get! (State.felts st { name := "%112" }) +
                                    Option.get! (State.felts st { name := "%52" }))
                                { name := "%18" }) -
                            Option.get!
                              ((st.felts[{ name := "%115" }] ←ₘ
                                  Option.get! (State.felts st { name := "%112" }) +
                                    Option.get! (State.felts st { name := "%52" }))
                                { name := "%55" }))
                        { name := "%55" }) =
                    0 ∨
                  Option.get!
                        ((st.felts[{ name := "%115" }] ←ₘ
                            Option.get! (State.felts st { name := "%112" }) +
                              Option.get! (State.felts st { name := "%52" }))
                          { name := "%18" }) -
                      Option.get!
                        ((st.felts[{ name := "%115" }] ←ₘ
                            Option.get! (State.felts st { name := "%112" }) +
                              Option.get! (State.felts st { name := "%52" }))
                          { name := "%55" }) =
                    0) ::
                st.constraints,
            cycle := st.cycle,
            felts :=
              ((st.felts[{ name := "%115" }] ←ₘ
                    Option.get! (State.felts st { name := "%112" }) +
                      Option.get! (State.felts st { name := "%52" }))[{ name := "%116" }] ←ₘ
                  Option.get!
                      ((st.felts[{ name := "%115" }] ←ₘ
                          Option.get! (State.felts st { name := "%112" }) +
                            Option.get! (State.felts st { name := "%52" }))
                        { name := "%18" }) -
                    Option.get!
                      ((st.felts[{ name := "%115" }] ←ₘ
                          Option.get! (State.felts st { name := "%112" }) +
                            Option.get! (State.felts st { name := "%52" }))
                        { name := "%55" }))[{ name := "%117" }] ←ₘ
                Option.get!
                    (((st.felts[{ name := "%115" }] ←ₘ
                          Option.get! (State.felts st { name := "%112" }) +
                            Option.get! (State.felts st { name := "%52" }))[{ name := "%116" }] ←ₘ
                        Option.get!
                            ((st.felts[{ name := "%115" }] ←ₘ
                                Option.get! (State.felts st { name := "%112" }) +
                                  Option.get! (State.felts st { name := "%52" }))
                              { name := "%18" }) -
                          Option.get!
                            ((st.felts[{ name := "%115" }] ←ₘ
                                Option.get! (State.felts st { name := "%112" }) +
                                  Option.get! (State.felts st { name := "%52" }))
                              { name := "%55" }))
                      { name := "%55" }) *
                  (Option.get!
                      ((st.felts[{ name := "%115" }] ←ₘ
                          Option.get! (State.felts st { name := "%112" }) +
                            Option.get! (State.felts st { name := "%52" }))
                        { name := "%18" }) -
                    Option.get!
                      ((st.felts[{ name := "%115" }] ←ₘ
                          Option.get! (State.felts st { name := "%112" }) +
                            Option.get! (State.felts st { name := "%52" }))
                        { name := "%55" })),
            isFailed := st.isFailed, props := st.props,
            vars :=
              st.vars } 

-- Run the program from part47 onwards by using part47_state rather than Code.part47
def part47_state_update (st: State): State :=
  Γ (part47_state st) ⟦Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part47_state for Code.part47 produces the same result
lemma part47_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part47_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part47
  MLIR
  rewrite [←eq]
  unfold part47_state_update part47_state
  rfl

lemma part47_updates_opaque {st : State} : 
  Code.getReturn (part46_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part47_state_update (part46_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part46_state_update, part47_wp]

end Risc0.OneHot20.Witness.WP