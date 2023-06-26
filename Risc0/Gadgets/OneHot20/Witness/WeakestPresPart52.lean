import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart51

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part52 on st
def part52_state (st: State) : State :=
  
          { buffers := st.buffers, bufferWidths := st.bufferWidths,
            constraints :=
              (Option.get!
                      (((st.felts[{ name := "%130" }] ←ₘ
                            Option.get! (State.felts st { name := "%127" }) +
                              Option.get! (State.felts st { name := "%67" }))[{ name := "%131" }] ←ₘ
                          Option.get!
                              ((st.felts[{ name := "%130" }] ←ₘ
                                  Option.get! (State.felts st { name := "%127" }) +
                                    Option.get! (State.felts st { name := "%67" }))
                                { name := "%18" }) -
                            Option.get!
                              ((st.felts[{ name := "%130" }] ←ₘ
                                  Option.get! (State.felts st { name := "%127" }) +
                                    Option.get! (State.felts st { name := "%67" }))
                                { name := "%70" }))
                        { name := "%70" }) =
                    0 ∨
                  Option.get!
                        ((st.felts[{ name := "%130" }] ←ₘ
                            Option.get! (State.felts st { name := "%127" }) +
                              Option.get! (State.felts st { name := "%67" }))
                          { name := "%18" }) -
                      Option.get!
                        ((st.felts[{ name := "%130" }] ←ₘ
                            Option.get! (State.felts st { name := "%127" }) +
                              Option.get! (State.felts st { name := "%67" }))
                          { name := "%70" }) =
                    0) ::
                st.constraints,
            cycle := st.cycle,
            felts :=
              ((st.felts[{ name := "%130" }] ←ₘ
                    Option.get! (State.felts st { name := "%127" }) +
                      Option.get! (State.felts st { name := "%67" }))[{ name := "%131" }] ←ₘ
                  Option.get!
                      ((st.felts[{ name := "%130" }] ←ₘ
                          Option.get! (State.felts st { name := "%127" }) +
                            Option.get! (State.felts st { name := "%67" }))
                        { name := "%18" }) -
                    Option.get!
                      ((st.felts[{ name := "%130" }] ←ₘ
                          Option.get! (State.felts st { name := "%127" }) +
                            Option.get! (State.felts st { name := "%67" }))
                        { name := "%70" }))[{ name := "%132" }] ←ₘ
                Option.get!
                    (((st.felts[{ name := "%130" }] ←ₘ
                          Option.get! (State.felts st { name := "%127" }) +
                            Option.get! (State.felts st { name := "%67" }))[{ name := "%131" }] ←ₘ
                        Option.get!
                            ((st.felts[{ name := "%130" }] ←ₘ
                                Option.get! (State.felts st { name := "%127" }) +
                                  Option.get! (State.felts st { name := "%67" }))
                              { name := "%18" }) -
                          Option.get!
                            ((st.felts[{ name := "%130" }] ←ₘ
                                Option.get! (State.felts st { name := "%127" }) +
                                  Option.get! (State.felts st { name := "%67" }))
                              { name := "%70" }))
                      { name := "%70" }) *
                  (Option.get!
                      ((st.felts[{ name := "%130" }] ←ₘ
                          Option.get! (State.felts st { name := "%127" }) +
                            Option.get! (State.felts st { name := "%67" }))
                        { name := "%18" }) -
                    Option.get!
                      ((st.felts[{ name := "%130" }] ←ₘ
                          Option.get! (State.felts st { name := "%127" }) +
                            Option.get! (State.felts st { name := "%67" }))
                        { name := "%70" })),
            isFailed := st.isFailed, props := st.props, vars := st.vars } 

-- Run the program from part52 onwards by using part52_state rather than Code.part52
def part52_state_update (st: State): State :=
  Γ (part52_state st) ⟦Code.part53; Code.part54⟧

-- Prove that substituting part52_state for Code.part52 produces the same result
lemma part52_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part52_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part53; Code.part54) = prog
  unfold Code.part52
  MLIR
  rewrite [←eq]
  unfold part52_state_update part52_state
  rfl

lemma part52_updates_opaque {st : State} : 
  Code.getReturn (part51_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part52_state_update (part51_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part51_state_update, part52_wp]

end Risc0.OneHot20.Witness.WP