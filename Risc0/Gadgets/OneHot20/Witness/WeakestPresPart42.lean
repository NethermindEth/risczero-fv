import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart41

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part42 on st
def part42_state (st: State) : State :=
  
          { buffers := st.buffers, bufferWidths := st.bufferWidths,
            constraints :=
              (Option.get!
                      (((st.felts[{ name := "%100" }] ←ₘ
                            Option.get! (State.felts st { name := "%97" }) +
                              Option.get! (State.felts st { name := "%37" }))[{ name := "%101" }] ←ₘ
                          Option.get!
                              ((st.felts[{ name := "%100" }] ←ₘ
                                  Option.get! (State.felts st { name := "%97" }) +
                                    Option.get! (State.felts st { name := "%37" }))
                                { name := "%18" }) -
                            Option.get!
                              ((st.felts[{ name := "%100" }] ←ₘ
                                  Option.get! (State.felts st { name := "%97" }) +
                                    Option.get! (State.felts st { name := "%37" }))
                                { name := "%40" }))
                        { name := "%40" }) =
                    0 ∨
                  Option.get!
                        ((st.felts[{ name := "%100" }] ←ₘ
                            Option.get! (State.felts st { name := "%97" }) +
                              Option.get! (State.felts st { name := "%37" }))
                          { name := "%18" }) -
                      Option.get!
                        ((st.felts[{ name := "%100" }] ←ₘ
                            Option.get! (State.felts st { name := "%97" }) +
                              Option.get! (State.felts st { name := "%37" }))
                          { name := "%40" }) =
                    0) ::
                st.constraints,
            cycle := st.cycle,
            felts :=
              ((st.felts[{ name := "%100" }] ←ₘ
                    Option.get! (State.felts st { name := "%97" }) +
                      Option.get! (State.felts st { name := "%37" }))[{ name := "%101" }] ←ₘ
                  Option.get!
                      ((st.felts[{ name := "%100" }] ←ₘ
                          Option.get! (State.felts st { name := "%97" }) +
                            Option.get! (State.felts st { name := "%37" }))
                        { name := "%18" }) -
                    Option.get!
                      ((st.felts[{ name := "%100" }] ←ₘ
                          Option.get! (State.felts st { name := "%97" }) +
                            Option.get! (State.felts st { name := "%37" }))
                        { name := "%40" }))[{ name := "%102" }] ←ₘ
                Option.get!
                    (((st.felts[{ name := "%100" }] ←ₘ
                          Option.get! (State.felts st { name := "%97" }) +
                            Option.get! (State.felts st { name := "%37" }))[{ name := "%101" }] ←ₘ
                        Option.get!
                            ((st.felts[{ name := "%100" }] ←ₘ
                                Option.get! (State.felts st { name := "%97" }) +
                                  Option.get! (State.felts st { name := "%37" }))
                              { name := "%18" }) -
                          Option.get!
                            ((st.felts[{ name := "%100" }] ←ₘ
                                Option.get! (State.felts st { name := "%97" }) +
                                  Option.get! (State.felts st { name := "%37" }))
                              { name := "%40" }))
                      { name := "%40" }) *
                  (Option.get!
                      ((st.felts[{ name := "%100" }] ←ₘ
                          Option.get! (State.felts st { name := "%97" }) +
                            Option.get! (State.felts st { name := "%37" }))
                        { name := "%18" }) -
                    Option.get!
                      ((st.felts[{ name := "%100" }] ←ₘ
                          Option.get! (State.felts st { name := "%97" }) +
                            Option.get! (State.felts st { name := "%37" }))
                        { name := "%40" })),
            isFailed := st.isFailed, props := st.props,
            vars :=
              st.vars } 

-- Run the program from part42 onwards by using part42_state rather than Code.part42
def part42_state_update (st: State): State :=
  Γ (part42_state st) ⟦Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part42_state for Code.part42 produces the same result
lemma part42_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part42_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part42
  MLIR
  rewrite [←eq]
  unfold part42_state_update part42_state
  rfl

lemma part42_updates_opaque {st : State} : 
  Code.getReturn (part41_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part42_state_update (part41_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part41_state_update, part42_wp]

end Risc0.OneHot20.Witness.WP