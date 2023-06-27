import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart37

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part38 on st
def part38_state (st: State) : State :=
  
          (withEqZero
            (Option.get!
                (((st.felts[{ name := "%88" }] ←ₘ
                      Option.get! (State.felts st { name := "%85" }) +
                        Option.get! (State.felts st { name := "%25" }))[{ name := "%89" }] ←ₘ
                    Option.get!
                        ((st.felts[{ name := "%88" }] ←ₘ
                            Option.get! (State.felts st { name := "%85" }) +
                              Option.get! (State.felts st { name := "%25" }))
                          { name := "%18" }) -
                      Option.get!
                        ((st.felts[{ name := "%88" }] ←ₘ
                            Option.get! (State.felts st { name := "%85" }) +
                              Option.get! (State.felts st { name := "%25" }))
                          { name := "%28" }))
                  { name := "%28" }) *
              (Option.get!
                  ((st.felts[{ name := "%88" }] ←ₘ
                      Option.get! (State.felts st { name := "%85" }) + Option.get! (State.felts st { name := "%25" }))
                    { name := "%18" }) -
                Option.get!
                  ((st.felts[{ name := "%88" }] ←ₘ
                      Option.get! (State.felts st { name := "%85" }) + Option.get! (State.felts st { name := "%25" }))
                    { name := "%28" })))
            (((st[felts][{ name := "%88" }] ←
                  Option.get! (State.felts st { name := "%85" }) +
                    Option.get! (State.felts st { name := "%25" }))[felts][{ name := "%89" }] ←
                Option.get!
                    ((st.felts[{ name := "%88" }] ←ₘ
                        Option.get! (State.felts st { name := "%85" }) + Option.get! (State.felts st { name := "%25" }))
                      { name := "%18" }) -
                  Option.get!
                    ((st.felts[{ name := "%88" }] ←ₘ
                        Option.get! (State.felts st { name := "%85" }) + Option.get! (State.felts st { name := "%25" }))
                      { name := "%28" }))[felts][{ name := "%90" }] ←
              Option.get!
                  (((st.felts[{ name := "%88" }] ←ₘ
                        Option.get! (State.felts st { name := "%85" }) +
                          Option.get! (State.felts st { name := "%25" }))[{ name := "%89" }] ←ₘ
                      Option.get!
                          ((st.felts[{ name := "%88" }] ←ₘ
                              Option.get! (State.felts st { name := "%85" }) +
                                Option.get! (State.felts st { name := "%25" }))
                            { name := "%18" }) -
                        Option.get!
                          ((st.felts[{ name := "%88" }] ←ₘ
                              Option.get! (State.felts st { name := "%85" }) +
                                Option.get! (State.felts st { name := "%25" }))
                            { name := "%28" }))
                    { name := "%28" }) *
                (Option.get!
                    ((st.felts[{ name := "%88" }] ←ₘ
                        Option.get! (State.felts st { name := "%85" }) + Option.get! (State.felts st { name := "%25" }))
                      { name := "%18" }) -
                  Option.get!
                    ((st.felts[{ name := "%88" }] ←ₘ
                        Option.get! (State.felts st { name := "%85" }) + Option.get! (State.felts st { name := "%25" }))
                      {
                        name :=
                          "%28" })))) 

-- Run the program from part38 onwards by using part38_state rather than Code.part38
def part38_state_update (st: State): State :=
  Γ (part38_state st) ⟦Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part38_state for Code.part38 produces the same result
lemma part38_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part38_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part38
  MLIR
  rewrite [←eq]
  unfold part38_state_update part38_state
  rfl

lemma part38_updates_opaque {st : State} : 
  Code.getReturn (part37_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part38_state_update (part37_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part37_state_update, part38_wp]

end Risc0.OneHot20.Witness.WP