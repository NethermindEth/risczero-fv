import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart45

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part46 on st
def part46_state (st: State) : State :=
  
          (withEqZero
            (Option.get!
                (((st.felts[{ name := "%112" }] ←ₘ
                      Option.get! (State.felts st { name := "%109" }) +
                        Option.get! (State.felts st { name := "%49" }))[{ name := "%113" }] ←ₘ
                    Option.get!
                        ((st.felts[{ name := "%112" }] ←ₘ
                            Option.get! (State.felts st { name := "%109" }) +
                              Option.get! (State.felts st { name := "%49" }))
                          { name := "%18" }) -
                      Option.get!
                        ((st.felts[{ name := "%112" }] ←ₘ
                            Option.get! (State.felts st { name := "%109" }) +
                              Option.get! (State.felts st { name := "%49" }))
                          { name := "%52" }))
                  { name := "%52" }) *
              (Option.get!
                  ((st.felts[{ name := "%112" }] ←ₘ
                      Option.get! (State.felts st { name := "%109" }) + Option.get! (State.felts st { name := "%49" }))
                    { name := "%18" }) -
                Option.get!
                  ((st.felts[{ name := "%112" }] ←ₘ
                      Option.get! (State.felts st { name := "%109" }) + Option.get! (State.felts st { name := "%49" }))
                    { name := "%52" })))
            (((st[felts][{ name := "%112" }] ←
                  Option.get! (State.felts st { name := "%109" }) +
                    Option.get! (State.felts st { name := "%49" }))[felts][{ name := "%113" }] ←
                Option.get!
                    ((st.felts[{ name := "%112" }] ←ₘ
                        Option.get! (State.felts st { name := "%109" }) +
                          Option.get! (State.felts st { name := "%49" }))
                      { name := "%18" }) -
                  Option.get!
                    ((st.felts[{ name := "%112" }] ←ₘ
                        Option.get! (State.felts st { name := "%109" }) +
                          Option.get! (State.felts st { name := "%49" }))
                      { name := "%52" }))[felts][{ name := "%114" }] ←
              Option.get!
                  (((st.felts[{ name := "%112" }] ←ₘ
                        Option.get! (State.felts st { name := "%109" }) +
                          Option.get! (State.felts st { name := "%49" }))[{ name := "%113" }] ←ₘ
                      Option.get!
                          ((st.felts[{ name := "%112" }] ←ₘ
                              Option.get! (State.felts st { name := "%109" }) +
                                Option.get! (State.felts st { name := "%49" }))
                            { name := "%18" }) -
                        Option.get!
                          ((st.felts[{ name := "%112" }] ←ₘ
                              Option.get! (State.felts st { name := "%109" }) +
                                Option.get! (State.felts st { name := "%49" }))
                            { name := "%52" }))
                    { name := "%52" }) *
                (Option.get!
                    ((st.felts[{ name := "%112" }] ←ₘ
                        Option.get! (State.felts st { name := "%109" }) +
                          Option.get! (State.felts st { name := "%49" }))
                      { name := "%18" }) -
                  Option.get!
                    ((st.felts[{ name := "%112" }] ←ₘ
                        Option.get! (State.felts st { name := "%109" }) +
                          Option.get! (State.felts st { name := "%49" }))
                      {
                        name :=
                          "%52" })))) 

-- Run the program from part46 onwards by using part46_state rather than Code.part46
def part46_state_update (st: State): State :=
  Γ (part46_state st) ⟦Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part46_state for Code.part46 produces the same result
lemma part46_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part46_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part46
  MLIR
  rewrite [←eq]
  unfold part46_state_update part46_state
  rfl

lemma part46_updates_opaque {st : State} : 
  Code.getReturn (part45_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part46_state_update (part45_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part45_state_update, part46_wp]

end Risc0.OneHot20.Witness.WP