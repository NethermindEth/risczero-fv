import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart7

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part8 on st
def part8_state (st: State) : State :=
  
          (State.set!
              ((st[felts][{ name := "%145" }] ←
                  Option.get! (State.felts st { name := "%20" }) -
                    Option.get! (State.felts st { name := "%15" }))[felts][{ name := "%146" }] ←
                if
                    Option.get! (State.felts st { name := "%20" }) - Option.get! (State.felts st { name := "%15" }) =
                      0 then
                  1
                else 0)
              { name := "data" } 4
              (if
                  Option.get! (State.felts st { name := "%20" }) - Option.get! (State.felts st { name := "%15" }) =
                    0 then
                1
              else 0)[felts][{ name := "%147" }] ←
            Option.get!
                (((st.felts[{ name := "%145" }] ←ₘ
                      Option.get! (State.felts st { name := "%20" }) -
                        Option.get! (State.felts st { name := "%15" }))[{ name := "%146" }] ←ₘ
                    if
                        Option.get! (State.felts st { name := "%20" }) -
                            Option.get! (State.felts st { name := "%15" }) =
                          0 then
                      1
                    else 0)
                  { name := "%20" }) -
              Option.get!
                (((st.felts[{ name := "%145" }] ←ₘ
                      Option.get! (State.felts st { name := "%20" }) -
                        Option.get! (State.felts st { name := "%15" }))[{ name := "%146" }] ←ₘ
                    if
                        Option.get! (State.felts st { name := "%20" }) -
                            Option.get! (State.felts st { name := "%15" }) =
                          0 then
                      1
                    else 0)
                  {
                    name :=
                      "%14" })) 

-- Run the program from part8 onwards by using part8_state rather than Code.part8
def part8_state_update (st: State): State :=
  Γ (part8_state st) ⟦Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part8_state for Code.part8 produces the same result
lemma part8_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part8_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part8
  MLIR
  rewrite [←eq]
  unfold part8_state_update part8_state
  rfl

lemma part8_updates_opaque {st : State} : 
  Code.getReturn (part7_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part8_state_update (part7_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part7_state_update, part8_wp]

end Risc0.OneHot20.Witness.WP