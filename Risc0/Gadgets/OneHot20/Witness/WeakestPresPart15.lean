import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart14

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part15 on st
def part15_state (st: State) : State :=
  
          ((State.set!
                (st[felts][{ name := "%164" }] ← if Option.get! (State.felts st { name := "%163" }) = 0 then 1 else 0)
                { name := "data" } 13
                (if Option.get! (State.felts st { name := "%163" }) = 0 then 1 else 0)[felts][{ name := "%165" }] ←
              Option.get!
                  ((st.felts[{ name := "%164" }] ←ₘ
                      if Option.get! (State.felts st { name := "%163" }) = 0 then 1 else 0)
                    { name := "%20" }) -
                Option.get!
                  ((st.felts[{ name := "%164" }] ←ₘ
                      if Option.get! (State.felts st { name := "%163" }) = 0 then 1 else 0)
                    { name := "%5" }))[felts][{ name := "%166" }] ←
            if
                Option.get!
                      ((st.felts[{ name := "%164" }] ←ₘ
                          if Option.get! (State.felts st { name := "%163" }) = 0 then 1 else 0)
                        { name := "%20" }) -
                    Option.get!
                      ((st.felts[{ name := "%164" }] ←ₘ
                          if Option.get! (State.felts st { name := "%163" }) = 0 then 1 else 0)
                        { name := "%5" }) =
                  0 then
              1
            else
              0) 

-- Run the program from part15 onwards by using part15_state rather than Code.part15
def part15_state_update (st: State): State :=
  Γ (part15_state st) ⟦Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54⟧

-- Prove that substituting part15_state for Code.part15 produces the same result
lemma part15_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part15_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39; Code.part40; Code.part41; Code.part42; Code.part43; Code.part44; Code.part45; Code.part46; Code.part47; Code.part48; Code.part49; Code.part50; Code.part51; Code.part52; Code.part53; Code.part54) = prog
  unfold Code.part15
  MLIR
  rewrite [←eq]
  unfold part15_state_update part15_state
  rfl

lemma part15_updates_opaque {st : State} : 
  Code.getReturn (part14_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part15_state_update (part14_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part14_state_update, part15_wp]

end Risc0.OneHot20.Witness.WP