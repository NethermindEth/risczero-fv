import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart4

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part5 on st
def part5_state (st: State) : State := 
  
        ((((st["%20"] ←ₛ getImpl st { name := "code" } 0 0)["%21"] ←ₛ
              getImpl (st["%20"] ←ₛ getImpl st { name := "code" } 0 0) { name := "data" } 0 1)["%22"] ←ₛ
            getImpl
              ((st["%20"] ←ₛ getImpl st { name := "code" } 0 0)["%21"] ←ₛ
                getImpl (st["%20"] ←ₛ getImpl st { name := "code" } 0 0) { name := "data" } 0 1)
              { name := "data" } 0 2)[felts][{ name := "%23" }] ←
          Option.get!
              (State.felts
                (((st["%20"] ←ₛ getImpl st { name := "code" } 0 0)["%21"] ←ₛ
                    getImpl (st["%20"] ←ₛ getImpl st { name := "code" } 0 0) { name := "data" } 0 1)["%22"] ←ₛ
                  getImpl
                    ((st["%20"] ←ₛ getImpl st { name := "code" } 0 0)["%21"] ←ₛ
                      getImpl (st["%20"] ←ₛ getImpl st { name := "code" } 0 0) { name := "data" } 0 1)
                    { name := "data" } 0 2)
                { name := "%22" }) *
            Option.get!
              (State.felts
                (((st["%20"] ←ₛ getImpl st { name := "code" } 0 0)["%21"] ←ₛ
                    getImpl (st["%20"] ←ₛ getImpl st { name := "code" } 0 0) { name := "data" } 0 1)["%22"] ←ₛ
                  getImpl
                    ((st["%20"] ←ₛ getImpl st { name := "code" } 0 0)["%21"] ←ₛ
                      getImpl (st["%20"] ←ₛ getImpl st { name := "code" } 0 0) { name := "data" } 0 1)
                    { name := "data" } 0 2)
                {
                  name :=
                    "%1" })) 

-- Run the whole program by using part5_state rather than Code.part5
def part5_state_update (st: State): State :=
  Γ (part5_state st) ⟦Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part5_state for Code.part5 produces the same result
lemma part5_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part5_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part5
  MLIR
  unfold part5_state_update part5_state
  rewrite [←eq]
  rfl

lemma part5_updates_opaque {st : State} : 
  Code.getReturn (part4_state_update st) ↔
  Code.getReturn (part5_state_update (part4_state st)) := by
  simp [part4_state_update, part5_wp]

end Risc0.OneHot20.Constraints.WP