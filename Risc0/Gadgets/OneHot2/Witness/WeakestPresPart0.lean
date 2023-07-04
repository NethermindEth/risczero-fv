import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot2.Witness.CodeDrops

namespace Risc0.OneHot2.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part0 on st
def part0_state (st: State) : State :=
  
          ((State.set!
              ((st["%2"] ←ₛ getImpl st { name := "code" } 0 0)[felts][{ name := "%12" }] ←
                if Option.get! (State.felts (st["%2"] ←ₛ getImpl st { name := "code" } 0 0) { name := "%2" }) = 0 then 1
                else 0)
              { name := "data" } 0
              (if Option.get! (State.felts (st["%2"] ←ₛ getImpl st { name := "code" } 0 0) { name := "%2" }) = 0 then 1
              else 0))[felts][{ name := "%0" }] ←
            1) 

def part0_drops (st: State) : State :=
  State.dropFelts (st) ⟨"%12"⟩

-- Run the whole program by using part0_state rather than Code.part0
def part0_state_update (st: State): State :=
  Γ (part0_drops (part0_state st)) ⟦Code.part1;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;Code.part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧

-- Prove that substituting part0_state for Code.part0 produces the same result
lemma part0_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (Γ st ⟦Code.part0;dropfelt ⟨"%12"⟩;Code.part1;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;Code.part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩⟧) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part0_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  generalize eq : (dropfelt ⟨"%12"⟩;Code.part1;dropfelt ⟨"%13"⟩;dropfelt ⟨"%14"⟩;Code.part2;dropfelt ⟨"%2"⟩;dropfelt ⟨"%4"⟩;Code.part3;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;Code.part4;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%10"⟩;Code.part5;dropfelt ⟨"%11"⟩;dropfelt ⟨"%1"⟩) = prog
  unfold Code.part0
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part0_state_update part0_drops part0_state
  rfl

lemma part0_cumulative_wp :
  Code.run (start_state [x0]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19] ↔
  Code.getReturn
        (part0_state_update
          {
            buffers :=
              Map.fromList
                [({ name := "code" }, [[x0]]),
                  ({ name := "data" },
                    [[none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none,
                        none, none, none, none]])],
            bufferWidths := Map.fromList [({ name := "code" }, 1), ({ name := "data" }, 20)], constraints := [],
            cycle := 0, felts := Map.empty, isFailed := false, props := Map.empty,
            vars := [{ name := "code" }, { name := "data" }] }) =
      [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19]  := by
    unfold Code.run start_state
    rewrite [Code.optimised_behaviour_full]
    unfold MLIR.runProgram
    rewrite [←Code.parts_combine]
    unfold Code.parts_combined
    rewrite [←Code.getReturn_ignores_drops]
    rewrite [←Code.behaviour_with_drops]
    rewrite [part0_wp]
    rfl

end Risc0.OneHot2.Witness.WP