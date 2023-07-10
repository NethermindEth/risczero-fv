import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.CodeDrops

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part0 on st
def part0_state (st: State) : State :=
  
        ((((st[props][{ name := "%6" }] ← True)[felts][{ name := "%4" }] ← (4 : Felt))["%13"] ←ₛ
            getImpl st { name := "data" } (0 : Back) (8 : ℕ))[felts][{ name := "%14" }] ←
          Option.get!
              (State.felts
                (((st[props][{ name := "%6" }] ← True)[felts][{ name := "%4" }] ← (4 : Felt))["%13"] ←ₛ
                  getImpl st { name := "data" } (0 : Back) (8 : ℕ))
                { name := "%13" }) *
            (4 : Felt)) 

def part0_drops (st: State) : State :=
  State.dropFelts (st) ⟨"%13"⟩

-- Run the whole program by using part0_state rather than Code.part0
def part0_state_update (st: State): State :=
  Γ (part0_drops (part0_state st)) ⟦Code.part1;dropfelt ⟨"%15"⟩;Code.part2;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;Code.part3;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;Code.part4;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;Code.part5;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;Code.part6;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;Code.part7;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;Code.part8;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part9;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩⟧

-- Prove that substituting part0_state for Code.part0 produces the same result
lemma part0_wp {st : State} :
  Code.getReturn (Γ st ⟦Code.part0;dropfelt ⟨"%13"⟩;Code.part1;dropfelt ⟨"%15"⟩;Code.part2;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;Code.part3;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;Code.part4;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;Code.part5;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;Code.part6;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;Code.part7;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;Code.part8;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part9;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩⟧)↔
  Code.getReturn (part0_state_update st) := by
  generalize eq : (dropfelt ⟨"%13"⟩;Code.part1;dropfelt ⟨"%15"⟩;Code.part2;dropfelt ⟨"%14"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%19"⟩;Code.part3;dropfelt ⟨"%20"⟩;dropfelt ⟨"%12"⟩;Code.part4;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;Code.part5;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;Code.part6;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;Code.part7;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;Code.part8;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part9;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩) = prog
  unfold Code.part0
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part0_state_update part0_drops part0_state
  rfl

lemma part0_cumulative_wp {x0 x1 x2 x3 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17: Felt}:
  Code.run (start_state [x0,x1,x2,x3] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17])) ↔
  Code.getReturn
      (part0_state_update
        {
          buffers :=
            Map.fromList
              [({ name := "in" }, [[some x0, some x1, some x2, some x3]]),
                ({ name := "data" },
                  [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7, some y8, some y9, some y10,
                      some y11, some y12, some y13, some y14, some y15, some y16, some y17]])],
          bufferWidths := Map.fromList [({ name := "in" }, (4 : ℕ)), ({ name := "data" }, (18 : ℕ))], constraints := [],
          cycle := (0 : ℕ), felts := Map.empty, isFailed := false, props := Map.empty,
          vars := [{ name := "in" }, { name := "data" }] })  := by
    unfold Code.run start_state
    rewrite [Code.optimised_behaviour_full]
    unfold MLIR.runProgram
    rewrite [←Code.parts_combine]
    unfold Code.parts_combined
    rewrite [←Code.getReturn_ignores_drops]
    rewrite [←Code.behaviour_with_drops]
    rewrite [part0_wp]
    rfl

end Risc0.ComputeDecode.Constraints.WP