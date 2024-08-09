import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.computeDecode.Constraints.CodeDrops

namespace Risc0.computeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part0 on st
def part0_state (st: State) : State :=
  
        ((((st[props][{ name := "%8" : PropVar }] ← True)[felts][{ name := "%3" : FeltVar }] ← (4 : Felt))["%11"] ←ₛ
            getImpl st { name := "data" : BufferVar } (0 : Back) (8 : ℕ))[felts][{ name := "%12" : FeltVar }] ←
          ((((st[props][{ name := "%8" : PropVar }] ← True)[felts][{ name := "%3" : FeltVar }] ← (4 : Felt))["%11"] ←ₛ
                    getImpl st { name := "data" : BufferVar } (0 : Back) (8 : ℕ)).felts
                { name := "%11" : FeltVar }).get! *
            (4 : Felt)) 

def part0_drops (st: State) : State :=
  State.dropFelts (st) ⟨"%11"⟩

-- Run the whole program by using part0_state rather than Code.part0
def part0_state_update (st: State): State :=
  Γ (part0_drops (part0_state st)) ⟦Code.part1;dropfelt ⟨"%13"⟩;Code.part2;dropfelt ⟨"%12"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;Code.part3;dropfelt ⟨"%18"⟩;dropfelt ⟨"%10"⟩;Code.part4;dropfelt ⟨"%19"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%22"⟩;Code.part5;dropfelt ⟨"%23"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;Code.part6;dropfelt ⟨"%28"⟩;dropfelt ⟨"%31"⟩;Code.part7;dropfelt ⟨"%6"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;Code.part8;dropfelt ⟨"%29"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;Code.part9;dropfelt ⟨"%38"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%40"⟩;Code.part10;dropfelt ⟨"%3"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%46"⟩;Code.part11;dropfelt ⟨"%5"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%48"⟩;Code.part12;dropfelt ⟨"%44"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;Code.part13;dropfelt ⟨"%1"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;Code.part14;dropfelt ⟨"%4"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%57"⟩;Code.part15;dropfelt ⟨"%60"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%61"⟩⟧

-- Prove that substituting part0_state for Code.part0 produces the same result
lemma part0_wp {st : State} :
  Code.getReturn (Γ st ⟦Code.part0;dropfelt ⟨"%11"⟩;Code.part1;dropfelt ⟨"%13"⟩;Code.part2;dropfelt ⟨"%12"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;Code.part3;dropfelt ⟨"%18"⟩;dropfelt ⟨"%10"⟩;Code.part4;dropfelt ⟨"%19"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%22"⟩;Code.part5;dropfelt ⟨"%23"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;Code.part6;dropfelt ⟨"%28"⟩;dropfelt ⟨"%31"⟩;Code.part7;dropfelt ⟨"%6"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;Code.part8;dropfelt ⟨"%29"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;Code.part9;dropfelt ⟨"%38"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%40"⟩;Code.part10;dropfelt ⟨"%3"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%46"⟩;Code.part11;dropfelt ⟨"%5"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%48"⟩;Code.part12;dropfelt ⟨"%44"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;Code.part13;dropfelt ⟨"%1"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;Code.part14;dropfelt ⟨"%4"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%57"⟩;Code.part15;dropfelt ⟨"%60"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%61"⟩⟧)↔
  Code.getReturn (part0_state_update st) := by
  generalize eq : (dropfelt ⟨"%11"⟩;Code.part1;dropfelt ⟨"%13"⟩;Code.part2;dropfelt ⟨"%12"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%17"⟩;Code.part3;dropfelt ⟨"%18"⟩;dropfelt ⟨"%10"⟩;Code.part4;dropfelt ⟨"%19"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%22"⟩;Code.part5;dropfelt ⟨"%23"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%25"⟩;Code.part6;dropfelt ⟨"%28"⟩;dropfelt ⟨"%31"⟩;Code.part7;dropfelt ⟨"%6"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;Code.part8;dropfelt ⟨"%29"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;Code.part9;dropfelt ⟨"%38"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%40"⟩;Code.part10;dropfelt ⟨"%3"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%46"⟩;Code.part11;dropfelt ⟨"%5"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%48"⟩;Code.part12;dropfelt ⟨"%44"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;Code.part13;dropfelt ⟨"%1"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;Code.part14;dropfelt ⟨"%4"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%57"⟩;Code.part15;dropfelt ⟨"%60"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%61"⟩) = prog
  unfold Code.part0
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part0_state_update part0_drops part0_state
  rfl
lemma part0_cumulative_wp {in0 data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Felt}:
  Code.run (start_state ([in0]) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17])) ↔
  Code.getReturn
      (part0_state_update
        {
          buffers :=
            Map.fromList
              [({ name := "in" : BufferVar }, [[some in0]]),
                ({ name := "data" : BufferVar },
                  [[some data0, some data1, some data2, some data3, some data4, some data5, some data6, some data7,
                      some data8, some data9, some data10, some data11, some data12, some data13, some data14,
                      some data15, some data16, some data17]])],
          bufferWidths :=
            Map.fromList [({ name := "in" : BufferVar }, (1 : ℕ)), ({ name := "data" : BufferVar }, (18 : ℕ))],
          cycle := (0 : ℕ), felts := Map.empty, isFailed := false = true, props := Map.empty,
          vars := [{ name := "in" : BufferVar }, { name := "data" : BufferVar }] })  := by
    unfold Code.run start_state
    rewrite [Code.optimised_behaviour_full]
    unfold MLIR.runProgram
    rewrite [←Code.parts_combine]
    unfold Code.parts_combined
    rewrite [←Code.getReturn_ignores_drops]
    rewrite [←Code.behaviour_with_drops]
    rewrite [part0_wp]
    rfl

end Risc0.computeDecode.Constraints.WP