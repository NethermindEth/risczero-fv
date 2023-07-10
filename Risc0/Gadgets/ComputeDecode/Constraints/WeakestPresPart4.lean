import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart3

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part4 on st
def part4_state (st: State) : State :=
  
        ((((st[felts][{ name := "%23" }] ←
                Option.get! (State.felts st { name := "%22" }) *
                  Option.get! (State.felts st { name := "%5" }))[felts][{ name := "%24" }] ←
              Option.get! (State.felts st { name := "%22" }) * Option.get! (State.felts st { name := "%5" }) +
                Option.get! (State.felts st { name := "%21" }))[felts][{ name := "%3" }] ←
            (2 : Felt))[felts][{ name := "%25" }] ←
          (Option.get! (State.felts st { name := "%22" }) * Option.get! (State.felts st { name := "%5" }) +
              Option.get! (State.felts st { name := "%21" })) *
            (2 : Felt)) 

def part4_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%21"⟩) ⟨"%5"⟩) ⟨"%22"⟩) ⟨"%23"⟩) ⟨"%24"⟩

-- Run the program from part4 onwards by using part4_state rather than Code.part4
def part4_state_update (st: State): State :=
  Γ (part4_drops (part4_state st)) ⟦Code.part5;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;Code.part6;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;Code.part7;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;Code.part8;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part9;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩⟧

-- Prove that substituting part4_state for Code.part4 produces the same result
lemma part4_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part4;dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;Code.part5;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;Code.part6;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;Code.part7;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;Code.part8;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part9;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩) st) ↔
  Code.getReturn (part4_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%21"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%24"⟩;Code.part5;dropfelt ⟨"%25"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%10"⟩;Code.part6;dropfelt ⟨"%27"⟩;dropfelt ⟨"%30"⟩;Code.part7;dropfelt ⟨"%2"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;Code.part8;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part9;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%6"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%64"⟩) = prog
  unfold Code.part4
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part4_state_update part4_drops part4_state
  rfl

lemma part4_updates_opaque {st : State} : 
  Code.getReturn (part3_state_update st) ↔
  Code.getReturn (part4_state_update (part3_drops (part3_state st))) := by
  simp [part3_state_update, part4_wp]

lemma part4_cumulative_wp {x0 x1 x2 x3 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17: Felt} :
  Code.run (start_state [x0,x1,x2,x3] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17])) ↔
  Code.getReturn
      (part4_state_update
        ((((((({
                        buffers :=
                          ((fun x => Map.empty x)[{ name := "data" }] ←ₘ
                              [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7, some y8,
                                  some y9, some y10, some y11, some y12, some y13, some y14, some y15, some y16,
                                  some y17]])[{ name := "in" }] ←ₘ
                            [[some x0, some x1, some x2, some x3]],
                        bufferWidths :=
                          ((fun x => Map.empty x)[{ name := "data" }] ←ₘ (18 : ℕ))[{ name := "in" }] ←ₘ (4 : ℕ),
                        constraints := [], cycle := (0 : ℕ), felts := Map.empty, isFailed := false, props := Map.empty,
                        vars := [{ name := "in" }, { name := "data" }] }[props][{ name := "%6" }] ←
                      True)[felts][{ name := "%4" }] ←
                    (4 : Felt))[felts][{ name := "%2" }] ←
                  (8 : Felt))[felts][{ name := "%1" }] ←
                (16 : Felt))[felts][{ name := "%21" }] ←
              y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)[felts][{ name := "%5" }] ←
            (64 : Felt))[felts][{ name := "%22" }] ←
          y10))  := by
    rewrite [part3_cumulative_wp]
    rewrite [part4_updates_opaque]
    unfold part3_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part3_drops
    -- 2 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]

end Risc0.ComputeDecode.Constraints.WP