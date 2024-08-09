import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.computeDecode.Witness.Code
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart13

namespace Risc0.computeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part14 on st
def part14_state (st: State) : State :=
  
        ((withEqZero
            ((st.felts { name := "%6" : FeltVar }).get! -
              ((st.felts { name := "%37" : FeltVar }).get! + (st.felts { name := "%26" : FeltVar }).get!))
            ((st[felts][{ name := "%38" : FeltVar }] ←
                (st.felts { name := "%37" : FeltVar }).get! +
                  (st.felts { name := "%26" : FeltVar }).get!)[felts][{ name := "%39" : FeltVar }] ←
              (st.felts { name := "%6" : FeltVar }).get! -
                ((st.felts { name := "%37" : FeltVar }).get! + (st.felts { name := "%26" : FeltVar }).get!)))["%41"] ←ₛ
          getImpl st { name := "data" : BufferVar } (0 : Back) (7 : ℕ)) 

def part14_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%6"⟩) ⟨"%37"⟩) ⟨"%26"⟩) ⟨"%38"⟩) ⟨"%39"⟩

-- Run the program from part14 onwards by using part14_state rather than Code.part14
def part14_state_update (st: State): State :=
  Γ (part14_drops (part14_state st)) ⟦Code.part15;dropfelt ⟨"%5"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%44"⟩;Code.part16;dropfelt ⟨"%2"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%46"⟩;Code.part17;dropfelt ⟨"%42"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;Code.part18;dropfelt ⟨"%7"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part19;dropfelt ⟨"%8"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%57"⟩;Code.part20;dropfelt ⟨"%58"⟩⟧

-- Prove that substituting part14_state for Code.part14 produces the same result
lemma part14_wp {st : State} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part14;dropfelt ⟨"%6"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part15;dropfelt ⟨"%5"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%44"⟩;Code.part16;dropfelt ⟨"%2"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%46"⟩;Code.part17;dropfelt ⟨"%42"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;Code.part18;dropfelt ⟨"%7"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part19;dropfelt ⟨"%8"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%57"⟩;Code.part20;dropfelt ⟨"%58"⟩) st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part14_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  unfold MLIR.runProgram; try simp only
  generalize eq : (dropfelt ⟨"%6"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part15;dropfelt ⟨"%5"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%44"⟩;Code.part16;dropfelt ⟨"%2"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%46"⟩;Code.part17;dropfelt ⟨"%42"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;Code.part18;dropfelt ⟨"%7"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part19;dropfelt ⟨"%8"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%57"⟩;Code.part20;dropfelt ⟨"%58"⟩) = prog
  unfold Code.part14
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part14_state_update part14_drops part14_state
  rfl

lemma part14_updates_opaque {st : State} : 
  Code.getReturn (part13_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part14_state_update (part13_drops (part13_state st))) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  try simp [part13_state_update, part14_wp]

lemma part14_cumulative_wp {in0: Felt} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Option Felt} :
  Code.run (start_state ([in0])) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn
      (part14_state_update
        (({
              buffers :=
                (Map.empty[{ name := "in" : BufferVar }] ←ₘ [[some in0]])[{ name := "data" : BufferVar }] ←ₘ
                  [[some (2 : Felt), some (0 : Felt), some (0 : Felt), some (3 : Felt), some (0 : Felt),
                      some (0 : Felt), some (2 : Felt), some (0 : Felt), some (0 : Felt), some (0 : Felt),
                      some (0 : Felt), some (0 : Felt), some (0 : Felt), some (0 : Felt), some (0 : Felt),
                      some (0 : Felt), some (0 : Felt), some (1 : Felt)]],
              bufferWidths :=
                (Map.empty[{ name := "data" : BufferVar }] ←ₘ (18 : ℕ))[{ name := "in" : BufferVar }] ←ₘ (1 : ℕ),
              cycle := (0 : ℕ),
              felts :=
                ((((Map.empty[{ name := "%7" : FeltVar }] ←ₘ (2 : Felt))[{ name := "%6" : FeltVar }] ←ₘ
                        (3 : Felt))[{ name := "%8" : FeltVar }] ←ₘ
                      (1 : Felt))[{ name := "%5" : FeltVar }] ←ₘ
                    (4 : Felt))[{ name := "%2" : FeltVar }] ←ₘ
                  (16 : Felt),
              isFailed := ¬(4 : Felt) - (2 : Felt) * (2 : Felt) = (0 : Felt), props := Map.empty,
              vars :=
                [{ name := "in" : BufferVar }, { name := "data" : BufferVar }] }[felts][{ name := "%37" : FeltVar }] ←
            (0 : Felt))[felts][{ name := "%26" : FeltVar }] ←
          (3 : Felt)))
      ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14,
        data15, data16, data17])  := by
    rewrite [part13_cumulative_wp]
    rewrite [part14_updates_opaque]
    unfold part13_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part13_drops
    -- 5 drops
    try simp [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    try simp [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    try simp [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- try simp [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.computeDecode.Witness.WP