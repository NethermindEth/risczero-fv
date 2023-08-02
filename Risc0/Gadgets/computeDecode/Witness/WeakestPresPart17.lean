import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.computeDecode.Witness.Code
import Risc0.Gadgets.computeDecode.Witness.WeakestPresPart16

namespace Risc0.computeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part17 on st
def part17_state (st: State) : State :=
  
        ((((st[felts][{ name := "%49" : FeltVar }] ←
                Option.get! (State.felts st { name := "%48" : FeltVar }) *
                  Option.get! (State.felts st { name := "%4" : FeltVar }))[felts][{ name := "%50" : FeltVar }] ←
              Option.get! (State.felts st { name := "%48" : FeltVar }) *
                  Option.get! (State.felts st { name := "%4" : FeltVar }) +
                Option.get! (State.felts st { name := "%47" : FeltVar }))[felts][{ name := "%51" : FeltVar }] ←
            Option.get! (State.felts st { name := "%48" : FeltVar }) *
                  Option.get! (State.felts st { name := "%4" : FeltVar }) +
                Option.get! (State.felts st { name := "%47" : FeltVar }) +
              Option.get! (State.felts st { name := "%42" : FeltVar }))["%40"] ←ₛ
          getImpl st { name := "data" : BufferVar } (0 : Back) (6 : ℕ)) 

def part17_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%42"⟩) ⟨"%47"⟩) ⟨"%48"⟩) ⟨"%49"⟩) ⟨"%50"⟩

-- Run the program from part17 onwards by using part17_state rather than Code.part17
def part17_state_update (st: State): State :=
  Γ (part17_drops (part17_state st)) ⟦Code.part18;dropfelt ⟨"%7"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part19;dropfelt ⟨"%8"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%57"⟩;Code.part20;dropfelt ⟨"%58"⟩⟧

-- Prove that substituting part17_state for Code.part17 produces the same result
lemma part17_wp {st : State} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part17;dropfelt ⟨"%42"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;Code.part18;dropfelt ⟨"%7"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part19;dropfelt ⟨"%8"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%57"⟩;Code.part20;dropfelt ⟨"%58"⟩) st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part17_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%42"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;Code.part18;dropfelt ⟨"%7"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part19;dropfelt ⟨"%8"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%57"⟩;Code.part20;dropfelt ⟨"%58"⟩) = prog
  unfold Code.part17
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part17_state_update part17_drops part17_state
  rfl

lemma part17_updates_opaque {st : State} : 
  Code.getReturn (part16_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part17_state_update (part16_drops (part16_state st))) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  simp [part16_state_update, part17_wp]

lemma part17_cumulative_wp {in0: Felt} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Option Felt} :
  Code.run (start_state ([in0])) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn
      (part17_state_update
        (((({
                  buffers :=
                    ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                        [[some in0]])[{ name := "data" : BufferVar }] ←ₘ
                      [[some (2 : Felt), some (0 : Felt), some (0 : Felt), some (3 : Felt), some (0 : Felt),
                          some (0 : Felt), some (2 : Felt), some (0 : Felt), some (0 : Felt), some (0 : Felt),
                          some (0 : Felt), some (0 : Felt), some (0 : Felt), some (0 : Felt), some (0 : Felt),
                          some (0 : Felt), some (0 : Felt), some (1 : Felt)]],
                  bufferWidths :=
                    ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                        (18 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                      (1 : ℕ),
                  cycle := (0 : ℕ),
                  felts :=
                    (Map.empty[{ name := "%7" : FeltVar }] ←ₘ (2 : Felt))[{ name := "%8" : FeltVar }] ←ₘ (1 : Felt),
                  isFailed := False, props := Map.empty,
                  vars :=
                    [{ name := "in" : BufferVar },
                      { name := "data" : BufferVar }] }[felts][{ name := "%42" : FeltVar }] ←
                (0 : Felt) * (4 : Felt))[felts][{ name := "%47" : FeltVar }] ←
              ((0 : Felt) * (4 : Felt) + (0 : Felt)) * (16 : Felt))[felts][{ name := "%4" : FeltVar }] ←
            (128 : Felt))[felts][{ name := "%48" : FeltVar }] ←
          (0 : Felt)))
      ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14,
        data15, data16, data17])  := by
    rewrite [part16_cumulative_wp]
    rewrite [part17_updates_opaque]
    unfold part16_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part16_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.computeDecode.Witness.WP