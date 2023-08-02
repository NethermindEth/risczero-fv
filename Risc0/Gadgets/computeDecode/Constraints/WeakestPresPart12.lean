import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.computeDecode.Constraints.Code
import Risc0.Gadgets.computeDecode.Constraints.WeakestPresPart11

namespace Risc0.computeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part12 on st
def part12_state (st: State) : State :=
  
        ((((st["%50"] ←ₛ
                getImpl st { name := "data" : BufferVar } (0 : Back) (14 : ℕ))[felts][{ name := "%51" : FeltVar }] ←
              Option.get!
                  (State.felts (st["%50"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (14 : ℕ))
                    { name := "%50" : FeltVar }) *
                Option.get! (State.felts st { name := "%4" : FeltVar }))[felts][{ name := "%52" : FeltVar }] ←
            Option.get!
                  (State.felts (st["%50"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (14 : ℕ))
                    { name := "%50" : FeltVar }) *
                Option.get! (State.felts st { name := "%4" : FeltVar }) +
              Option.get! (State.felts st { name := "%49" : FeltVar }))[felts][{ name := "%53" : FeltVar }] ←
          Option.get!
                  (State.felts (st["%50"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (14 : ℕ))
                    { name := "%50" : FeltVar }) *
                Option.get! (State.felts st { name := "%4" : FeltVar }) +
              Option.get! (State.felts st { name := "%49" : FeltVar }) +
            Option.get! (State.felts st { name := "%44" : FeltVar })) 

def part12_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%44"⟩) ⟨"%49"⟩) ⟨"%50"⟩) ⟨"%51"⟩) ⟨"%52"⟩

-- Run the program from part12 onwards by using part12_state rather than Code.part12
def part12_state_update (st: State): State :=
  Γ (part12_drops (part12_state st)) ⟦Code.part13;dropfelt ⟨"%1"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;Code.part14;dropfelt ⟨"%4"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%57"⟩;Code.part15;dropfelt ⟨"%60"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%61"⟩⟧

-- Prove that substituting part12_state for Code.part12 produces the same result
lemma part12_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part12;dropfelt ⟨"%44"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;Code.part13;dropfelt ⟨"%1"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;Code.part14;dropfelt ⟨"%4"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%57"⟩;Code.part15;dropfelt ⟨"%60"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%61"⟩) st) ↔
  Code.getReturn (part12_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%44"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;Code.part13;dropfelt ⟨"%1"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;Code.part14;dropfelt ⟨"%4"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%57"⟩;Code.part15;dropfelt ⟨"%60"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%61"⟩) = prog
  unfold Code.part12
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part12_state_update part12_drops part12_state
  rfl

lemma part12_updates_opaque {st : State} : 
  Code.getReturn (part11_state_update st) ↔
  Code.getReturn (part12_state_update (part11_drops (part11_state st))) := by
  simp [part11_state_update, part12_wp]

lemma part12_cumulative_wp {in0 data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Felt} :
  Code.run (start_state ([in0]) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17])) ↔
  Code.getReturn
      (part12_state_update
        ((((((({
                        buffers :=
                          ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                              [[some data0, some data1, some data2, some data3, some data4, some data5, some data6,
                                  some data7, some data8, some data9, some data10, some data11, some data12,
                                  some data13, some data14, some data15, some data16,
                                  some data17]])[{ name := "in" : BufferVar }] ←ₘ
                            [[some in0]],
                        bufferWidths :=
                          ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                              (18 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                            (1 : ℕ),
                        cycle := (0 : ℕ), felts := Map.empty, isFailed := False, props := Map.empty,
                        vars :=
                          [{ name := "in" : BufferVar },
                            { name := "data" : BufferVar }] }[props][{ name := "%8" : PropVar }] ←
                      True)[felts][{ name := "%1" : FeltVar }] ←
                    (2 : Felt))[props][{ name := "%26" : PropVar }] ←
                  (4 : Felt) -
                      ((data10 * (64 : Felt) +
                            (data1 * (16 : Felt) + data9 * (8 : Felt) + data8 * (4 : Felt) + data0)) *
                          (2 : Felt) +
                        data13) =
                    (0 : Felt))[props][{ name := "%41" : PropVar }] ←
                ((4 : Felt) -
                      ((data10 * (64 : Felt) +
                            (data1 * (16 : Felt) + data9 * (8 : Felt) + data8 * (4 : Felt) + data0)) *
                          (2 : Felt) +
                        data13) =
                    (0 : Felt) ∧
                  (3 : Felt) -
                      ((data12 * (8 : Felt) + data2 * (2 : Felt) + data11) * (16 : Felt) + data4 * (4 : Felt) + data3) =
                    (0 : Felt)))[felts][{ name := "%44" : FeltVar }] ←
              data7 * (4 : Felt))[felts][{ name := "%49" : FeltVar }] ←
            (data15 * (4 : Felt) + data5) * (16 : Felt))[felts][{ name := "%4" : FeltVar }] ←
          (128 : Felt)))  := by
    rewrite [part11_cumulative_wp]
    rewrite [part12_updates_opaque]
    unfold part11_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part11_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.computeDecode.Constraints.WP