import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart14

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part15 on st
def part15_state (st: State) : State :=
  
        ((((st["%59"] ←ₛ
                getImpl st { name := "data" : BufferVar } (0 : Back) (17 : ℕ))[felts][{ name := "%62" : FeltVar }] ←
              Option.get! (State.felts st { name := "%61" : FeltVar }) +
                Option.get!
                  (State.felts (st["%59"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (17 : ℕ))
                    { name := "%59" : FeltVar }))["%7"] ←ₛ
            getImpl st { name := "in" : BufferVar } (0 : Back) (0 : ℕ))[felts][{ name := "%63" : FeltVar }] ←
          Option.get!
              (State.felts
                (((st["%59"] ←ₛ
                      getImpl st { name := "data" : BufferVar } (0 : Back)
                        (17 : ℕ))[felts][{ name := "%62" : FeltVar }] ←
                    Option.get! (State.felts st { name := "%61" : FeltVar }) +
                      Option.get!
                        (State.felts (st["%59"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (17 : ℕ))
                          { name := "%59" : FeltVar }))["%7"] ←ₛ
                  getImpl st { name := "in" : BufferVar } (0 : Back) (0 : ℕ))
                { name := "%7" : FeltVar }) -
            (Option.get! (State.felts st { name := "%61" : FeltVar }) +
              Option.get!
                (State.felts (st["%59"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (17 : ℕ))
                  { name := "%59" : FeltVar }))) 

def part15_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%61"⟩) ⟨"%59"⟩) ⟨"%62"⟩) ⟨"%7"⟩

-- Run the program from part15 onwards by using part15_state rather than Code.part15
def part15_state_update (st: State): State :=
  Γ (part15_drops (part15_state st)) ⟦Code.part16;dropfelt ⟨"%63"⟩⟧

-- Prove that substituting part15_state for Code.part15 produces the same result
lemma part15_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%63"⟩) st) ↔
  Code.getReturn (part15_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%63"⟩) = prog
  unfold Code.part15
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part15_state_update part15_drops part15_state
  rfl

lemma part15_updates_opaque {st : State} : 
  Code.getReturn (part14_state_update st) ↔
  Code.getReturn (part15_state_update (part14_drops (part14_state st))) := by
  simp [part14_state_update, part15_wp]

lemma part15_cumulative_wp {in0 in1 in2 in3 data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Felt} :
  Code.run (start_state ([in0, in1, in2, in3]) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17])) ↔
  Code.getReturn
      (part15_state_update
        ((((({
                    buffers :=
                      ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                          [[some data0, some data1, some data2, some data3, some data4, some data5, some data6,
                              some data7, some data8, some data9, some data10, some data11, some data12, some data13,
                              some data14, some data15, some data16, some data17]])[{ name := "in" : BufferVar }] ←ₘ
                        [[some in0, some in1, some in2, some in3]],
                    bufferWidths :=
                      ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                          (18 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                        (4 : ℕ),
                    cycle := (0 : ℕ), felts := Map.empty, isFailed := False, props := Map.empty,
                    vars :=
                      [{ name := "in" : BufferVar },
                        { name := "data" : BufferVar }] }[props][{ name := "%6" : PropVar }] ←
                  True)[props][{ name := "%28" : PropVar }] ←
                in3 -
                    ((data10 * (64 : Felt) + (data1 * (16 : Felt) + data9 * (8 : Felt) + data8 * (4 : Felt) + data0)) *
                        (2 : Felt) +
                      data13) =
                  (0 : Felt))[props][{ name := "%43" : PropVar }] ←
              (in3 -
                    ((data10 * (64 : Felt) + (data1 * (16 : Felt) + data9 * (8 : Felt) + data8 * (4 : Felt) + data0)) *
                        (2 : Felt) +
                      data13) =
                  (0 : Felt) ∧
                in2 - ((data12 * (8 : Felt) + data2 * (2 : Felt) + data11) * (16 : Felt) + data4 * (4 : Felt) + data3) =
                  (0 : Felt)))[props][{ name := "%58" : PropVar }] ←
            ((in3 -
                    ((data10 * (64 : Felt) + (data1 * (16 : Felt) + data9 * (8 : Felt) + data8 * (4 : Felt) + data0)) *
                        (2 : Felt) +
                      data13) =
                  (0 : Felt) ∧
                in2 - ((data12 * (8 : Felt) + data2 * (2 : Felt) + data11) * (16 : Felt) + data4 * (4 : Felt) + data3) =
                  (0 : Felt)) ∧
              in1 - (data14 * (128 : Felt) + (data15 * (4 : Felt) + data5) * (16 : Felt) + data7 * (4 : Felt) + data6) =
                (0 : Felt)))[felts][{ name := "%61" : FeltVar }] ←
          data16 * (128 : Felt)))  := by
    rewrite [part14_cumulative_wp]
    rewrite [part15_updates_opaque]
    unfold part14_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part14_drops
    -- 5 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths, State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.ComputeDecode.Constraints.WP