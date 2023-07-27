import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart30

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part31 on st
def part31_state (st: State) : State :=
  
        (withEqZero
          (Option.get! (State.felts st { name := "%20" : FeltVar }) -
            (Option.get! (State.felts st { name := "%71" : FeltVar }) +
              Option.get!
                (State.felts (st["%69"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (17 : ℕ))
                  { name := "%69" : FeltVar })))
          (((st["%69"] ←ₛ
                getImpl st { name := "data" : BufferVar } (0 : Back) (17 : ℕ))[felts][{ name := "%72" : FeltVar }] ←
              Option.get! (State.felts st { name := "%71" : FeltVar }) +
                Option.get!
                  (State.felts (st["%69"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (17 : ℕ))
                    { name := "%69" : FeltVar }))[felts][{ name := "%73" : FeltVar }] ←
            Option.get! (State.felts st { name := "%20" : FeltVar }) -
              (Option.get! (State.felts st { name := "%71" : FeltVar }) +
                Option.get!
                  (State.felts (st["%69"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (17 : ℕ))
                    { name := "%69" : FeltVar })))) 

def part31_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%20"⟩) ⟨"%71"⟩) ⟨"%69"⟩) ⟨"%72"⟩) ⟨"%73"⟩

-- Run the program from part31 onwards by using part31_state rather than Code.part31
def part31_state_update (st: State): State :=
  part31_drops (part31_state st)

-- Prove that substituting part31_state for Code.part31 produces the same result
lemma part31_wp {st : State} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part31_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) = prog
  unfold Code.part31
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_dropfelt]
  unfold part31_state_update part31_drops part31_state
  rfl

lemma part31_updates_opaque {st : State} : 
  Code.getReturn (part30_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part31_state_update (part30_drops (part30_state st))) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  simp [part30_state_update, part31_wp]

lemma part31_cumulative_wp {in0 in1 in2 in3: Felt} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Option Felt} :
  Code.run (start_state ([in0, in1, in2, in3])) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn
      (part31_state_update
        ({
            buffers :=
              ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                  [[some in0, some in1, some in2, some in3]])[{ name := "data" : BufferVar }] ←ₘ
                [[some (feltBitAnd in3 (6 : Felt) * (1006632961 : Felt)),
                    some (feltBitAnd in3 (96 : Felt) * (1950351361 : Felt)),
                    some (feltBitAnd in2 (96 : Felt) * (1950351361 : Felt)), some (feltBitAnd in2 (3 : Felt)),
                    some (feltBitAnd in2 (12 : Felt) * (1509949441 : Felt)),
                    some (feltBitAnd in1 (48 : Felt) * (1887436801 : Felt)), some (feltBitAnd in1 (3 : Felt)),
                    some (feltBitAnd in1 (12 : Felt) * (1509949441 : Felt)),
                    some (feltBitAnd in3 (8 : Felt) * (1761607681 : Felt)),
                    some (feltBitAnd in3 (16 : Felt) * (1887436801 : Felt)),
                    some (feltBitAnd in3 (128 : Felt) * (1997537281 : Felt)),
                    some (feltBitAnd in2 (16 : Felt) * (1887436801 : Felt)),
                    some (feltBitAnd in2 (128 : Felt) * (1997537281 : Felt)), some (feltBitAnd in3 (1 : Felt)),
                    some (feltBitAnd in1 (128 : Felt) * (1997537281 : Felt)),
                    some (feltBitAnd in1 (64 : Felt) * (1981808641 : Felt)),
                    some (feltBitAnd in0 (128 : Felt) * (1997537281 : Felt)), some (feltBitAnd in0 (127 : Felt))]],
            bufferWidths :=
              ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ (18 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                (4 : ℕ),
            cycle := (0 : ℕ), felts := Map.empty[{ name := "%20" : FeltVar }] ←ₘ in0,
            isFailed :=
              (¬in3 -
                        ((feltBitAnd in3 (128 : Felt) * (1997537281 : Felt) * (64 : Felt) +
                              (feltBitAnd in3 (96 : Felt) * (1950351361 : Felt) * (16 : Felt) +
                                    feltBitAnd in3 (16 : Felt) * (1887436801 : Felt) * (8 : Felt) +
                                  feltBitAnd in3 (8 : Felt) * (1761607681 : Felt) * (4 : Felt) +
                                feltBitAnd in3 (6 : Felt) * (1006632961 : Felt))) *
                            (2 : Felt) +
                          feltBitAnd in3 (1 : Felt)) =
                      (0 : Felt) ∨
                  ¬in2 -
                        ((feltBitAnd in2 (128 : Felt) * (1997537281 : Felt) * (8 : Felt) +
                                  feltBitAnd in2 (96 : Felt) * (1950351361 : Felt) * (2 : Felt) +
                                feltBitAnd in2 (16 : Felt) * (1887436801 : Felt)) *
                              (16 : Felt) +
                            feltBitAnd in2 (12 : Felt) * (1509949441 : Felt) * (4 : Felt) +
                          feltBitAnd in2 (3 : Felt)) =
                      (0 : Felt)) ∨
                ¬in1 -
                      (feltBitAnd in1 (128 : Felt) * (1997537281 : Felt) * (128 : Felt) +
                            (feltBitAnd in1 (64 : Felt) * (1981808641 : Felt) * (4 : Felt) +
                                feltBitAnd in1 (48 : Felt) * (1887436801 : Felt)) *
                              (16 : Felt) +
                          feltBitAnd in1 (12 : Felt) * (1509949441 : Felt) * (4 : Felt) +
                        feltBitAnd in1 (3 : Felt)) =
                    (0 : Felt),
            props := Map.empty,
            vars :=
              [{ name := "in" : BufferVar }, { name := "data" : BufferVar }] }[felts][{ name := "%71" : FeltVar }] ←
          feltBitAnd in0 (128 : Felt) * (1997537281 : Felt) * (128 : Felt)))
      ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14,
        data15, data16, data17])  := by
    rewrite [part30_cumulative_wp]
    rewrite [part31_updates_opaque]
    unfold part30_state
    try simplify_get_hack
    MLIR_states_updates
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates
    unfold part30_drops
    -- 5 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are statements after an if
    try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

lemma closed_form {in0 in1 in2 in3: Felt} :
  Code.run (start_state [in0,in1,in2,in3]) ([data0,data1,data2,data3,data4,data5,data6,data7,data8,data9,data10,data11,data12,data13,data14,data15,data16,data17]) ↔
   (some (feltBitAnd in3 (6 : Felt) * (1006632961 : Felt)) = data0 ∧
        some (feltBitAnd in3 (96 : Felt) * (1950351361 : Felt)) = data1 ∧
          some (feltBitAnd in2 (96 : Felt) * (1950351361 : Felt)) = data2 ∧
            some (feltBitAnd in2 (3 : Felt)) = data3 ∧
              some (feltBitAnd in2 (12 : Felt) * (1509949441 : Felt)) = data4 ∧
                some (feltBitAnd in1 (48 : Felt) * (1887436801 : Felt)) = data5 ∧
                  some (feltBitAnd in1 (3 : Felt)) = data6 ∧
                    some (feltBitAnd in1 (12 : Felt) * (1509949441 : Felt)) = data7 ∧
                      some (feltBitAnd in3 (8 : Felt) * (1761607681 : Felt)) = data8 ∧
                        some (feltBitAnd in3 (16 : Felt) * (1887436801 : Felt)) = data9 ∧
                          some (feltBitAnd in3 (128 : Felt) * (1997537281 : Felt)) = data10 ∧
                            some (feltBitAnd in2 (16 : Felt) * (1887436801 : Felt)) = data11 ∧
                              some (feltBitAnd in2 (128 : Felt) * (1997537281 : Felt)) = data12 ∧
                                some (feltBitAnd in3 (1 : Felt)) = data13 ∧
                                  some (feltBitAnd in1 (128 : Felt) * (1997537281 : Felt)) = data14 ∧
                                    some (feltBitAnd in1 (64 : Felt) * (1981808641 : Felt)) = data15 ∧
                                      some (feltBitAnd in0 (128 : Felt) * (1997537281 : Felt)) = data16 ∧
                                        some (feltBitAnd in0 (127 : Felt)) = data17) ∧
      ¬(((¬in3 -
                    ((feltBitAnd in3 (128 : Felt) * (1997537281 : Felt) * (64 : Felt) +
                          (feltBitAnd in3 (96 : Felt) * (1950351361 : Felt) * (16 : Felt) +
                                feltBitAnd in3 (16 : Felt) * (1887436801 : Felt) * (8 : Felt) +
                              feltBitAnd in3 (8 : Felt) * (1761607681 : Felt) * (4 : Felt) +
                            feltBitAnd in3 (6 : Felt) * (1006632961 : Felt))) *
                        (2 : Felt) +
                      feltBitAnd in3 (1 : Felt)) =
                  (0 : Felt) ∨
              ¬in2 -
                    ((feltBitAnd in2 (128 : Felt) * (1997537281 : Felt) * (8 : Felt) +
                              feltBitAnd in2 (96 : Felt) * (1950351361 : Felt) * (2 : Felt) +
                            feltBitAnd in2 (16 : Felt) * (1887436801 : Felt)) *
                          (16 : Felt) +
                        feltBitAnd in2 (12 : Felt) * (1509949441 : Felt) * (4 : Felt) +
                      feltBitAnd in2 (3 : Felt)) =
                  (0 : Felt)) ∨
            ¬in1 -
                  (feltBitAnd in1 (128 : Felt) * (1997537281 : Felt) * (128 : Felt) +
                        (feltBitAnd in1 (64 : Felt) * (1981808641 : Felt) * (4 : Felt) +
                            feltBitAnd in1 (48 : Felt) * (1887436801 : Felt)) *
                          (16 : Felt) +
                      feltBitAnd in1 (12 : Felt) * (1509949441 : Felt) * (4 : Felt) +
                    feltBitAnd in1 (3 : Felt)) =
                (0 : Felt)) ∨
          ¬in0 - (feltBitAnd in0 (128 : Felt) * (1997537281 : Felt) * (128 : Felt) + feltBitAnd in0 (127 : Felt)) =
              (0 : Felt))  := by
    rewrite [part31_cumulative_wp]
    unfold part31_state_update
    unfold part31_state
    try simplify_get_hack
    MLIR_states_updates
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates
    unfold part31_drops
    -- 5 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are statements after an if
    try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]
    unfold Code.getReturn
    simp only
    simp [Map.update_get_wobbly, List.getLast!]
end Risc0.ComputeDecode.Witness.WP