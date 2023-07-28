import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart29

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part30 on st
def part30_state (st: State) : State :=
  
        (((withEqZero
              (Option.get! (State.felts st { name := "%21" : FeltVar }) -
                Option.get! (State.felts st { name := "%67" : FeltVar }))
              (st[felts][{ name := "%68" : FeltVar }] ←
                Option.get! (State.felts st { name := "%21" : FeltVar }) -
                  Option.get! (State.felts st { name := "%67" : FeltVar })))["%70"] ←ₛ
            getImpl st { name := "data" : BufferVar } (0 : Back) (16 : ℕ))[felts][{ name := "%71" : FeltVar }] ←
          Option.get!
              (State.felts
                ((withEqZero
                    (Option.get! (State.felts st { name := "%21" : FeltVar }) -
                      Option.get! (State.felts st { name := "%67" : FeltVar }))
                    (st[felts][{ name := "%68" : FeltVar }] ←
                      Option.get! (State.felts st { name := "%21" : FeltVar }) -
                        Option.get! (State.felts st { name := "%67" : FeltVar })))["%70"] ←ₛ
                  getImpl st { name := "data" : BufferVar } (0 : Back) (16 : ℕ))
                { name := "%70" : FeltVar }) *
            Option.get! (State.felts st { name := "%19" : FeltVar })) 

def part30_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%19"⟩) ⟨"%21"⟩) ⟨"%67"⟩) ⟨"%68"⟩) ⟨"%70"⟩

-- Run the program from part30 onwards by using part30_state rather than Code.part30
def part30_state_update (st: State): State :=
  Γ (part30_drops (part30_state st)) ⟦Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩⟧

-- Prove that substituting part30_state for Code.part30 produces the same result
lemma part30_wp {st : State} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part30_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) = prog
  unfold Code.part30
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part30_state_update part30_drops part30_state
  rfl

lemma part30_updates_opaque {st : State} : 
  Code.getReturn (part29_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part30_state_update (part29_drops (part29_state st))) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  simp [part29_state_update, part30_wp]

lemma part30_cumulative_wp {in0 in1 in2 in3: Felt} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Option Felt} :
  Code.run (start_state ([in0, in1, in2, in3])) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn
      (part30_state_update
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
            cycle := (0 : ℕ),
            felts :=
              ((Map.empty[{ name := "%19" : FeltVar }] ←ₘ (128 : Felt))[{ name := "%21" : FeltVar }] ←ₘ
                  in1)[{ name := "%20" : FeltVar }] ←ₘ
                in0,
            isFailed :=
              (False ∨
                  ¬in3 -
                        ((feltBitAnd in3 (128 : Felt) * (1997537281 : Felt) * (64 : Felt) +
                              (feltBitAnd in3 (96 : Felt) * (1950351361 : Felt) * (16 : Felt) +
                                    feltBitAnd in3 (16 : Felt) * (1887436801 : Felt) * (8 : Felt) +
                                  feltBitAnd in3 (8 : Felt) * (1761607681 : Felt) * (4 : Felt) +
                                feltBitAnd in3 (6 : Felt) * (1006632961 : Felt))) *
                            (2 : Felt) +
                          feltBitAnd in3 (1 : Felt)) =
                      (0 : Felt)) ∨
                ¬in2 -
                      ((feltBitAnd in2 (128 : Felt) * (1997537281 : Felt) * (8 : Felt) +
                                feltBitAnd in2 (96 : Felt) * (1950351361 : Felt) * (2 : Felt) +
                              feltBitAnd in2 (16 : Felt) * (1887436801 : Felt)) *
                            (16 : Felt) +
                          feltBitAnd in2 (12 : Felt) * (1509949441 : Felt) * (4 : Felt) +
                        feltBitAnd in2 (3 : Felt)) =
                    (0 : Felt),
            props := Map.empty,
            vars :=
              [{ name := "in" : BufferVar }, { name := "data" : BufferVar }] }[felts][{ name := "%67" : FeltVar }] ←
          feltBitAnd in1 (128 : Felt) * (1997537281 : Felt) * (128 : Felt) +
                (feltBitAnd in1 (64 : Felt) * (1981808641 : Felt) * (4 : Felt) +
                    feltBitAnd in1 (48 : Felt) * (1887436801 : Felt)) *
                  (16 : Felt) +
              feltBitAnd in1 (12 : Felt) * (1509949441 : Felt) * (4 : Felt) +
            feltBitAnd in1 (3 : Felt)))
      ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14,
        data15, data16, data17])  := by
    rewrite [part29_cumulative_wp]
    rewrite [part30_updates_opaque]
    unfold part29_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part29_drops
    -- 6 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.ComputeDecode.Witness.WP