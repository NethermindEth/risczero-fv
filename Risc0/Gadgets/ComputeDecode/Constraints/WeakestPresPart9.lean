import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart8

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part9 on st
def part9_state (st: State) : State :=
  
        ((((st["%29"] ←ₛ
                getImpl st { name := "data" : BufferVar } (0 : Back) (3 : ℕ))[felts][{ name := "%41" : FeltVar }] ←
              Option.get! (State.felts st { name := "%40" : FeltVar }) +
                Option.get!
                  (State.felts (st["%29"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (3 : ℕ))
                    { name := "%29" : FeltVar }))["%9"] ←ₛ
            getImpl st { name := "in" : BufferVar } (0 : Back) (2 : ℕ))[felts][{ name := "%42" : FeltVar }] ←
          Option.get!
              (State.felts
                (((st["%29"] ←ₛ
                      getImpl st { name := "data" : BufferVar } (0 : Back)
                        (3 : ℕ))[felts][{ name := "%41" : FeltVar }] ←
                    Option.get! (State.felts st { name := "%40" : FeltVar }) +
                      Option.get!
                        (State.felts (st["%29"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (3 : ℕ))
                          { name := "%29" : FeltVar }))["%9"] ←ₛ
                  getImpl st { name := "in" : BufferVar } (0 : Back) (2 : ℕ))
                { name := "%9" : FeltVar }) -
            (Option.get! (State.felts st { name := "%40" : FeltVar }) +
              Option.get!
                (State.felts (st["%29"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (3 : ℕ))
                  { name := "%29" : FeltVar }))) 

def part9_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%40"⟩) ⟨"%29"⟩) ⟨"%41"⟩) ⟨"%9"⟩

-- Run the program from part9 onwards by using part9_state rather than Code.part9
def part9_state_update (st: State): State :=
  Γ (part9_drops (part9_state st)) ⟦Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%63"⟩⟧

-- Prove that substituting part9_state for Code.part9 produces the same result
lemma part9_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part9;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%63"⟩) st) ↔
  Code.getReturn (part9_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%63"⟩) = prog
  unfold Code.part9
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part9_state_update part9_drops part9_state
  rfl

lemma part9_updates_opaque {st : State} : 
  Code.getReturn (part8_state_update st) ↔
  Code.getReturn (part9_state_update (part8_drops (part8_state st))) := by
  simp [part8_state_update, part9_wp]

lemma part9_cumulative_wp {in0 in1 in2 in3 data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Felt} :
  Code.run (start_state ([in0, in1, in2, in3]) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17])) ↔
  Code.getReturn
      (part9_state_update
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
                    constraints := [], cycle := (0 : ℕ), felts := Map.empty, isFailed := false, props := Map.empty,
                    vars :=
                      [{ name := "in" : BufferVar },
                        { name := "data" : BufferVar }] }[props][{ name := "%6" : PropVar }] ←
                  True)[felts][{ name := "%4" : FeltVar }] ←
                (4 : Felt))[felts][{ name := "%1" : FeltVar }] ←
              (16 : Felt))[props][{ name := "%28" : PropVar }] ←
            in3 -
                ((data10 * (64 : Felt) + (data1 * (16 : Felt) + data9 * (8 : Felt) + data8 * (4 : Felt) + data0)) *
                    (2 : Felt) +
                  data13) =
              (0 : Felt))[felts][{ name := "%40" : FeltVar }] ←
          (data12 * (8 : Felt) + data2 * (2 : Felt) + data11) * (16 : Felt) + data4 * (4 : Felt)))  := by
    rewrite [part8_cumulative_wp]
    rewrite [part9_updates_opaque]
    unfold part8_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part8_drops
    -- 5 drops
    simp only [State.drop_update_swap, State.drop_update_same, State.drop_updateProps_swap]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.constraints_if_eq_if_constraints,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.ComputeDecode.Constraints.WP