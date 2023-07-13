import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart7

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part8 on st
def part8_state (st: State) : State :=
  
        ((((st["%32"] ←ₛ
                getImpl st { name := "data" : BufferVar } (0 : Back) (11 : ℕ))[felts][{ name := "%38" : FeltVar }] ←
              Option.get! (State.felts st { name := "%37" : FeltVar }) +
                Option.get!
                  (State.felts (st["%32"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (11 : ℕ))
                    { name := "%32" : FeltVar }))[felts][{ name := "%39" : FeltVar }] ←
            (Option.get! (State.felts st { name := "%37" : FeltVar }) +
                Option.get!
                  (State.felts (st["%32"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (11 : ℕ))
                    { name := "%32" : FeltVar })) *
              Option.get! (State.felts st { name := "%1" : FeltVar }))[felts][{ name := "%40" : FeltVar }] ←
          (Option.get! (State.felts st { name := "%37" : FeltVar }) +
                Option.get!
                  (State.felts (st["%32"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (11 : ℕ))
                    { name := "%32" : FeltVar })) *
              Option.get! (State.felts st { name := "%1" : FeltVar }) +
            Option.get! (State.felts st { name := "%31" : FeltVar })) 

def part8_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%31"⟩) ⟨"%37"⟩) ⟨"%32"⟩) ⟨"%38"⟩) ⟨"%39"⟩

-- Run the program from part8 onwards by using part8_state rather than Code.part8
def part8_state_update (st: State): State :=
  Γ (part8_drops (part8_state st)) ⟦Code.part9;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%63"⟩⟧

-- Prove that substituting part8_state for Code.part8 produces the same result
lemma part8_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part8;dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part9;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%63"⟩) st) ↔
  Code.getReturn (part8_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%31"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%39"⟩;Code.part9;dropfelt ⟨"%40"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%9"⟩;Code.part10;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part11;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%50"⟩;Code.part12;dropfelt ⟨"%51"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%53"⟩;Code.part13;dropfelt ⟨"%46"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%44"⟩;Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%63"⟩) = prog
  unfold Code.part8
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part8_state_update part8_drops part8_state
  rfl

lemma part8_updates_opaque {st : State} : 
  Code.getReturn (part7_state_update st) ↔
  Code.getReturn (part8_state_update (part7_drops (part7_state st))) := by
  simp [part7_state_update, part8_wp]

lemma part8_cumulative_wp {x0 x1 x2 x3 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17: Felt} :
  Code.run (start_state [x0,x1,x2,x3] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17])) ↔
  Code.getReturn
      (part8_state_update
        (((((({
                      buffers :=
                        ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                            [[some y0, some y1, some y2, some y3, some y4, some y5, some y6, some y7, some y8, some y9,
                                some y10, some y11, some y12, some y13, some y14, some y15, some y16,
                                some y17]])[{ name := "in" : BufferVar }] ←ₘ
                          [[some x0, some x1, some x2, some x3]],
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
              x3 -
                  ((y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) * (2 : Felt) +
                    y13) =
                (0 : Felt))[felts][{ name := "%31" : FeltVar }] ←
            y4 * (4 : Felt))[felts][{ name := "%37" : FeltVar }] ←
          y12 * (8 : Felt) + y2 * (2 : Felt)))  := by
    rewrite [part7_cumulative_wp]
    rewrite [part8_updates_opaque]
    unfold part7_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part7_drops
    -- 6 drops
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