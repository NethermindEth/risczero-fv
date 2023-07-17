import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart13

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part14 on st
def part14_state (st: State) : State :=
  
        ((((st[felts][{ name := "%57" : FeltVar }] ←
                Option.get! (State.felts st { name := "%8" : FeltVar }) -
                  Option.get! (State.felts st { name := "%56" : FeltVar }))[props][{ name := "%58" : PropVar }] ←
              (Option.get! (State.props st { name := "%43" : PropVar }) ∧
                Option.get! (State.felts st { name := "%8" : FeltVar }) -
                    Option.get! (State.felts st { name := "%56" : FeltVar }) =
                  (0 : Felt)))["%60"] ←ₛ
            getImpl st { name := "data" : BufferVar } (0 : Back) (16 : ℕ))[felts][{ name := "%61" : FeltVar }] ←
          Option.get!
              (State.felts
                (((st[felts][{ name := "%57" : FeltVar }] ←
                      Option.get! (State.felts st { name := "%8" : FeltVar }) -
                        Option.get! (State.felts st { name := "%56" : FeltVar }))[props][{ name := "%58" : PropVar }] ←
                    (Option.get! (State.props st { name := "%43" : PropVar }) ∧
                      Option.get! (State.felts st { name := "%8" : FeltVar }) -
                          Option.get! (State.felts st { name := "%56" : FeltVar }) =
                        (0 : Felt)))["%60"] ←ₛ
                  getImpl st { name := "data" : BufferVar } (0 : Back) (16 : ℕ))
                { name := "%60" : FeltVar }) *
            Option.get! (State.felts st { name := "%0" : FeltVar })) 

def part14_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%0"⟩) ⟨"%56"⟩) ⟨"%8"⟩) ⟨"%57"⟩) ⟨"%60"⟩

-- Run the program from part14 onwards by using part14_state rather than Code.part14
def part14_state_update (st: State): State :=
  Γ (part14_drops (part14_state st)) ⟦Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%63"⟩⟧

-- Prove that substituting part14_state for Code.part14 produces the same result
lemma part14_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part14;dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%63"⟩) st) ↔
  Code.getReturn (part14_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%0"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%60"⟩;Code.part15;dropfelt ⟨"%61"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%7"⟩;Code.part16;dropfelt ⟨"%63"⟩) = prog
  unfold Code.part14
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part14_state_update part14_drops part14_state
  rfl

lemma part14_updates_opaque {st : State} : 
  Code.getReturn (part13_state_update st) ↔
  Code.getReturn (part14_state_update (part13_drops (part13_state st))) := by
  simp [part13_state_update, part14_wp]

lemma part14_cumulative_wp {x0 x1 x2 x3 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17: Felt} :
  Code.run (start_state [x0,x1,x2,x3] ([y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17])) ↔
  Code.getReturn
      (part14_state_update
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
                    True)[props][{ name := "%28" : PropVar }] ←
                  x3 -
                      ((y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) * (2 : Felt) +
                        y13) =
                    (0 : Felt))[props][{ name := "%43" : PropVar }] ←
                (x3 -
                      ((y10 * (64 : Felt) + (y1 * (16 : Felt) + y9 * (8 : Felt) + y8 * (4 : Felt) + y0)) * (2 : Felt) +
                        y13) =
                    (0 : Felt) ∧
                  x2 - ((y12 * (8 : Felt) + y2 * (2 : Felt) + y11) * (16 : Felt) + y4 * (4 : Felt) + y3) =
                    (0 : Felt)))[felts][{ name := "%0" : FeltVar }] ←
              (128 : Felt))[felts][{ name := "%56" : FeltVar }] ←
            y14 * (128 : Felt) + (y15 * (4 : Felt) + y5) * (16 : Felt) + y7 * (4 : Felt) +
              y6)[felts][{ name := "%8" : FeltVar }] ←
          x1))  := by
    rewrite [part13_cumulative_wp]
    rewrite [part14_updates_opaque]
    unfold part13_state
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part13_drops
    -- 4 drops
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