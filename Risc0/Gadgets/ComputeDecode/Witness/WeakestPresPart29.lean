import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart28

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part29 on st
def part29_state (st: State) : State :=
  
          ((((st[felts][{ name := "%65" : FeltVar }] ←
                  Option.get! (State.felts st { name := "%64" : FeltVar }) +
                    Option.get! (State.felts st { name := "%62" : FeltVar }))[felts][{ name := "%66" : FeltVar }] ←
                Option.get! (State.felts st { name := "%64" : FeltVar }) +
                    Option.get! (State.felts st { name := "%62" : FeltVar }) +
                  Option.get! (State.felts st { name := "%57" : FeltVar }))["%55"] ←ₛ
              getImpl st { name := "data" : BufferVar } (0 : Back) (6 : ℕ))[felts][{ name := "%67" : FeltVar }] ←
            Option.get! (State.felts st { name := "%64" : FeltVar }) +
                  Option.get! (State.felts st { name := "%62" : FeltVar }) +
                Option.get! (State.felts st { name := "%57" : FeltVar }) +
              Option.get!
                (State.felts
                  (((st[felts][{ name := "%65" : FeltVar }] ←
                        Option.get! (State.felts st { name := "%64" : FeltVar }) +
                          Option.get!
                            (State.felts st { name := "%62" : FeltVar }))[felts][{ name := "%66" : FeltVar }] ←
                      Option.get! (State.felts st { name := "%64" : FeltVar }) +
                          Option.get! (State.felts st { name := "%62" : FeltVar }) +
                        Option.get! (State.felts st { name := "%57" : FeltVar }))["%55"] ←ₛ
                    getImpl st { name := "data" : BufferVar } (0 : Back) (6 : ℕ))
                  { name := "%55" : FeltVar })) 

def part29_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%57"⟩) ⟨"%62"⟩) ⟨"%64"⟩) ⟨"%65"⟩) ⟨"%66"⟩) ⟨"%55"⟩

-- Run the program from part29 onwards by using part29_state rather than Code.part29
def part29_state_update (st: State): State :=
  Γ (part29_drops (part29_state st)) ⟦Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩⟧

-- Prove that substituting part29_state for Code.part29 produces the same result
lemma part29_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part29_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) = prog
  unfold Code.part29
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part29_state_update part29_drops part29_state
  rfl

lemma part29_updates_opaque {st : State} : 
  Code.getReturn (part28_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part29_state_update (part28_drops (part28_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part28_state_update, part29_wp]

lemma part29_cumulative_wp {x0 x1 x2 x3: Felt} :
  Code.run (start_state [x0,x1,x2,x3]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17] ↔
  Code.getReturn
        (part29_state_update
          ((({
                  buffers :=
                    ((fun x => Map.empty x)[{ name := "in" : BufferVar }] ←ₘ
                        [[some x0, some x1, some x2, some x3]])[{ name := "data" : BufferVar }] ←ₘ
                      [[some (feltBitAnd x3 (6 : Felt) * (1006632961 : Felt)),
                          some (feltBitAnd x3 (96 : Felt) * (1950351361 : Felt)),
                          some (feltBitAnd x2 (96 : Felt) * (1950351361 : Felt)), some (feltBitAnd x2 (3 : Felt)),
                          some (feltBitAnd x2 (12 : Felt) * (1509949441 : Felt)),
                          some (feltBitAnd x1 (48 : Felt) * (1887436801 : Felt)), some (feltBitAnd x1 (3 : Felt)),
                          some (feltBitAnd x1 (12 : Felt) * (1509949441 : Felt)),
                          some (feltBitAnd x3 (8 : Felt) * (1761607681 : Felt)),
                          some (feltBitAnd x3 (16 : Felt) * (1887436801 : Felt)),
                          some (feltBitAnd x3 (128 : Felt) * (1997537281 : Felt)),
                          some (feltBitAnd x2 (16 : Felt) * (1887436801 : Felt)),
                          some (feltBitAnd x2 (128 : Felt) * (1997537281 : Felt)), some (feltBitAnd x3 (1 : Felt)),
                          some (feltBitAnd x1 (128 : Felt) * (1997537281 : Felt)),
                          some (feltBitAnd x1 (64 : Felt) * (1981808641 : Felt)),
                          some (feltBitAnd x0 (128 : Felt) * (1997537281 : Felt)), some (feltBitAnd x0 (127 : Felt))]],
                  bufferWidths :=
                    ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ
                        (18 : ℕ))[{ name := "in" : BufferVar }] ←ₘ
                      (4 : ℕ),
                  constraints :=
                    [x2 -
                          ((feltBitAnd x2 (128 : Felt) * (1997537281 : Felt) * (8 : Felt) +
                                    feltBitAnd x2 (96 : Felt) * (1950351361 : Felt) * (2 : Felt) +
                                  feltBitAnd x2 (16 : Felt) * (1887436801 : Felt)) *
                                (16 : Felt) +
                              feltBitAnd x2 (12 : Felt) * (1509949441 : Felt) * (4 : Felt) +
                            feltBitAnd x2 (3 : Felt)) =
                        (0 : Felt),
                      x3 -
                          ((feltBitAnd x3 (128 : Felt) * (1997537281 : Felt) * (64 : Felt) +
                                (feltBitAnd x3 (96 : Felt) * (1950351361 : Felt) * (16 : Felt) +
                                      feltBitAnd x3 (16 : Felt) * (1887436801 : Felt) * (8 : Felt) +
                                    feltBitAnd x3 (8 : Felt) * (1761607681 : Felt) * (4 : Felt) +
                                  feltBitAnd x3 (6 : Felt) * (1006632961 : Felt))) *
                              (2 : Felt) +
                            feltBitAnd x3 (1 : Felt)) =
                        (0 : Felt)],
                  cycle := (0 : ℕ),
                  felts :=
                    ((Map.empty[{ name := "%19" : FeltVar }] ←ₘ (128 : Felt))[{ name := "%21" : FeltVar }] ←ₘ
                        x1)[{ name := "%20" : FeltVar }] ←ₘ
                      x0,
                  isFailed := false, props := Map.empty,
                  vars :=
                    [{ name := "in" : BufferVar },
                      { name := "data" : BufferVar }] }[felts][{ name := "%57" : FeltVar }] ←
                feltBitAnd x1 (12 : Felt) * (1509949441 : Felt) * (4 : Felt))[felts][{ name := "%62" : FeltVar }] ←
              (feltBitAnd x1 (64 : Felt) * (1981808641 : Felt) * (4 : Felt) +
                  feltBitAnd x1 (48 : Felt) * (1887436801 : Felt)) *
                (16 : Felt))[felts][{ name := "%64" : FeltVar }] ←
            feltBitAnd x1 (128 : Felt) * (1997537281 : Felt) * (128 : Felt))) =
      [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17]  := by
    rewrite [part28_cumulative_wp]
    rewrite [part29_updates_opaque]
    unfold part28_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part28_drops
    -- 5 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.constraints_if_eq_if_constraints,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.ComputeDecode.Witness.WP