import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart53

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part54 on st
def part54_state (st: State) : State :=
  
          (withEqZero
            (Option.get! (State.felts st { name := "%136" : FeltVar }) -
              Option.get! (State.felts st { name := "%18" : FeltVar }))
            ((st[felts][{ name := "%137" : FeltVar }] ←
                Option.get! (State.felts st { name := "%136" : FeltVar }) -
                  Option.get! (State.felts st { name := "%18" : FeltVar }))[felts][{ name := "%19" : FeltVar }] ←
              (0 : Felt))) 

def part54_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%18"⟩) ⟨"%136"⟩) ⟨"%137"⟩) ⟨"%19"⟩

-- Run the program from part54 onwards by using part54_state rather than Code.part54
def part54_state_update (st: State): State :=
  part54_drops (part54_state st)

-- Prove that substituting part54_state for Code.part54 produces the same result
lemma part54_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part54_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) = prog
  unfold Code.part54
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_dropfelt]
  unfold part54_state_update part54_drops part54_state
  rfl

lemma part54_updates_opaque {st : State} : 
  Code.getReturn (part53_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part54_state_update (part53_drops (part53_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part53_state_update, part54_wp]

set_option maxRecDepth 10000000 in
lemma part54_cumulative_wp {x0: Felt} :
  Code.run (start_state [x0]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19] ↔
  Code.getReturn
        (part54_state_update
          ({
              buffers :=
                ((fun x => Map.empty x)[{ name := "code" : BufferVar }] ←ₘ
                    [[some x0]])[{ name := "data" : BufferVar }] ←ₘ
                  [[some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (2 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (16 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (17 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (18 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                      some (if x0 - (19 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))]],
              bufferWidths :=
                ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ (20 : ℕ))[{ name := "code" : BufferVar }] ←ₘ
                  (1 : ℕ),
              constraints :=
                [(x0 - (19 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (19 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (18 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (18 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (17 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (17 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (16 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (16 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (15 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (14 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (13 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (12 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (11 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (10 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (9 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (8 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (7 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (6 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (5 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (4 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (3 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (2 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (2 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 - (1 : Felt) = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (x0 = (0 : Felt) → False) ∨
                    ((1 : Felt) - if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                  (((((((((((((((((((if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                                          if x0 - (2 : Felt) = (0 : Felt) then (2 : Felt)
                                                          else (0 : Felt)) +
                                                        if x0 - (3 : Felt) = (0 : Felt) then (3 : Felt)
                                                        else (0 : Felt)) +
                                                      if x0 - (4 : Felt) = (0 : Felt) then (4 : Felt) else (0 : Felt)) +
                                                    if x0 - (5 : Felt) = (0 : Felt) then (5 : Felt) else (0 : Felt)) +
                                                  if x0 - (6 : Felt) = (0 : Felt) then (6 : Felt) else (0 : Felt)) +
                                                if x0 - (7 : Felt) = (0 : Felt) then (7 : Felt) else (0 : Felt)) +
                                              if x0 - (8 : Felt) = (0 : Felt) then (8 : Felt) else (0 : Felt)) +
                                            if x0 - (9 : Felt) = (0 : Felt) then (9 : Felt) else (0 : Felt)) +
                                          if x0 - (10 : Felt) = (0 : Felt) then (10 : Felt) else (0 : Felt)) +
                                        if x0 - (11 : Felt) = (0 : Felt) then (11 : Felt) else (0 : Felt)) +
                                      if x0 - (12 : Felt) = (0 : Felt) then (12 : Felt) else (0 : Felt)) +
                                    if x0 - (13 : Felt) = (0 : Felt) then (13 : Felt) else (0 : Felt)) +
                                  if x0 - (14 : Felt) = (0 : Felt) then (14 : Felt) else (0 : Felt)) +
                                if x0 - (15 : Felt) = (0 : Felt) then (15 : Felt) else (0 : Felt)) +
                              if x0 - (16 : Felt) = (0 : Felt) then (16 : Felt) else (0 : Felt)) +
                            if x0 - (17 : Felt) = (0 : Felt) then (17 : Felt) else (0 : Felt)) +
                          if x0 - (18 : Felt) = (0 : Felt) then (18 : Felt) else (0 : Felt)) +
                        if x0 - (19 : Felt) = (0 : Felt) then (19 : Felt) else (0 : Felt)) -
                      x0 =
                    (0 : Felt)],
              cycle := (0 : ℕ), felts := Map.empty[{ name := "%18" : FeltVar }] ←ₘ (1 : Felt), isFailed := false,
              props := Map.empty,
              vars :=
                [{ name := "code" : BufferVar },
                  { name := "data" : BufferVar }] }[felts][{ name := "%136" : FeltVar }] ←
            (((((((((((((((((((if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                                  if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                                if x0 - (2 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                              if x0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                            if x0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                          if x0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                        if x0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                      if x0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                    if x0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                  if x0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                if x0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                              if x0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                            if x0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                          if x0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                        if x0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                      if x0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                    if x0 - (16 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                  if x0 - (17 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                if x0 - (18 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
              if x0 - (19 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))) =
      [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19]  := by
    rewrite [part53_cumulative_wp]
    rewrite [part54_updates_opaque]
    unfold part53_state
    try simplify_get_hack
    MLIR_states_updates
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates
    unfold part53_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are statements after an if
    try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.constraints_if_eq_if_constraints,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

lemma closed_form {x0: Felt} :
  Code.run (start_state [x0]) = [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15,y16,y17,y18,y19] ↔
   some (if x0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y0 ∧
      some (if x0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y1 ∧
        some (if x0 - (2 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y2 ∧
          some (if x0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y3 ∧
            some (if x0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y4 ∧
              some (if x0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y5 ∧
                some (if x0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y6 ∧
                  some (if x0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y7 ∧
                    some (if x0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y8 ∧
                      some (if x0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y9 ∧
                        some (if x0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y10 ∧
                          some (if x0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y11 ∧
                            some (if x0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y12 ∧
                              some (if x0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y13 ∧
                                some (if x0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y14 ∧
                                  some (if x0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y15 ∧
                                    some (if x0 - (16 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y16 ∧
                                      some (if x0 - (17 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y17 ∧
                                        some (if x0 - (18 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = y18 ∧
                                          some (if x0 - (19 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) =
                                            y19  := by
    rewrite [part54_cumulative_wp]
    unfold part54_state_update
    unfold part54_state
    try simplify_get_hack
    MLIR_states_updates
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates
    unfold part54_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are statements after an if
    try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.constraints_if_eq_if_constraints,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]
    unfold Code.getReturn
    simp only
    simp [Map.update_get_wobbly, List.getLast!]
end Risc0.OneHot20.Witness.WP