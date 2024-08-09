import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart50

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part51 on st
def part51_state (st: State) : State :=
  
        ((withEqZero
            ((st.felts { name := "%67" : FeltVar }).get! *
              ((st.felts { name := "%18" : FeltVar }).get! - (st.felts { name := "%67" : FeltVar }).get!))
            ((st[felts][{ name := "%128" : FeltVar }] ←
                (st.felts { name := "%18" : FeltVar }).get! -
                  (st.felts { name := "%67" : FeltVar }).get!)[felts][{ name := "%129" : FeltVar }] ←
              (st.felts { name := "%67" : FeltVar }).get! *
                ((st.felts { name := "%18" : FeltVar }).get! -
                  (st.felts { name := "%67" : FeltVar }).get!)))[felts][{ name := "%130" : FeltVar }] ←
          (st.felts { name := "%127" : FeltVar }).get! + (st.felts { name := "%67" : FeltVar }).get!) 

def part51_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%67"⟩) ⟨"%127"⟩) ⟨"%128"⟩) ⟨"%129"⟩

-- Run the program from part51 onwards by using part51_state rather than Code.part51
def part51_state_update (st: State): State :=
  Γ (part51_drops (part51_state st)) ⟦Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩⟧

-- Prove that substituting part51_state for Code.part51 produces the same result
lemma part51_wp {st : State} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 data18 data19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) ↔
  Code.getReturn (part51_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) := by
  unfold MLIR.runProgram; try simp only
  generalize eq : (dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) = prog
  unfold Code.part51
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part51_state_update part51_drops part51_state
  rfl

lemma part51_updates_opaque {st : State} : 
  Code.getReturn (part50_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) ↔
  Code.getReturn (part51_state_update (part50_drops (part50_state st))) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) := by
  try simp [part50_state_update, part51_wp]

lemma part51_cumulative_wp {code0: Felt} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 data18 data19: Option Felt} :
  Code.run (start_state ([code0])) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) ↔
  Code.getReturn
      (part51_state_update
        ({
            buffers :=
              (Map.empty[{ name := "code" : BufferVar }] ←ₘ [[some code0]])[{ name := "data" : BufferVar }] ←ₘ
                [[some (if code0 = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (2 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (16 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (17 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (18 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)),
                    some (if code0 - (19 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))]],
            bufferWidths :=
              (Map.empty[{ name := "data" : BufferVar }] ←ₘ (20 : ℕ))[{ name := "code" : BufferVar }] ←ₘ (1 : ℕ),
            cycle := (0 : ℕ),
            felts :=
              (((Map.empty[{ name := "%18" : FeltVar }] ←ₘ (1 : Felt))[{ name := "%67" : FeltVar }] ←ₘ
                    if code0 - (17 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))[{ name := "%70" : FeltVar }] ←ₘ
                  if code0 - (18 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))[{ name := "%73" : FeltVar }] ←ₘ
                if code0 - (19 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt),
            isFailed :=
              ((((((((((((((((¬(((((((((((((((((((if code0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                                                                          if
                                                                                              code0 - (2 : Felt) =
                                                                                                (0 : Felt) then
                                                                                            (2 : Felt)
                                                                                          else (0 : Felt)) +
                                                                                        if
                                                                                            code0 - (3 : Felt) =
                                                                                              (0 : Felt) then
                                                                                          (3 : Felt)
                                                                                        else (0 : Felt)) +
                                                                                      if
                                                                                          code0 - (4 : Felt) =
                                                                                            (0 : Felt) then
                                                                                        (4 : Felt)
                                                                                      else (0 : Felt)) +
                                                                                    if
                                                                                        code0 - (5 : Felt) =
                                                                                          (0 : Felt) then
                                                                                      (5 : Felt)
                                                                                    else (0 : Felt)) +
                                                                                  if
                                                                                      code0 - (6 : Felt) =
                                                                                        (0 : Felt) then
                                                                                    (6 : Felt)
                                                                                  else (0 : Felt)) +
                                                                                if code0 - (7 : Felt) = (0 : Felt) then
                                                                                  (7 : Felt)
                                                                                else (0 : Felt)) +
                                                                              if code0 - (8 : Felt) = (0 : Felt) then
                                                                                (8 : Felt)
                                                                              else (0 : Felt)) +
                                                                            if code0 - (9 : Felt) = (0 : Felt) then
                                                                              (9 : Felt)
                                                                            else (0 : Felt)) +
                                                                          if code0 - (10 : Felt) = (0 : Felt) then
                                                                            (10 : Felt)
                                                                          else (0 : Felt)) +
                                                                        if code0 - (11 : Felt) = (0 : Felt) then
                                                                          (11 : Felt)
                                                                        else (0 : Felt)) +
                                                                      if code0 - (12 : Felt) = (0 : Felt) then
                                                                        (12 : Felt)
                                                                      else (0 : Felt)) +
                                                                    if code0 - (13 : Felt) = (0 : Felt) then (13 : Felt)
                                                                    else (0 : Felt)) +
                                                                  if code0 - (14 : Felt) = (0 : Felt) then (14 : Felt)
                                                                  else (0 : Felt)) +
                                                                if code0 - (15 : Felt) = (0 : Felt) then (15 : Felt)
                                                                else (0 : Felt)) +
                                                              if code0 - (16 : Felt) = (0 : Felt) then (16 : Felt)
                                                              else (0 : Felt)) +
                                                            if code0 - (17 : Felt) = (0 : Felt) then (17 : Felt)
                                                            else (0 : Felt)) +
                                                          if code0 - (18 : Felt) = (0 : Felt) then (18 : Felt)
                                                          else (0 : Felt)) +
                                                        if code0 - (19 : Felt) = (0 : Felt) then (19 : Felt)
                                                        else (0 : Felt)) -
                                                      code0 =
                                                    (0 : Felt) ∨
                                                code0 = (0 : Felt) ∧
                                                  ¬((1 : Felt) -
                                                        if code0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) =
                                                      (0 : Felt)) ∨
                                              code0 - (1 : Felt) = (0 : Felt) ∧
                                                ¬((1 : Felt) -
                                                      if code0 - (1 : Felt) = (0 : Felt) then (1 : Felt)
                                                      else (0 : Felt)) =
                                                    (0 : Felt)) ∨
                                            code0 - (2 : Felt) = (0 : Felt) ∧
                                              ¬((1 : Felt) -
                                                    if code0 - (2 : Felt) = (0 : Felt) then (1 : Felt)
                                                    else (0 : Felt)) =
                                                  (0 : Felt)) ∨
                                          code0 - (3 : Felt) = (0 : Felt) ∧
                                            ¬((1 : Felt) -
                                                  if code0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) =
                                                (0 : Felt)) ∨
                                        code0 - (4 : Felt) = (0 : Felt) ∧
                                          ¬((1 : Felt) -
                                                if code0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) =
                                              (0 : Felt)) ∨
                                      code0 - (5 : Felt) = (0 : Felt) ∧
                                        ¬((1 : Felt) -
                                              if code0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) =
                                            (0 : Felt)) ∨
                                    code0 - (6 : Felt) = (0 : Felt) ∧
                                      ¬((1 : Felt) -
                                            if code0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) =
                                          (0 : Felt)) ∨
                                  code0 - (7 : Felt) = (0 : Felt) ∧
                                    ¬((1 : Felt) - if code0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) =
                                        (0 : Felt)) ∨
                                code0 - (8 : Felt) = (0 : Felt) ∧
                                  ¬((1 : Felt) - if code0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) =
                                      (0 : Felt)) ∨
                              code0 - (9 : Felt) = (0 : Felt) ∧
                                ¬((1 : Felt) - if code0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) =
                                    (0 : Felt)) ∨
                            code0 - (10 : Felt) = (0 : Felt) ∧
                              ¬((1 : Felt) - if code0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) =
                                  (0 : Felt)) ∨
                          code0 - (11 : Felt) = (0 : Felt) ∧
                            ¬((1 : Felt) - if code0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) =
                                (0 : Felt)) ∨
                        code0 - (12 : Felt) = (0 : Felt) ∧
                          ¬((1 : Felt) - if code0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) =
                              (0 : Felt)) ∨
                      code0 - (13 : Felt) = (0 : Felt) ∧
                        ¬((1 : Felt) - if code0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) =
                            (0 : Felt)) ∨
                    code0 - (14 : Felt) = (0 : Felt) ∧
                      ¬((1 : Felt) - if code0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) =
                          (0 : Felt)) ∨
                  code0 - (15 : Felt) = (0 : Felt) ∧
                    ¬((1 : Felt) - if code0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt)) ∨
                code0 - (16 : Felt) = (0 : Felt) ∧
                  ¬((1 : Felt) - if code0 - (16 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
            props := Map.empty,
            vars :=
              [{ name := "code" : BufferVar }, { name := "data" : BufferVar }] }[felts][{ name := "%127" : FeltVar }] ←
          ((((((((((((((((if code0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                          if code0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                        if code0 - (2 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                      if code0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                    if code0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                  if code0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                if code0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                              if code0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                            if code0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                          if code0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                        if code0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                      if code0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                    if code0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                  if code0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                if code0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
              if code0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
            if code0 - (16 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)))
      ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14,
        data15, data16, data17, data18, data19])  := by
    rewrite [part50_cumulative_wp]
    rewrite [part51_updates_opaque]
    unfold part50_state
    try simplify_get_hack
    MLIR_states_updates
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates
    unfold part50_drops
    -- 4 drops
    try simp [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    try simp [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    try simp [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- try simp [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.OneHot20.Witness.WP