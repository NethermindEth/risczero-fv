import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart49

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part50 on st
def part50_state (st: State) : State :=
  
        ((withEqZero
            (Option.get! (State.felts st { name := "%64" : FeltVar }) *
              (Option.get! (State.felts st { name := "%18" : FeltVar }) -
                Option.get! (State.felts st { name := "%64" : FeltVar })))
            ((st[felts][{ name := "%125" : FeltVar }] ←
                Option.get! (State.felts st { name := "%18" : FeltVar }) -
                  Option.get! (State.felts st { name := "%64" : FeltVar }))[felts][{ name := "%126" : FeltVar }] ←
              Option.get! (State.felts st { name := "%64" : FeltVar }) *
                (Option.get! (State.felts st { name := "%18" : FeltVar }) -
                  Option.get! (State.felts st { name := "%64" : FeltVar }))))[felts][{ name := "%127" : FeltVar }] ←
          Option.get! (State.felts st { name := "%124" : FeltVar }) +
            Option.get! (State.felts st { name := "%64" : FeltVar })) 

def part50_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%64"⟩) ⟨"%124"⟩) ⟨"%125"⟩) ⟨"%126"⟩

-- Run the program from part50 onwards by using part50_state rather than Code.part50
def part50_state_update (st: State): State :=
  Γ (part50_drops (part50_state st)) ⟦Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩⟧

-- Prove that substituting part50_state for Code.part50 produces the same result
lemma part50_wp {st : State} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 data18 data19 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part50;dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) ↔
  Code.getReturn (part50_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%64"⟩;dropfelt ⟨"%124"⟩;dropfelt ⟨"%125"⟩;dropfelt ⟨"%126"⟩;Code.part51;dropfelt ⟨"%67"⟩;dropfelt ⟨"%127"⟩;dropfelt ⟨"%128"⟩;dropfelt ⟨"%129"⟩;Code.part52;dropfelt ⟨"%70"⟩;dropfelt ⟨"%130"⟩;dropfelt ⟨"%131"⟩;dropfelt ⟨"%132"⟩;Code.part53;dropfelt ⟨"%73"⟩;dropfelt ⟨"%133"⟩;dropfelt ⟨"%134"⟩;dropfelt ⟨"%135"⟩;Code.part54;dropfelt ⟨"%18"⟩;dropfelt ⟨"%136"⟩;dropfelt ⟨"%137"⟩;dropfelt ⟨"%19"⟩) = prog
  unfold Code.part50
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part50_state_update part50_drops part50_state
  rfl

lemma part50_updates_opaque {st : State} : 
  Code.getReturn (part49_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) ↔
  Code.getReturn (part50_state_update (part49_drops (part49_state st))) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) := by
  simp [part49_state_update, part50_wp]

lemma part50_cumulative_wp {code0: Felt} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 data18 data19: Option Felt} :
  Code.run (start_state ([code0])) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17, data18, data19]) ↔
  Code.getReturn
      (part50_state_update
        ({
            buffers :=
              ((fun x => Map.empty x)[{ name := "code" : BufferVar }] ←ₘ
                  [[some code0]])[{ name := "data" : BufferVar }] ←ₘ
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
              ((fun x => Map.empty x)[{ name := "data" : BufferVar }] ←ₘ (20 : ℕ))[{ name := "code" : BufferVar }] ←ₘ
                (1 : ℕ),
            constraints :=
              [(if code0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                  ((1 : Felt) - if code0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                (if code0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                  ((1 : Felt) - if code0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                (if code0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                  ((1 : Felt) - if code0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                (if code0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                  ((1 : Felt) - if code0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                (if code0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                  ((1 : Felt) - if code0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                (if code0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                  ((1 : Felt) - if code0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                (if code0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                  ((1 : Felt) - if code0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                (if code0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                  ((1 : Felt) - if code0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                (if code0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                  ((1 : Felt) - if code0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                (if code0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                  ((1 : Felt) - if code0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                (if code0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                  ((1 : Felt) - if code0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                (if code0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                  ((1 : Felt) - if code0 - (4 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                (if code0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                  ((1 : Felt) - if code0 - (3 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                (if code0 - (2 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                  ((1 : Felt) - if code0 - (2 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                (if code0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                  ((1 : Felt) - if code0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                (if code0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt) ∨
                  ((1 : Felt) - if code0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) = (0 : Felt),
                (if code0 - (1 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
                                                        (if code0 - (2 : Felt) = (0 : Felt) then (1 : Felt)
                                                          else (0 : Felt)) *
                                                          (2 : Felt) +
                                                      (if code0 - (3 : Felt) = (0 : Felt) then (1 : Felt)
                                                        else (0 : Felt)) *
                                                        (3 : Felt) +
                                                    (if code0 - (4 : Felt) = (0 : Felt) then (1 : Felt)
                                                      else (0 : Felt)) *
                                                      (4 : Felt) +
                                                  (if code0 - (5 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) *
                                                    (5 : Felt) +
                                                (if code0 - (6 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) *
                                                  (6 : Felt) +
                                              (if code0 - (7 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) *
                                                (7 : Felt) +
                                            (if code0 - (8 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) *
                                              (8 : Felt) +
                                          (if code0 - (9 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) *
                                            (9 : Felt) +
                                        (if code0 - (10 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) *
                                          (10 : Felt) +
                                      (if code0 - (11 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) *
                                        (11 : Felt) +
                                    (if code0 - (12 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) *
                                      (12 : Felt) +
                                  (if code0 - (13 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (13 : Felt) +
                                (if code0 - (14 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (14 : Felt) +
                              (if code0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (15 : Felt) +
                            (if code0 - (16 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (16 : Felt) +
                          (if code0 - (17 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (17 : Felt) +
                        (if code0 - (18 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (18 : Felt) +
                      (if code0 - (19 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)) * (19 : Felt) -
                    code0 =
                  (0 : Felt)],
            cycle := (0 : ℕ),
            felts :=
              ((((Map.empty[{ name := "%18" : FeltVar }] ←ₘ (1 : Felt))[{ name := "%64" : FeltVar }] ←ₘ
                      if code0 - (16 : Felt) = (0 : Felt) then (1 : Felt)
                      else (0 : Felt))[{ name := "%67" : FeltVar }] ←ₘ
                    if code0 - (17 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))[{ name := "%70" : FeltVar }] ←ₘ
                  if code0 - (18 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt))[{ name := "%73" : FeltVar }] ←ₘ
                if code0 - (19 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt),
            isFailed := false, props := Map.empty,
            vars :=
              [{ name := "code" : BufferVar }, { name := "data" : BufferVar }] }[felts][{ name := "%124" : FeltVar }] ←
          (((((((((((((((if code0 = (0 : Felt) then (1 : Felt) else (0 : Felt)) +
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
            if code0 - (15 : Felt) = (0 : Felt) then (1 : Felt) else (0 : Felt)))
      ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14,
        data15, data16, data17, data18, data19])  := by
    rewrite [part49_cumulative_wp]
    rewrite [part50_updates_opaque]
    unfold part49_state
    try simplify_get_hack
    MLIR_states_updates
    -- 1 withEqZero
    rewrite [withEqZero_def]
    MLIR_states_updates
    unfold part49_drops
    -- 4 drops
    simp only [State.drop_update_swap, State.drop_update_same]
    rewrite [State.dropFelts]
    simp only [State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle, State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars]
    simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- 0 sets
    -- rewrite [Map.drop_of_updates]
    -- simp only [Map.drop_base, ne_eq, Map.update_drop_swap, Map.update_drop]
    -- there are not any statements after an if
    -- try simp [State.buffers_if_eq_if_buffers,State.bufferWidths_if_eq_if_bufferWidths,State.constraints_if_eq_if_constraints,State.cycle_if_eq_if_cycle,State.felts_if_eq_if_felts,State.isFailed_if_eq_if_isFailed,State.props_if_eq_if_props,State.vars_if_eq_if_vars]

end Risc0.OneHot20.Witness.WP