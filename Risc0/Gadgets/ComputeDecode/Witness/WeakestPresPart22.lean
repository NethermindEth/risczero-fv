import Risc0.State
import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart21

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part22 on st
def part22_state (st: State) : State :=
  
        (withEqZero
          (Option.get! (State.felts st { name := "%23" : FeltVar }) -
            (Option.get! (State.felts st { name := "%38" : FeltVar }) +
              Option.get!
                (State.felts (st["%24"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (13 : ℕ))
                  { name := "%24" : FeltVar })))
          (((st["%24"] ←ₛ
                getImpl st { name := "data" : BufferVar } (0 : Back) (13 : ℕ))[felts][{ name := "%39" : FeltVar }] ←
              Option.get! (State.felts st { name := "%38" : FeltVar }) +
                Option.get!
                  (State.felts (st["%24"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (13 : ℕ))
                    { name := "%24" : FeltVar }))[felts][{ name := "%40" : FeltVar }] ←
            Option.get! (State.felts st { name := "%23" : FeltVar }) -
              (Option.get! (State.felts st { name := "%38" : FeltVar }) +
                Option.get!
                  (State.felts (st["%24"] ←ₛ getImpl st { name := "data" : BufferVar } (0 : Back) (13 : ℕ))
                    { name := "%24" : FeltVar })))) 

def part22_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%23"⟩) ⟨"%38"⟩) ⟨"%24"⟩) ⟨"%39"⟩) ⟨"%40"⟩

-- Run the program from part22 onwards by using part22_state rather than Code.part22
def part22_state_update (st: State): State :=
  Γ (part22_drops (part22_state st)) ⟦Code.part23;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part24;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;Code.part25;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩⟧

-- Prove that substituting part22_state for Code.part22 produces the same result
lemma part22_wp {st : State} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part22;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;Code.part23;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part24;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;Code.part25;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part22_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;Code.part23;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;Code.part24;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;Code.part25;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;Code.part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;Code.part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;Code.part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;Code.part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) = prog
  unfold Code.part22
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part22_state_update part22_drops part22_state
  rfl

lemma part22_updates_opaque {st : State} : 
  Code.getReturn (part21_state_update st) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn (part22_state_update (part21_drops (part21_state st))) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) := by
  simp [part21_state_update, part22_wp]

lemma part22_cumulative_wp {in0 in1 in2 in3: Felt} {data0 data1 data2 data3 data4 data5 data6 data7 data8 data9 data10 data11 data12 data13 data14 data15 data16 data17: Option Felt} :
  Code.run (start_state ([in0, in1, in2, in3])) ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14, data15, data16, data17]) ↔
  Code.getReturn
      (part22_state_update
        ((({
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
                  ((((((Map.empty[{ name := "%19" : FeltVar }] ←ₘ (128 : Felt))[{ name := "%23" : FeltVar }] ←ₘ
                              in3)[{ name := "%15" : FeltVar }] ←ₘ
                            (16 : Felt))[{ name := "%13" : FeltVar }] ←ₘ
                          (8 : Felt))[{ name := "%22" : FeltVar }] ←ₘ
                        in2)[{ name := "%21" : FeltVar }] ←ₘ
                      in1)[{ name := "%20" : FeltVar }] ←ₘ
                    in0,
                isFailed := False, props := Map.empty,
                vars :=
                  [{ name := "in" : BufferVar }, { name := "data" : BufferVar }] }[felts][{ name := "%7" : FeltVar }] ←
              (4 : Felt))[felts][{ name := "%11" : FeltVar }] ←
            (2 : Felt))[felts][{ name := "%38" : FeltVar }] ←
          (feltBitAnd in3 (128 : Felt) * (1997537281 : Felt) * (64 : Felt) +
              (feltBitAnd in3 (96 : Felt) * (1950351361 : Felt) * (16 : Felt) +
                    feltBitAnd in3 (16 : Felt) * (1887436801 : Felt) * (8 : Felt) +
                  feltBitAnd in3 (8 : Felt) * (1761607681 : Felt) * (4 : Felt) +
                feltBitAnd in3 (6 : Felt) * (1006632961 : Felt))) *
            (2 : Felt)))
      ([data0, data1, data2, data3, data4, data5, data6, data7, data8, data9, data10, data11, data12, data13, data14,
        data15, data16, data17])  := by
    rewrite [part21_cumulative_wp]
    rewrite [part22_updates_opaque]
    unfold part21_state
    try simplify_get_hack
    MLIR_states_updates
    -- 0 withEqZeros
    -- rewrite [withEqZero_def]
    -- MLIR_states_updates
    unfold part21_drops
    -- 5 drops
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