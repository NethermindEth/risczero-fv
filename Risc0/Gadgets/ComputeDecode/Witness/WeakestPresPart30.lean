import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart29

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part30 on st
def part30_state (st: State) : State :=
  
          (((withEqZero
                (Option.get! (State.felts st { name := "%21" }) - Option.get! (State.felts st { name := "%67" }))
                (st[felts][{ name := "%68" }] ←
                  Option.get! (State.felts st { name := "%21" }) -
                    Option.get! (State.felts st { name := "%67" })))["%70"] ←ₛ
              getImpl st { name := "data" } 0 16)[felts][{ name := "%71" }] ←
            Option.get!
                (State.felts
                  ((withEqZero
                      (Option.get! (State.felts st { name := "%21" }) - Option.get! (State.felts st { name := "%67" }))
                      (st[felts][{ name := "%68" }] ←
                        Option.get! (State.felts st { name := "%21" }) -
                          Option.get! (State.felts st { name := "%67" })))["%70"] ←ₛ
                    getImpl st { name := "data" } 0 16)
                  { name := "%70" }) *
              Option.get! (State.felts st { name := "%19" })) 

def part30_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%19"⟩) ⟨"%21"⟩) ⟨"%67"⟩) ⟨"%68"⟩) ⟨"%70"⟩

-- Run the program from part30 onwards by using part30_state rather than Code.part30
def part30_state_update (st: State): State :=
  Γ (part30_drops (part30_state st)) ⟦Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩⟧

-- Prove that substituting part30_state for Code.part30 produces the same result
lemma part30_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part30_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) = prog
  unfold Code.part30
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt]
  unfold part30_state_update part30_drops part30_state
  rfl

lemma part30_updates_opaque {st : State} : 
  Code.getReturn (part29_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part30_state_update (part29_drops (part29_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part29_state_update, part30_wp]

end Risc0.ComputeDecode.Witness.WP