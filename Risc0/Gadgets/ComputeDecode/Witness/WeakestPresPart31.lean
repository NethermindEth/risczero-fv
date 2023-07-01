import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Witness.Code
import Risc0.Gadgets.ComputeDecode.Witness.WeakestPresPart30

namespace Risc0.ComputeDecode.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part31 on st
def part31_state (st: State) : State :=
  
          (withEqZero
            (Option.get! (State.felts st { name := "%20" }) -
              (Option.get! (State.felts st { name := "%71" }) +
                Option.get! (State.felts (st["%69"] ←ₛ getImpl st { name := "data" } 0 17) { name := "%69" })))
            (((st["%69"] ←ₛ getImpl st { name := "data" } 0 17)[felts][{ name := "%72" }] ←
                Option.get! (State.felts st { name := "%71" }) +
                  Option.get!
                    (State.felts (st["%69"] ←ₛ getImpl st { name := "data" } 0 17)
                      { name := "%69" }))[felts][{ name := "%73" }] ←
              Option.get! (State.felts st { name := "%20" }) -
                (Option.get! (State.felts st { name := "%71" }) +
                  Option.get!
                    (State.felts (st["%69"] ←ₛ getImpl st { name := "data" } 0 17) { name := "%69" })))) 

def part31_drops (st: State) : State :=
  State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (State.dropFelts (st) ⟨"%20"⟩) ⟨"%71"⟩) ⟨"%69"⟩) ⟨"%72"⟩) ⟨"%73"⟩

-- Run the program from part31 onwards by using part31_state rather than Code.part31
def part31_state_update (st: State): State :=
  part31_drops (part31_state st)

-- Prove that substituting part31_state for Code.part31 produces the same result
lemma part31_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 : Option Felt} :
  Code.getReturn (MLIR.runProgram (Code.part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part31_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩) = prog
  unfold Code.part31
  MLIR
  rewrite [←eq]
  rewrite [MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_seq_def,MLIR.run_dropfelt, MLIR.run_dropfelt]
  unfold part31_state_update part31_drops part31_state
  rfl

lemma part31_updates_opaque {st : State} : 
  Code.getReturn (part30_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] ↔
  Code.getReturn (part31_state_update (part30_drops (part30_state st))) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17] := by
  simp [part30_state_update, part31_wp]

end Risc0.ComputeDecode.Witness.WP