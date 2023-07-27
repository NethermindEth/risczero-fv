import Risc0.Gadgets.OneHot1.Constraints.CodeParts

namespace Risc0.OneHot1.Constraints.Code

open MLIRNotation

lemma drop_past_part1 (h0: ⟨"%4"⟩ ≠ x) (h1: ⟨"%1"⟩ ≠ x) (h2: ⟨"%6"⟩ ≠ x) (h3: ⟨"%7"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part1; rest⟧) =
  (Γ st ⟦part1; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part1; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part1; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part1
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_andEqz (by trivial),drop_past_const (by trivial),drop_past_get (by trivial),drop_past_sub (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part1
    rfl
lemma drop_past_part2 (h0: ⟨"%6"⟩ ≠ x) (h1: ⟨"%7"⟩ ≠ x) (h2: ⟨"%8"⟩ ≠ x) (h3: ⟨"%1"⟩ ≠ x) (h4: ⟨"%10"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part2; rest⟧) =
  (Γ st ⟦part2; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part2; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part2; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part2
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_andEqz (by trivial),drop_past_sub (by trivial) (by trivial) (by trivial),drop_past_andEqz (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part2
    rfl

lemma behaviour_with_drops2 :
  Γ st ⟦dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%4"⟩;part2;dropfelt ⟨"%1"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%10"⟩⟧ =
  Γ st ⟦part2;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%10"⟩⟧ := by
    rewrite [MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part2 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def,drop_past_part2 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part2 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), MLIR.run_seq_def]
    rewrite [←MLIR.run_seq_def]
    rfl
lemma behaviour_with_drops1 :
  Γ st ⟦dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;part1;dropfelt ⟨"%4"⟩;part2;dropfelt ⟨"%1"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%10"⟩⟧ =
  Γ st ⟦part1;part2;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%10"⟩⟧ := by
    rewrite [MLIR.run_seq_def]
    rewrite [drop_past_part1 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part1 (by trivial) (by trivial) (by trivial) (by trivial), MLIR.run_seq_def]
    rewrite [behaviour_with_drops2, ←MLIR.run_seq_def]
    rfl
lemma behaviour_with_drops :
  Γ st ⟦part0;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;part1;dropfelt ⟨"%4"⟩;part2;dropfelt ⟨"%1"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%10"⟩⟧ =
  Γ st ⟦part0;part1;part2;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%10"⟩⟧ := by
    rewrite [MLIR.run_seq_def]
    rewrite [behaviour_with_drops1, ←MLIR.run_seq_def]
    rfl
lemma getReturn_ignores_drops :
  getReturn (Γ st ⟦part0;part1;part2;dropfelt ⟨"%0"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%10"⟩⟧)  =
  getReturn (Γ st ⟦part0;part1;part2⟧)  := by
    simp [getReturn, MLIR.run_seq_def, State.constraintsInVar, MLIR.run_dropfelt, State.dropFelts_buffers, State.dropFelts_isFailed, State.dropFelts_props]

end Risc0.OneHot1.Constraints.Code