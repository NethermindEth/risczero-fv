import Risc0.Gadgets.OneHot20.Witness.CodeParts

namespace Risc0.OneHot20.Witness.Code

open MLIRNotation

lemma drop_past_part1 (h0: ⟨"%74"⟩ ≠ x) (h1: ⟨"%18"⟩ ≠ x) (h2: ⟨"%75"⟩ ≠ x) (h3: ⟨"%17"⟩ ≠ x) (h4: ⟨"%23"⟩ ≠ x) (h5: ⟨"%76"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part1; rest⟧) =
  (Γ st ⟦part1; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part1; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part1; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part1
    rewrite [drop_sequencing_nndn]
    rewrite[drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_set (by trivial),drop_past_const (by trivial),drop_past_bitAnd (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_nndn]
    rewrite [h_rhs]
    unfold part1
    rfl
lemma drop_past_part2 (h0: ⟨"%16"⟩ ≠ x) (h1: ⟨"%76"⟩ ≠ x) (h2: ⟨"%77"⟩ ≠ x) (h3: ⟨"%15"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part2; rest⟧) =
  (Γ st ⟦part2; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part2; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part2; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part2
    rewrite [drop_sequencing_dnnd]
    rewrite[drop_past_const (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_set (by trivial),drop_past_const (by trivial)]
    rewrite [←drop_sequencing_dnnd]
    rewrite [h_rhs]
    unfold part2
    rfl
lemma drop_past_part3 (h0: ⟨"%23"⟩ ≠ x) (h1: ⟨"%15"⟩ ≠ x) (h2: ⟨"%78"⟩ ≠ x) (h3: ⟨"%14"⟩ ≠ x) (h4: ⟨"%79"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part3; rest⟧) =
  (Γ st ⟦part3; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part3; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part3; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part3
    rewrite [drop_sequencing_ndnn]
    rewrite[drop_past_bitAnd (by trivial) (by trivial) (by trivial),drop_past_const (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_set (by trivial)]
    rewrite [←drop_sequencing_ndnn]
    rewrite [h_rhs]
    unfold part3
    rfl
lemma drop_past_part4 (h0: ⟨"%13"⟩ ≠ x) (h1: ⟨"%23"⟩ ≠ x) (h2: ⟨"%80"⟩ ≠ x) (h3: ⟨"%12"⟩ ≠ x) (h4: ⟨"%81"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part4; rest⟧) =
  (Γ st ⟦part4; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part4; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part4; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part4
    rewrite [drop_sequencing_dndn]
    rewrite[drop_past_const (by trivial),drop_past_bitAnd (by trivial) (by trivial) (by trivial),drop_past_const (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dndn]
    rewrite [h_rhs]
    unfold part4
    rfl
lemma drop_past_part5 (h0: ⟨"%81"⟩ ≠ x) (h1: ⟨"%10"⟩ ≠ x) (h2: ⟨"%23"⟩ ≠ x) (h3: ⟨"%82"⟩ ≠ x) (h4: ⟨"%9"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part5; rest⟧) =
  (Γ st ⟦part5; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part5; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part5; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part5
    rewrite [drop_sequencing_ndnd]
    rewrite[drop_past_set (by trivial),drop_past_const (by trivial),drop_past_bitAnd (by trivial) (by trivial) (by trivial),drop_past_const (by trivial)]
    rewrite [←drop_sequencing_ndnd]
    rewrite [h_rhs]
    unfold part5
    rfl
lemma drop_past_part6 (h0: ⟨"%82"⟩ ≠ x) (h1: ⟨"%9"⟩ ≠ x) (h2: ⟨"%83"⟩ ≠ x) (h3: ⟨"%8"⟩ ≠ x) (h4: ⟨"%23"⟩ ≠ x) (h5: ⟨"%84"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part6; rest⟧) =
  (Γ st ⟦part6; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part6; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part6; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part6
    rewrite [drop_sequencing_nndn]
    rewrite[drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_set (by trivial),drop_past_const (by trivial),drop_past_bitAnd (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_nndn]
    rewrite [h_rhs]
    unfold part6
    rfl
lemma drop_past_part7 (h0: ⟨"%84"⟩ ≠ x) (h1: ⟨"%22"⟩ ≠ x) (h2: ⟨"%19"⟩ ≠ x) (h3: ⟨"%85"⟩ ≠ x) (h4: ⟨"%18"⟩ ≠ x) (h5: ⟨"%86"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part7; rest⟧) =
  (Γ st ⟦part7; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part7; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part7; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part7
    rewrite [drop_sequencing_ndnn]
    rewrite[drop_past_set (by trivial),drop_past_get (by trivial),drop_past_bitAnd (by trivial) (by trivial) (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_ndnn]
    rewrite [h_rhs]
    unfold part7
    rfl
lemma drop_past_part8 (h0: ⟨"%86"⟩ ≠ x) (h1: ⟨"%22"⟩ ≠ x) (h2: ⟨"%17"⟩ ≠ x) (h3: ⟨"%87"⟩ ≠ x) (h4: ⟨"%16"⟩ ≠ x) (h5: ⟨"%88"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part8; rest⟧) =
  (Γ st ⟦part8; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part8; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part8; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part8
    rewrite [drop_sequencing_nnnn]
    rewrite[drop_past_set (by trivial),drop_past_bitAnd (by trivial) (by trivial) (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_set (by trivial)]
    rewrite [←drop_sequencing_nnnn]
    rewrite [h_rhs]
    unfold part8
    rfl
lemma drop_past_part9 (h0: ⟨"%22"⟩ ≠ x) (h1: ⟨"%15"⟩ ≠ x) (h2: ⟨"%89"⟩ ≠ x) (h3: ⟨"%14"⟩ ≠ x) (h4: ⟨"%90"⟩ ≠ x) (h5: ⟨"%6"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part9; rest⟧) =
  (Γ st ⟦part9; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part9; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part9; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part9
    rewrite [drop_sequencing_nnnd]
    rewrite[drop_past_bitAnd (by trivial) (by trivial) (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_set (by trivial),drop_past_const (by trivial)]
    rewrite [←drop_sequencing_nnnd]
    rewrite [h_rhs]
    unfold part9
    rfl
lemma drop_past_part10 (h0: ⟨"%22"⟩ ≠ x) (h1: ⟨"%6"⟩ ≠ x) (h2: ⟨"%91"⟩ ≠ x) (h3: ⟨"%5"⟩ ≠ x) (h4: ⟨"%92"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part10; rest⟧) =
  (Γ st ⟦part10; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part10; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part10; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part10
    rewrite [drop_sequencing_ndnn]
    rewrite[drop_past_bitAnd (by trivial) (by trivial) (by trivial),drop_past_const (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_set (by trivial)]
    rewrite [←drop_sequencing_ndnn]
    rewrite [h_rhs]
    unfold part10
    rfl
lemma drop_past_part11 (h0: ⟨"%4"⟩ ≠ x) (h1: ⟨"%22"⟩ ≠ x) (h2: ⟨"%93"⟩ ≠ x) (h3: ⟨"%21"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part11; rest⟧) =
  (Γ st ⟦part11; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part11; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part11; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part11
    rewrite [drop_sequencing_dnnd]
    rewrite[drop_past_const (by trivial),drop_past_bitAnd (by trivial) (by trivial) (by trivial),drop_past_set (by trivial),drop_past_get (by trivial)]
    rewrite [←drop_sequencing_dnnd]
    rewrite [h_rhs]
    unfold part11
    rfl
lemma drop_past_part12 (h0: ⟨"%21"⟩ ≠ x) (h1: ⟨"%19"⟩ ≠ x) (h2: ⟨"%94"⟩ ≠ x) (h3: ⟨"%18"⟩ ≠ x) (h4: ⟨"%95"⟩ ≠ x) (h5: ⟨"%3"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part12; rest⟧) =
  (Γ st ⟦part12; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part12; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part12; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part12
    rewrite [drop_sequencing_nnnd]
    rewrite[drop_past_bitAnd (by trivial) (by trivial) (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_set (by trivial),drop_past_const (by trivial)]
    rewrite [←drop_sequencing_nnnd]
    rewrite [h_rhs]
    unfold part12
    rfl
lemma drop_past_part13 (h0: ⟨"%21"⟩ ≠ x) (h1: ⟨"%3"⟩ ≠ x) (h2: ⟨"%96"⟩ ≠ x) (h3: ⟨"%2"⟩ ≠ x) (h4: ⟨"%97"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part13; rest⟧) =
  (Γ st ⟦part13; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part13; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part13; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part13
    rewrite [drop_sequencing_ndnn]
    rewrite[drop_past_bitAnd (by trivial) (by trivial) (by trivial),drop_past_const (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_set (by trivial)]
    rewrite [←drop_sequencing_ndnn]
    rewrite [h_rhs]
    unfold part13
    rfl
lemma drop_past_part14 (h0: ⟨"%1"⟩ ≠ x) (h1: ⟨"%21"⟩ ≠ x) (h2: ⟨"%98"⟩ ≠ x) (h3: ⟨"%14"⟩ ≠ x) (h4: ⟨"%99"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part14; rest⟧) =
  (Γ st ⟦part14; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part14; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part14; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part14
    rewrite [drop_sequencing_dnnn]
    rewrite[drop_past_const (by trivial),drop_past_bitAnd (by trivial) (by trivial) (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_set (by trivial)]
    rewrite [←drop_sequencing_dnnn]
    rewrite [h_rhs]
    unfold part14
    rfl
lemma drop_past_part15 (h0: ⟨"%21"⟩ ≠ x) (h1: ⟨"%6"⟩ ≠ x) (h2: ⟨"%100"⟩ ≠ x) (h3: ⟨"%5"⟩ ≠ x) (h4: ⟨"%101"⟩ ≠ x) (h5: ⟨"%4"⟩ ≠ x) (h6: ⟨"%102"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part15; rest⟧) =
  (Γ st ⟦part15; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part15; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part15; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part15
    rewrite [drop_sequencing_nnnn]
    rewrite[drop_past_bitAnd (by trivial) (by trivial) (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_set (by trivial),drop_past_bitAnd (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_nnnn]
    rewrite [h_rhs]
    unfold part15
    rfl
lemma drop_past_part16 (h0: ⟨"%102"⟩ ≠ x) (h1: ⟨"%20"⟩ ≠ x) (h2: ⟨"%19"⟩ ≠ x) (h3: ⟨"%103"⟩ ≠ x) (h4: ⟨"%18"⟩ ≠ x) (h5: ⟨"%104"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part16; rest⟧) =
  (Γ st ⟦part16; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part16; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part16; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part16
    rewrite [drop_sequencing_ndnn]
    rewrite[drop_past_set (by trivial),drop_past_get (by trivial),drop_past_bitAnd (by trivial) (by trivial) (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_ndnn]
    rewrite [h_rhs]
    unfold part16
    rfl
lemma drop_past_part17 (h0: ⟨"%104"⟩ ≠ x) (h1: ⟨"%0"⟩ ≠ x) (h2: ⟨"%20"⟩ ≠ x) (h3: ⟨"%105"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part17; rest⟧) =
  (Γ st ⟦part17; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part17; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part17; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part17
    rewrite [drop_sequencing_ndnn]
    rewrite[drop_past_set (by trivial),drop_past_const (by trivial),drop_past_bitAnd (by trivial) (by trivial) (by trivial),drop_past_set (by trivial)]
    rewrite [←drop_sequencing_ndnn]
    rewrite [h_rhs]
    unfold part17
    rfl
lemma drop_past_part18 (h0: ⟨"%7"⟩ ≠ x) (h1: ⟨"%26"⟩ ≠ x) (h2: ⟨"%27"⟩ ≠ x) (h3: ⟨"%28"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part18; rest⟧) =
  (Γ st ⟦part18; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part18; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part18; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part18
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_const (by trivial),drop_past_get (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_get (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part18
    rfl
lemma drop_past_part19 (h0: ⟨"%28"⟩ ≠ x) (h1: ⟨"%13"⟩ ≠ x) (h2: ⟨"%29"⟩ ≠ x) (h3: ⟨"%30"⟩ ≠ x) (h4: ⟨"%15"⟩ ≠ x) (h5: ⟨"%31"⟩ ≠ x) (h6: ⟨"%32"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part19; rest⟧) =
  (Γ st ⟦part19; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part19; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part19; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part19
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_get (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_add (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part19
    rfl
lemma drop_past_part20 (h0: ⟨"%32"⟩ ≠ x) (h1: ⟨"%27"⟩ ≠ x) (h2: ⟨"%33"⟩ ≠ x) (h3: ⟨"%25"⟩ ≠ x) (h4: ⟨"%34"⟩ ≠ x) (h5: ⟨"%35"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part20; rest⟧) =
  (Γ st ⟦part20; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part20; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part20; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part20
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_add (by trivial) (by trivial) (by trivial),drop_past_get (by trivial),drop_past_add (by trivial) (by trivial) (by trivial),drop_past_get (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part20
    rfl
lemma drop_past_part21 (h0: ⟨"%35"⟩ ≠ x) (h1: ⟨"%3"⟩ ≠ x) (h2: ⟨"%36"⟩ ≠ x) (h3: ⟨"%34"⟩ ≠ x) (h4: ⟨"%37"⟩ ≠ x) (h5: ⟨"%11"⟩ ≠ x) (h6: ⟨"%38"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part21; rest⟧) =
  (Γ st ⟦part21; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part21; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part21; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part21
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_add (by trivial) (by trivial) (by trivial),drop_past_const (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part21
    rfl
lemma drop_past_part22 (h0: ⟨"%24"⟩ ≠ x) (h1: ⟨"%38"⟩ ≠ x) (h2: ⟨"%39"⟩ ≠ x) (h3: ⟨"%23"⟩ ≠ x) (h4: ⟨"%40"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part22; rest⟧) =
  (Γ st ⟦part22; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part22; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part22; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part22
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_get (by trivial),drop_past_add (by trivial) (by trivial) (by trivial),drop_past_sub (by trivial) (by trivial) (by trivial),drop_past_eqz (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part22
    rfl
lemma drop_past_part23 (h0: ⟨"%42"⟩ ≠ x) (h1: ⟨"%7"⟩ ≠ x) (h2: ⟨"%43"⟩ ≠ x) (h3: ⟨"%45"⟩ ≠ x) (h4: ⟨"%11"⟩ ≠ x) (h5: ⟨"%46"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part23; rest⟧) =
  (Γ st ⟦part23; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part23; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part23; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part23
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_get (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_get (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part23
    rfl
lemma drop_past_part24 (h0: ⟨"%47"⟩ ≠ x) (h1: ⟨"%13"⟩ ≠ x) (h2: ⟨"%48"⟩ ≠ x) (h3: ⟨"%46"⟩ ≠ x) (h4: ⟨"%49"⟩ ≠ x) (h5: ⟨"%44"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part24; rest⟧) =
  (Γ st ⟦part24; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part24; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part24; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part24
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_get (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_add (by trivial) (by trivial) (by trivial),drop_past_get (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part24
    rfl
lemma drop_past_part25 (h0: ⟨"%49"⟩ ≠ x) (h1: ⟨"%44"⟩ ≠ x) (h2: ⟨"%50"⟩ ≠ x) (h3: ⟨"%15"⟩ ≠ x) (h4: ⟨"%51"⟩ ≠ x) (h5: ⟨"%43"⟩ ≠ x) (h6: ⟨"%52"⟩ ≠ x) (h7: ⟨"%41"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part25; rest⟧) =
  (Γ st ⟦part25; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part25; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part25; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part25
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_add (by trivial) (by trivial) (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_add (by trivial) (by trivial) (by trivial),drop_past_get (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part25
    rfl
lemma drop_past_part26 (h0: ⟨"%52"⟩ ≠ x) (h1: ⟨"%41"⟩ ≠ x) (h2: ⟨"%53"⟩ ≠ x) (h3: ⟨"%22"⟩ ≠ x) (h4: ⟨"%54"⟩ ≠ x) (h5: ⟨"%56"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part26; rest⟧) =
  (Γ st ⟦part26; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part26; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part26; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part26
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_add (by trivial) (by trivial) (by trivial),drop_past_sub (by trivial) (by trivial) (by trivial),drop_past_eqz (by trivial),drop_past_get (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part26
    rfl
lemma drop_past_part27 (h0: ⟨"%56"⟩ ≠ x) (h1: ⟨"%7"⟩ ≠ x) (h2: ⟨"%57"⟩ ≠ x) (h3: ⟨"%59"⟩ ≠ x) (h4: ⟨"%60"⟩ ≠ x) (h5: ⟨"%58"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part27; rest⟧) =
  (Γ st ⟦part27; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part27; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part27; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part27
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_get (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_get (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part27
    rfl
lemma drop_past_part28 (h0: ⟨"%60"⟩ ≠ x) (h1: ⟨"%58"⟩ ≠ x) (h2: ⟨"%61"⟩ ≠ x) (h3: ⟨"%15"⟩ ≠ x) (h4: ⟨"%62"⟩ ≠ x) (h5: ⟨"%63"⟩ ≠ x) (h6: ⟨"%19"⟩ ≠ x) (h7: ⟨"%64"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part28; rest⟧) =
  (Γ st ⟦part28; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part28; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part28; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part28
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_add (by trivial) (by trivial) (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial),drop_past_get (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part28
    rfl
lemma drop_past_part29 (h0: ⟨"%64"⟩ ≠ x) (h1: ⟨"%62"⟩ ≠ x) (h2: ⟨"%65"⟩ ≠ x) (h3: ⟨"%57"⟩ ≠ x) (h4: ⟨"%66"⟩ ≠ x) (h5: ⟨"%55"⟩ ≠ x) (h6: ⟨"%67"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part29; rest⟧) =
  (Γ st ⟦part29; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part29; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part29; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part29
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_add (by trivial) (by trivial) (by trivial),drop_past_add (by trivial) (by trivial) (by trivial),drop_past_get (by trivial),drop_past_add (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part29
    rfl
lemma drop_past_part30 (h0: ⟨"%21"⟩ ≠ x) (h1: ⟨"%67"⟩ ≠ x) (h2: ⟨"%68"⟩ ≠ x) (h3: ⟨"%70"⟩ ≠ x) (h4: ⟨"%19"⟩ ≠ x) (h5: ⟨"%71"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part30; rest⟧) =
  (Γ st ⟦part30; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part30; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part30; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part30
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_sub (by trivial) (by trivial) (by trivial),drop_past_eqz (by trivial),drop_past_get (by trivial),drop_past_mul (by trivial) (by trivial) (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part30
    rfl
lemma drop_past_part31 (h0: ⟨"%69"⟩ ≠ x) (h1: ⟨"%71"⟩ ≠ x) (h2: ⟨"%72"⟩ ≠ x) (h3: ⟨"%20"⟩ ≠ x) (h4: ⟨"%73"⟩ ≠ x):
  (Γ st ⟦dropfelt x; part31; rest⟧) =
  (Γ st ⟦part31; dropfelt x; rest⟧) := by
    let rhs : State := (Γ st ⟦part31; dropfelt x; rest⟧)
    have h_rhs: rhs = (Γ st ⟦part31; dropfelt x; rest⟧) := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def, MLIR.run_seq_def]
    unfold part31
    rewrite [drop_sequencing_dddd]
    rewrite[drop_past_get (by trivial),drop_past_add (by trivial) (by trivial) (by trivial),drop_past_sub (by trivial) (by trivial) (by trivial),drop_past_eqz (by trivial)]
    rewrite [←drop_sequencing_dddd]
    rewrite [h_rhs]
    unfold part31
    rfl

lemma behaviour_with_drops2 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;part2;rest⟧ =
  Γ st ⟦part2;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def]
    rewrite [drop_past_part2 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part2 (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops3 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;part3;rest⟧ =
  Γ st ⟦part3;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part3 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part3 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part3 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part3 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops4 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;part4;rest⟧ =
  Γ st ⟦part4;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part4 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops5 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;part5;rest⟧ =
  Γ st ⟦part5;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part5 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops6 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;part6;rest⟧ =
  Γ st ⟦part6;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part6 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops7 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;part7;rest⟧ =
  Γ st ⟦part7;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part7 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops8 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;part8;rest⟧ =
  Γ st ⟦part8;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part8 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops9 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;part9;rest⟧ =
  Γ st ⟦part9;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part9 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops10 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;part10;rest⟧ =
  Γ st ⟦part10;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part10 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops11 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;part11;rest⟧ =
  Γ st ⟦part11;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part11 (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops12 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;part12;rest⟧ =
  Γ st ⟦part12;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part12 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops13 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;part13;rest⟧ =
  Γ st ⟦part13;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part13 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops14 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;part14;rest⟧ =
  Γ st ⟦part14;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part14 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops15 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;part15;rest⟧ =
  Γ st ⟦part15;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part15 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops16 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;part16;rest⟧ =
  Γ st ⟦part16;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part16 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops17 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;part17;rest⟧ =
  Γ st ⟦part17;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part17 (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops18 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;part18;rest⟧ =
  Γ st ⟦part18;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part18 (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops19 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;part19;rest⟧ =
  Γ st ⟦part19;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part19 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops20 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;part20;rest⟧ =
  Γ st ⟦part20;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part20 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops21 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;part21;rest⟧ =
  Γ st ⟦part21;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part21 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops22 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;part22;rest⟧ =
  Γ st ⟦part22;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part22 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops23 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;part23;rest⟧ =
  Γ st ⟦part23;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part23 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops24 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;part24;rest⟧ =
  Γ st ⟦part24;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part24 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops25 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;part25;rest⟧ =
  Γ st ⟦part25;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part25 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops26 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;part26;rest⟧ =
  Γ st ⟦part26;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part26 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops27 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;part27;rest⟧ =
  Γ st ⟦part27;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part27 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops28 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;part28;rest⟧ =
  Γ st ⟦part28;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part28 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops29 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;part29;rest⟧ =
  Γ st ⟦part29;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part29 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops30 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;part30;rest⟧ =
  Γ st ⟦part30;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part30 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops31 :
  Γ st ⟦dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;part31;rest⟧ =
  Γ st ⟦part31;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;rest⟧ := by
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rewrite [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial), ←MLIR.run_seq_def]
    rw [drop_past_part31 (by trivial) (by trivial) (by trivial) (by trivial) (by trivial)]
lemma behaviour_with_drops :
  Γ st ⟦part0;part1;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;part2;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;part3;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;part4;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;part5;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;part6;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;part7;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;part8;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;part9;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;part10;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;part11;dropfelt ⟨"%93"⟩;part12;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;part13;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;part14;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;part15;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;part16;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;part17;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;part18;dropfelt ⟨"%26"⟩;part19;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;part20;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;part21;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;part22;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;part23;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;part24;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;part25;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;part26;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;part27;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;part28;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;part29;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;part30;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;part31;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩⟧ =
  Γ st ⟦part0;part1;part2;part3;part4;part5;part6;part7;part8;part9;part10;part11;part12;part13;part14;part15;part16;part17;part18;part19;part20;part21;part22;part23;part24;part25;part26;part27;part28;part29;part30;part31;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩⟧ := by
    let rhs : State := (Γ st ⟦part0;part1;part2;part3;part4;part5;part6;part7;part8;part9;part10;part11;part12;part13;part14;part15;part16;part17;part18;part19;part20;part21;part22;part23;part24;part25;part26;part27;part28;part29;part30;part31;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩⟧)
    have h_rhs : rhs = Γ st ⟦part0;part1;part2;part3;part4;part5;part6;part7;part8;part9;part10;part11;part12;part13;part14;part15;part16;part17;part18;part19;part20;part21;part22;part23;part24;part25;part26;part27;part28;part29;part30;part31;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩⟧ := rfl
    rewrite [←h_rhs]
    rewrite [MLIR.run_seq_def]
    let st0 : State := (Γ st ⟦part0⟧)
    have h_st0 : st0 = (Γ st ⟦part0⟧) := rfl
    rewrite [←h_st0]
    rewrite [MLIR.run_seq_def]
    let st1 : State := (Γ st0 ⟦part1⟧)
    have h_st1 : st1 = (Γ st0 ⟦part1⟧) := rfl
    rewrite [←h_st1]
    rewrite [behaviour_with_drops2]
    rewrite [MLIR.run_seq_def]
    let st2 : State := (Γ st1 ⟦part2⟧)
    have h_st2 : st2 = (Γ st1 ⟦part2⟧) := rfl
    rewrite [←h_st2]
    rewrite [behaviour_with_drops3]
    rewrite [MLIR.run_seq_def]
    let st3 : State := (Γ st2 ⟦part3⟧)
    have h_st3 : st3 = (Γ st2 ⟦part3⟧) := rfl
    rewrite [←h_st3]
    rewrite [behaviour_with_drops4]
    rewrite [MLIR.run_seq_def]
    let st4 : State := (Γ st3 ⟦part4⟧)
    have h_st4 : st4 = (Γ st3 ⟦part4⟧) := rfl
    rewrite [←h_st4]
    rewrite [behaviour_with_drops5]
    rewrite [MLIR.run_seq_def]
    let st5 : State := (Γ st4 ⟦part5⟧)
    have h_st5 : st5 = (Γ st4 ⟦part5⟧) := rfl
    rewrite [←h_st5]
    rewrite [behaviour_with_drops6]
    rewrite [MLIR.run_seq_def]
    let st6 : State := (Γ st5 ⟦part6⟧)
    have h_st6 : st6 = (Γ st5 ⟦part6⟧) := rfl
    rewrite [←h_st6]
    rewrite [behaviour_with_drops7]
    rewrite [MLIR.run_seq_def]
    let st7 : State := (Γ st6 ⟦part7⟧)
    have h_st7 : st7 = (Γ st6 ⟦part7⟧) := rfl
    rewrite [←h_st7]
    rewrite [behaviour_with_drops8]
    rewrite [MLIR.run_seq_def]
    let st8 : State := (Γ st7 ⟦part8⟧)
    have h_st8 : st8 = (Γ st7 ⟦part8⟧) := rfl
    rewrite [←h_st8]
    rewrite [behaviour_with_drops9]
    rewrite [MLIR.run_seq_def]
    let st9 : State := (Γ st8 ⟦part9⟧)
    have h_st9 : st9 = (Γ st8 ⟦part9⟧) := rfl
    rewrite [←h_st9]
    rewrite [behaviour_with_drops10]
    rewrite [MLIR.run_seq_def]
    let st10 : State := (Γ st9 ⟦part10⟧)
    have h_st10 : st10 = (Γ st9 ⟦part10⟧) := rfl
    rewrite [←h_st10]
    rewrite [behaviour_with_drops11]
    rewrite [MLIR.run_seq_def]
    let st11 : State := (Γ st10 ⟦part11⟧)
    have h_st11 : st11 = (Γ st10 ⟦part11⟧) := rfl
    rewrite [←h_st11]
    rewrite [behaviour_with_drops12]
    rewrite [MLIR.run_seq_def]
    let st12 : State := (Γ st11 ⟦part12⟧)
    have h_st12 : st12 = (Γ st11 ⟦part12⟧) := rfl
    rewrite [←h_st12]
    rewrite [behaviour_with_drops13]
    rewrite [MLIR.run_seq_def]
    let st13 : State := (Γ st12 ⟦part13⟧)
    have h_st13 : st13 = (Γ st12 ⟦part13⟧) := rfl
    rewrite [←h_st13]
    rewrite [behaviour_with_drops14]
    rewrite [MLIR.run_seq_def]
    let st14 : State := (Γ st13 ⟦part14⟧)
    have h_st14 : st14 = (Γ st13 ⟦part14⟧) := rfl
    rewrite [←h_st14]
    rewrite [behaviour_with_drops15]
    rewrite [MLIR.run_seq_def]
    let st15 : State := (Γ st14 ⟦part15⟧)
    have h_st15 : st15 = (Γ st14 ⟦part15⟧) := rfl
    rewrite [←h_st15]
    rewrite [behaviour_with_drops16]
    rewrite [MLIR.run_seq_def]
    let st16 : State := (Γ st15 ⟦part16⟧)
    have h_st16 : st16 = (Γ st15 ⟦part16⟧) := rfl
    rewrite [←h_st16]
    rewrite [behaviour_with_drops17]
    rewrite [MLIR.run_seq_def]
    let st17 : State := (Γ st16 ⟦part17⟧)
    have h_st17 : st17 = (Γ st16 ⟦part17⟧) := rfl
    rewrite [←h_st17]
    rewrite [behaviour_with_drops18]
    rewrite [MLIR.run_seq_def]
    let st18 : State := (Γ st17 ⟦part18⟧)
    have h_st18 : st18 = (Γ st17 ⟦part18⟧) := rfl
    rewrite [←h_st18]
    rewrite [behaviour_with_drops19]
    rewrite [MLIR.run_seq_def]
    let st19 : State := (Γ st18 ⟦part19⟧)
    have h_st19 : st19 = (Γ st18 ⟦part19⟧) := rfl
    rewrite [←h_st19]
    rewrite [behaviour_with_drops20]
    rewrite [MLIR.run_seq_def]
    let st20 : State := (Γ st19 ⟦part20⟧)
    have h_st20 : st20 = (Γ st19 ⟦part20⟧) := rfl
    rewrite [←h_st20]
    rewrite [behaviour_with_drops21]
    rewrite [MLIR.run_seq_def]
    let st21 : State := (Γ st20 ⟦part21⟧)
    have h_st21 : st21 = (Γ st20 ⟦part21⟧) := rfl
    rewrite [←h_st21]
    rewrite [behaviour_with_drops22]
    rewrite [MLIR.run_seq_def]
    let st22 : State := (Γ st21 ⟦part22⟧)
    have h_st22 : st22 = (Γ st21 ⟦part22⟧) := rfl
    rewrite [←h_st22]
    rewrite [behaviour_with_drops23]
    rewrite [MLIR.run_seq_def]
    let st23 : State := (Γ st22 ⟦part23⟧)
    have h_st23 : st23 = (Γ st22 ⟦part23⟧) := rfl
    rewrite [←h_st23]
    rewrite [behaviour_with_drops24]
    rewrite [MLIR.run_seq_def]
    let st24 : State := (Γ st23 ⟦part24⟧)
    have h_st24 : st24 = (Γ st23 ⟦part24⟧) := rfl
    rewrite [←h_st24]
    rewrite [behaviour_with_drops25]
    rewrite [MLIR.run_seq_def]
    let st25 : State := (Γ st24 ⟦part25⟧)
    have h_st25 : st25 = (Γ st24 ⟦part25⟧) := rfl
    rewrite [←h_st25]
    rewrite [behaviour_with_drops26]
    rewrite [MLIR.run_seq_def]
    let st26 : State := (Γ st25 ⟦part26⟧)
    have h_st26 : st26 = (Γ st25 ⟦part26⟧) := rfl
    rewrite [←h_st26]
    rewrite [behaviour_with_drops27]
    rewrite [MLIR.run_seq_def]
    let st27 : State := (Γ st26 ⟦part27⟧)
    have h_st27 : st27 = (Γ st26 ⟦part27⟧) := rfl
    rewrite [←h_st27]
    rewrite [behaviour_with_drops28]
    rewrite [MLIR.run_seq_def]
    let st28 : State := (Γ st27 ⟦part28⟧)
    have h_st28 : st28 = (Γ st27 ⟦part28⟧) := rfl
    rewrite [←h_st28]
    rewrite [behaviour_with_drops29]
    rewrite [MLIR.run_seq_def]
    let st29 : State := (Γ st28 ⟦part29⟧)
    have h_st29 : st29 = (Γ st28 ⟦part29⟧) := rfl
    rewrite [←h_st29]
    rewrite [behaviour_with_drops30]
    rewrite [MLIR.run_seq_def]
    let st30 : State := (Γ st29 ⟦part30⟧)
    have h_st30 : st30 = (Γ st29 ⟦part30⟧) := rfl
    rewrite [←h_st30]
    rewrite [behaviour_with_drops31]
    rewrite [MLIR.run_seq_def]
    let st31 : State := (Γ st30 ⟦part31⟧)
    have h_st31 : st31 = (Γ st30 ⟦part31⟧) := rfl
    rewrite [←h_st31]
    rewrite [h_st31, ←MLIR.run_seq_def]
    rewrite [h_st30, ←MLIR.run_seq_def]
    rewrite [h_st29, ←MLIR.run_seq_def]
    rewrite [h_st28, ←MLIR.run_seq_def]
    rewrite [h_st27, ←MLIR.run_seq_def]
    rewrite [h_st26, ←MLIR.run_seq_def]
    rewrite [h_st25, ←MLIR.run_seq_def]
    rewrite [h_st24, ←MLIR.run_seq_def]
    rewrite [h_st23, ←MLIR.run_seq_def]
    rewrite [h_st22, ←MLIR.run_seq_def]
    rewrite [h_st21, ←MLIR.run_seq_def]
    rewrite [h_st20, ←MLIR.run_seq_def]
    rewrite [h_st19, ←MLIR.run_seq_def]
    rewrite [h_st18, ←MLIR.run_seq_def]
    rewrite [h_st17, ←MLIR.run_seq_def]
    rewrite [h_st16, ←MLIR.run_seq_def]
    rewrite [h_st15, ←MLIR.run_seq_def]
    rewrite [h_st14, ←MLIR.run_seq_def]
    rewrite [h_st13, ←MLIR.run_seq_def]
    rewrite [h_st12, ←MLIR.run_seq_def]
    rewrite [h_st11, ←MLIR.run_seq_def]
    rewrite [h_st10, ←MLIR.run_seq_def]
    rewrite [h_st9, ←MLIR.run_seq_def]
    rewrite [h_st8, ←MLIR.run_seq_def]
    rewrite [h_st7, ←MLIR.run_seq_def]
    rewrite [h_st6, ←MLIR.run_seq_def]
    rewrite [h_st5, ←MLIR.run_seq_def]
    rewrite [h_st4, ←MLIR.run_seq_def]
    rewrite [h_st3, ←MLIR.run_seq_def]
    rewrite [h_st2, ←MLIR.run_seq_def]
    rewrite [h_st1, ←MLIR.run_seq_def]
    rw [h_st0, ←MLIR.run_seq_def]
lemma getReturn_ignores_drops :
  getReturn (Γ st ⟦part0;part1;part2;part3;part4;part5;part6;part7;part8;part9;part10;part11;part12;part13;part14;part15;part16;part17;part18;part19;part20;part21;part22;part23;part24;part25;part26;part27;part28;part29;part30;part31;dropfelt ⟨"%74"⟩;dropfelt ⟨"%75"⟩;dropfelt ⟨"%76"⟩;dropfelt ⟨"%77"⟩;dropfelt ⟨"%78"⟩;dropfelt ⟨"%79"⟩;dropfelt ⟨"%80"⟩;dropfelt ⟨"%12"⟩;dropfelt ⟨"%81"⟩;dropfelt ⟨"%10"⟩;dropfelt ⟨"%82"⟩;dropfelt ⟨"%9"⟩;dropfelt ⟨"%83"⟩;dropfelt ⟨"%8"⟩;dropfelt ⟨"%84"⟩;dropfelt ⟨"%85"⟩;dropfelt ⟨"%17"⟩;dropfelt ⟨"%16"⟩;dropfelt ⟨"%86"⟩;dropfelt ⟨"%87"⟩;dropfelt ⟨"%88"⟩;dropfelt ⟨"%89"⟩;dropfelt ⟨"%90"⟩;dropfelt ⟨"%91"⟩;dropfelt ⟨"%92"⟩;dropfelt ⟨"%93"⟩;dropfelt ⟨"%94"⟩;dropfelt ⟨"%95"⟩;dropfelt ⟨"%96"⟩;dropfelt ⟨"%2"⟩;dropfelt ⟨"%97"⟩;dropfelt ⟨"%14"⟩;dropfelt ⟨"%1"⟩;dropfelt ⟨"%98"⟩;dropfelt ⟨"%99"⟩;dropfelt ⟨"%6"⟩;dropfelt ⟨"%5"⟩;dropfelt ⟨"%4"⟩;dropfelt ⟨"%100"⟩;dropfelt ⟨"%101"⟩;dropfelt ⟨"%18"⟩;dropfelt ⟨"%102"⟩;dropfelt ⟨"%103"⟩;dropfelt ⟨"%104"⟩;dropfelt ⟨"%0"⟩;dropfelt ⟨"%105"⟩;dropfelt ⟨"%26"⟩;dropfelt ⟨"%28"⟩;dropfelt ⟨"%29"⟩;dropfelt ⟨"%30"⟩;dropfelt ⟨"%31"⟩;dropfelt ⟨"%27"⟩;dropfelt ⟨"%32"⟩;dropfelt ⟨"%33"⟩;dropfelt ⟨"%25"⟩;dropfelt ⟨"%3"⟩;dropfelt ⟨"%34"⟩;dropfelt ⟨"%35"⟩;dropfelt ⟨"%36"⟩;dropfelt ⟨"%37"⟩;dropfelt ⟨"%23"⟩;dropfelt ⟨"%38"⟩;dropfelt ⟨"%24"⟩;dropfelt ⟨"%39"⟩;dropfelt ⟨"%40"⟩;dropfelt ⟨"%11"⟩;dropfelt ⟨"%42"⟩;dropfelt ⟨"%45"⟩;dropfelt ⟨"%13"⟩;dropfelt ⟨"%46"⟩;dropfelt ⟨"%47"⟩;dropfelt ⟨"%48"⟩;dropfelt ⟨"%43"⟩;dropfelt ⟨"%49"⟩;dropfelt ⟨"%44"⟩;dropfelt ⟨"%50"⟩;dropfelt ⟨"%51"⟩;dropfelt ⟨"%22"⟩;dropfelt ⟨"%52"⟩;dropfelt ⟨"%41"⟩;dropfelt ⟨"%53"⟩;dropfelt ⟨"%54"⟩;dropfelt ⟨"%7"⟩;dropfelt ⟨"%56"⟩;dropfelt ⟨"%59"⟩;dropfelt ⟨"%15"⟩;dropfelt ⟨"%60"⟩;dropfelt ⟨"%58"⟩;dropfelt ⟨"%61"⟩;dropfelt ⟨"%63"⟩;dropfelt ⟨"%57"⟩;dropfelt ⟨"%62"⟩;dropfelt ⟨"%64"⟩;dropfelt ⟨"%65"⟩;dropfelt ⟨"%66"⟩;dropfelt ⟨"%55"⟩;dropfelt ⟨"%19"⟩;dropfelt ⟨"%21"⟩;dropfelt ⟨"%67"⟩;dropfelt ⟨"%68"⟩;dropfelt ⟨"%70"⟩;dropfelt ⟨"%20"⟩;dropfelt ⟨"%71"⟩;dropfelt ⟨"%69"⟩;dropfelt ⟨"%72"⟩;dropfelt ⟨"%73"⟩⟧) =
  getReturn (Γ st ⟦part0;part1;part2;part3;part4;part5;part6;part7;part8;part9;part10;part11;part12;part13;part14;part15;part16;part17;part18;part19;part20;part21;part22;part23;part24;part25;part26;part27;part28;part29;part30;part31⟧) := by
    simp [getReturn, MLIR.run_seq_def, State.constraintsInVar, MLIR.run_dropfelt, State.dropFelts_buffers, State.dropFelts_props]

end Risc0.OneHot20.Witness.Code