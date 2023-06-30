import Risc0.Gadgets.ComputeDecode.Witness.CodeReordered

namespace Risc0.ComputeDecode.Witness.Code

open MLIRNotation

def part0 : MLIRProgram :=   "%19" ←ₐ .Const 128; "%23" ←ₐ .Get ⟨"in"⟩ 0 3; nondet ( "%74" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%19"⟩ ); "%18" ←ₐ .Const 1997537281
def part1 : MLIRProgram :=   nondet ( "%75" ←ₐ .Mul ⟨"%74"⟩ ⟨"%18"⟩; ⟨"data"⟩[10] ←ᵢ ⟨"%75"⟩ ); "%17" ←ₐ .Const 96; nondet ( "%76" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%17"⟩ )
def drop_part_part1 (h0: ⟨"%74"⟩ ≠ x) (h1: ⟨"%18"⟩ ≠ x) (h2: ⟨"%75"⟩ ≠ x) (h3: ⟨"%17"⟩ ≠ x) (h4: ⟨"%23"⟩ ≠ x) (h5: ⟨"%76"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part1⟧) =
  State.buffers (Γ st ⟦part1; dropfelt x⟧) := by
    unfold part1
    rewrite[drop_past_mul_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_set_nondet_single (by trivial),MLIR.run_seq_def,drop_past_const (by trivial),MLIR.run_seq_def,drop_past_bitAnd_nondet (by trivial) (by trivial) (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part2 : MLIRProgram :=   "%16" ←ₐ .Const 1950351361; nondet ( "%77" ←ₐ .Mul ⟨"%76"⟩ ⟨"%16"⟩; ⟨"data"⟩[1] ←ᵢ ⟨"%77"⟩ ); "%15" ←ₐ .Const 16
def drop_part_part2 (h0: ⟨"%16"⟩ ≠ x) (h1: ⟨"%76"⟩ ≠ x) (h2: ⟨"%77"⟩ ≠ x) (h3: ⟨"%15"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part2⟧) =
  State.buffers (Γ st ⟦part2; dropfelt x⟧) := by
    unfold part2
    rewrite[drop_past_const (by trivial),MLIR.run_seq_def,drop_past_mul_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_set_nondet_single (by trivial),MLIR.run_seq_def,drop_past_const_single (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part3 : MLIRProgram :=   nondet ( "%78" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%15"⟩ ); "%14" ←ₐ .Const 1887436801; nondet ( "%79" ←ₐ .Mul ⟨"%78"⟩ ⟨"%14"⟩; ⟨"data"⟩[9] ←ᵢ ⟨"%79"⟩ )
def drop_part_part3 (h0: ⟨"%23"⟩ ≠ x) (h1: ⟨"%15"⟩ ≠ x) (h2: ⟨"%78"⟩ ≠ x) (h3: ⟨"%14"⟩ ≠ x) (h4: ⟨"%79"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part3⟧) =
  State.buffers (Γ st ⟦part3; dropfelt x⟧) := by
    unfold part3
    rewrite[drop_past_bitAnd_nondet_single (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_const (by trivial),MLIR.run_seq_def,drop_past_mul_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_set_nondet (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part4 : MLIRProgram :=   "%13" ←ₐ .Const 8; nondet ( "%80" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%13"⟩ ); "%12" ←ₐ .Const 1761607681; nondet ( "%81" ←ₐ .Mul ⟨"%80"⟩ ⟨"%12"⟩ )
def drop_part_part4 (h0: ⟨"%13"⟩ ≠ x) (h1: ⟨"%23"⟩ ≠ x) (h2: ⟨"%80"⟩ ≠ x) (h3: ⟨"%12"⟩ ≠ x) (h4: ⟨"%81"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part4⟧) =
  State.buffers (Γ st ⟦part4; dropfelt x⟧) := by
    unfold part4
    rewrite[drop_past_const (by trivial),MLIR.run_seq_def,drop_past_bitAnd_nondet_single (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_const (by trivial),MLIR.run_seq_def,drop_past_mul_nondet (by trivial) (by trivial) (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part5 : MLIRProgram :=   nondet ( ⟨"data"⟩[8] ←ᵢ ⟨"%81"⟩ ); "%10" ←ₐ .Const 6; nondet ( "%82" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%10"⟩ ); "%9" ←ₐ .Const 1006632961
def drop_part_part5 (h0: ⟨"%81"⟩ ≠ x) (h1: ⟨"%10"⟩ ≠ x) (h2: ⟨"%23"⟩ ≠ x) (h3: ⟨"%82"⟩ ≠ x) (h4: ⟨"%9"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part5⟧) =
  State.buffers (Γ st ⟦part5; dropfelt x⟧) := by
    unfold part5
    rewrite[drop_past_set_nondet_single (by trivial),MLIR.run_seq_def,drop_past_const (by trivial),MLIR.run_seq_def,drop_past_bitAnd_nondet_single (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_const_single (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part6 : MLIRProgram :=   nondet ( "%83" ←ₐ .Mul ⟨"%82"⟩ ⟨"%9"⟩; ⟨"data"⟩[0] ←ᵢ ⟨"%83"⟩ ); "%8" ←ₐ .Const 1; nondet ( "%84" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%8"⟩ )
def drop_part_part6 (h0: ⟨"%82"⟩ ≠ x) (h1: ⟨"%9"⟩ ≠ x) (h2: ⟨"%83"⟩ ≠ x) (h3: ⟨"%8"⟩ ≠ x) (h4: ⟨"%23"⟩ ≠ x) (h5: ⟨"%84"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part6⟧) =
  State.buffers (Γ st ⟦part6; dropfelt x⟧) := by
    unfold part6
    rewrite[drop_past_mul_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_set_nondet_single (by trivial),MLIR.run_seq_def,drop_past_const (by trivial),MLIR.run_seq_def,drop_past_bitAnd_nondet (by trivial) (by trivial) (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part7 : MLIRProgram :=   nondet ( ⟨"data"⟩[13] ←ᵢ ⟨"%84"⟩ ); "%22" ←ₐ .Get ⟨"in"⟩ 0 2; nondet ( "%85" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%19"⟩; "%86" ←ₐ .Mul ⟨"%85"⟩ ⟨"%18"⟩ )
def drop_part_part7 (h0: ⟨"%84"⟩ ≠ x) (h1: ⟨"%22"⟩ ≠ x) (h2: ⟨"%19"⟩ ≠ x) (h3: ⟨"%85"⟩ ≠ x) (h4: ⟨"%18"⟩ ≠ x) (h5: ⟨"%86"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part7⟧) =
  State.buffers (Γ st ⟦part7; dropfelt x⟧) := by
    unfold part7
    rewrite[drop_past_set_nondet_single (by trivial),MLIR.run_seq_def,drop_past_get (by trivial),MLIR.run_seq_def,drop_past_bitAnd_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_mul_nondet (by trivial) (by trivial) (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part8 : MLIRProgram :=   nondet ( ⟨"data"⟩[12] ←ᵢ ⟨"%86"⟩; "%87" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%17"⟩; "%88" ←ₐ .Mul ⟨"%87"⟩ ⟨"%16"⟩; ⟨"data"⟩[2] ←ᵢ ⟨"%88"⟩ )
def drop_part_part8 (h0: ⟨"%86"⟩ ≠ x) (h1: ⟨"%22"⟩ ≠ x) (h2: ⟨"%17"⟩ ≠ x) (h3: ⟨"%87"⟩ ≠ x) (h4: ⟨"%16"⟩ ≠ x) (h5: ⟨"%88"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part8⟧) =
  State.buffers (Γ st ⟦part8; dropfelt x⟧) := by
    unfold part8
    rewrite[drop_past_set_nondet (by trivial),MLIR.run_seq_def,drop_past_bitAnd_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_mul_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_set_nondet (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part9 : MLIRProgram :=   nondet ( "%89" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%15"⟩; "%90" ←ₐ .Mul ⟨"%89"⟩ ⟨"%14"⟩; ⟨"data"⟩[11] ←ᵢ ⟨"%90"⟩ ); "%6" ←ₐ .Const 12
def drop_part_part9 (h0: ⟨"%22"⟩ ≠ x) (h1: ⟨"%15"⟩ ≠ x) (h2: ⟨"%89"⟩ ≠ x) (h3: ⟨"%14"⟩ ≠ x) (h4: ⟨"%90"⟩ ≠ x) (h5: ⟨"%6"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part9⟧) =
  State.buffers (Γ st ⟦part9; dropfelt x⟧) := by
    unfold part9
    rewrite[drop_past_bitAnd_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_mul_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_set_nondet_single (by trivial),MLIR.run_seq_def,drop_past_const_single (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part10 : MLIRProgram :=   nondet ( "%91" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%6"⟩ ); "%5" ←ₐ .Const 1509949441; nondet ( "%92" ←ₐ .Mul ⟨"%91"⟩ ⟨"%5"⟩; ⟨"data"⟩[4] ←ᵢ ⟨"%92"⟩ )
def drop_part_part10 (h0: ⟨"%22"⟩ ≠ x) (h1: ⟨"%6"⟩ ≠ x) (h2: ⟨"%91"⟩ ≠ x) (h3: ⟨"%5"⟩ ≠ x) (h4: ⟨"%92"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part10⟧) =
  State.buffers (Γ st ⟦part10; dropfelt x⟧) := by
    unfold part10
    rewrite[drop_past_bitAnd_nondet_single (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_const (by trivial),MLIR.run_seq_def,drop_past_mul_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_set_nondet (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part11 : MLIRProgram :=   "%4" ←ₐ .Const 3; nondet ( "%93" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%4"⟩; ⟨"data"⟩[3] ←ᵢ ⟨"%93"⟩ ); "%21" ←ₐ .Get ⟨"in"⟩ 0 1
def drop_part_part11 (h0: ⟨"%4"⟩ ≠ x) (h1: ⟨"%22"⟩ ≠ x) (h2: ⟨"%93"⟩ ≠ x) (h3: ⟨"%21"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part11⟧) =
  State.buffers (Γ st ⟦part11; dropfelt x⟧) := by
    unfold part11
    rewrite[drop_past_const (by trivial),MLIR.run_seq_def,drop_past_bitAnd_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_set_nondet_single (by trivial),MLIR.run_seq_def,drop_past_get_single (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part12 : MLIRProgram :=   nondet ( "%94" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%19"⟩; "%95" ←ₐ .Mul ⟨"%94"⟩ ⟨"%18"⟩; ⟨"data"⟩[14] ←ᵢ ⟨"%95"⟩ ); "%3" ←ₐ .Const 64
def drop_part_part12 (h0: ⟨"%21"⟩ ≠ x) (h1: ⟨"%19"⟩ ≠ x) (h2: ⟨"%94"⟩ ≠ x) (h3: ⟨"%18"⟩ ≠ x) (h4: ⟨"%95"⟩ ≠ x) (h5: ⟨"%3"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part12⟧) =
  State.buffers (Γ st ⟦part12; dropfelt x⟧) := by
    unfold part12
    rewrite[drop_past_bitAnd_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_mul_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_set_nondet_single (by trivial),MLIR.run_seq_def,drop_past_const_single (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part13 : MLIRProgram :=   nondet ( "%96" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%3"⟩ ); "%2" ←ₐ .Const 1981808641; nondet ( "%97" ←ₐ .Mul ⟨"%96"⟩ ⟨"%2"⟩; ⟨"data"⟩[15] ←ᵢ ⟨"%97"⟩ )
def drop_part_part13 (h0: ⟨"%21"⟩ ≠ x) (h1: ⟨"%3"⟩ ≠ x) (h2: ⟨"%96"⟩ ≠ x) (h3: ⟨"%2"⟩ ≠ x) (h4: ⟨"%97"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part13⟧) =
  State.buffers (Γ st ⟦part13; dropfelt x⟧) := by
    unfold part13
    rewrite[drop_past_bitAnd_nondet_single (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_const (by trivial),MLIR.run_seq_def,drop_past_mul_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_set_nondet (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part14 : MLIRProgram :=   "%1" ←ₐ .Const 48; nondet ( "%98" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%1"⟩; "%99" ←ₐ .Mul ⟨"%98"⟩ ⟨"%14"⟩; ⟨"data"⟩[5] ←ᵢ ⟨"%99"⟩ )
def drop_part_part14 (h0: ⟨"%1"⟩ ≠ x) (h1: ⟨"%21"⟩ ≠ x) (h2: ⟨"%98"⟩ ≠ x) (h3: ⟨"%14"⟩ ≠ x) (h4: ⟨"%99"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part14⟧) =
  State.buffers (Γ st ⟦part14; dropfelt x⟧) := by
    unfold part14
    rewrite[drop_past_const (by trivial),MLIR.run_seq_def,drop_past_bitAnd_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_mul_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_set_nondet (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part15 : MLIRProgram :=   nondet ( "%100" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%6"⟩; "%101" ←ₐ .Mul ⟨"%100"⟩ ⟨"%5"⟩; ⟨"data"⟩[7] ←ᵢ ⟨"%101"⟩; "%102" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%4"⟩ )
def drop_part_part15 (h0: ⟨"%21"⟩ ≠ x) (h1: ⟨"%6"⟩ ≠ x) (h2: ⟨"%100"⟩ ≠ x) (h3: ⟨"%5"⟩ ≠ x) (h4: ⟨"%101"⟩ ≠ x) (h5: ⟨"%4"⟩ ≠ x) (h6: ⟨"%102"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part15⟧) =
  State.buffers (Γ st ⟦part15; dropfelt x⟧) := by
    unfold part15
    rewrite[drop_past_bitAnd_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_mul_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_set_nondet (by trivial),MLIR.run_seq_def,drop_past_bitAnd_nondet (by trivial) (by trivial) (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part16 : MLIRProgram :=   nondet ( ⟨"data"⟩[6] ←ᵢ ⟨"%102"⟩ ); "%20" ←ₐ .Get ⟨"in"⟩ 0 0; nondet ( "%103" ←ₐ .BitAnd ⟨"%20"⟩ ⟨"%19"⟩; "%104" ←ₐ .Mul ⟨"%103"⟩ ⟨"%18"⟩ )
def drop_part_part16 (h0: ⟨"%102"⟩ ≠ x) (h1: ⟨"%20"⟩ ≠ x) (h2: ⟨"%19"⟩ ≠ x) (h3: ⟨"%103"⟩ ≠ x) (h4: ⟨"%18"⟩ ≠ x) (h5: ⟨"%104"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part16⟧) =
  State.buffers (Γ st ⟦part16; dropfelt x⟧) := by
    unfold part16
    rewrite[drop_past_set_nondet_single (by trivial),MLIR.run_seq_def,drop_past_get (by trivial),MLIR.run_seq_def,drop_past_bitAnd_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_mul_nondet (by trivial) (by trivial) (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part17 : MLIRProgram :=   nondet ( ⟨"data"⟩[16] ←ᵢ ⟨"%104"⟩ ); "%0" ←ₐ .Const 127; nondet ( "%105" ←ₐ .BitAnd ⟨"%20"⟩ ⟨"%0"⟩; ⟨"data"⟩[17] ←ᵢ ⟨"%105"⟩ )
def drop_part_part17 (h0: ⟨"%104"⟩ ≠ x) (h1: ⟨"%0"⟩ ≠ x) (h2: ⟨"%20"⟩ ≠ x) (h3: ⟨"%105"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part17⟧) =
  State.buffers (Γ st ⟦part17; dropfelt x⟧) := by
    unfold part17
    rewrite[drop_past_set_nondet_single (by trivial),MLIR.run_seq_def,drop_past_const (by trivial),MLIR.run_seq_def,drop_past_bitAnd_nondet (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_set_nondet (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part18 : MLIRProgram :=   "%7" ←ₐ .Const 4; "%26" ←ₐ .Get ⟨"data"⟩ 0 8; "%27" ←ₐ .Mul ⟨"%26"⟩ ⟨"%7"⟩; "%28" ←ₐ .Get ⟨"data"⟩ 0 9
def drop_part_part18 (h0: ⟨"%7"⟩ ≠ x) (h1: ⟨"%26"⟩ ≠ x) (h2: ⟨"%27"⟩ ≠ x) (h3: ⟨"%28"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part18⟧) =
  State.buffers (Γ st ⟦part18; dropfelt x⟧) := by
    unfold part18
    rewrite[drop_past_const (by trivial),MLIR.run_seq_def,drop_past_get (by trivial),MLIR.run_seq_def,drop_past_mul (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_get_single (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part19 : MLIRProgram :=   "%29" ←ₐ .Mul ⟨"%28"⟩ ⟨"%13"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 1; "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%15"⟩; "%32" ←ₐ .Add ⟨"%31"⟩ ⟨"%29"⟩
def drop_part_part19 (h0: ⟨"%28"⟩ ≠ x) (h1: ⟨"%13"⟩ ≠ x) (h2: ⟨"%29"⟩ ≠ x) (h3: ⟨"%30"⟩ ≠ x) (h4: ⟨"%15"⟩ ≠ x) (h5: ⟨"%31"⟩ ≠ x) (h6: ⟨"%32"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part19⟧) =
  State.buffers (Γ st ⟦part19; dropfelt x⟧) := by
    unfold part19
    rewrite[drop_past_mul (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_get (by trivial),MLIR.run_seq_def,drop_past_mul (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_add_single (by trivial) (by trivial) (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part20 : MLIRProgram :=   "%33" ←ₐ .Add ⟨"%32"⟩ ⟨"%27"⟩; "%25" ←ₐ .Get ⟨"data"⟩ 0 0; "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%25"⟩; "%35" ←ₐ .Get ⟨"data"⟩ 0 10
def drop_part_part20 (h0: ⟨"%32"⟩ ≠ x) (h1: ⟨"%27"⟩ ≠ x) (h2: ⟨"%33"⟩ ≠ x) (h3: ⟨"%25"⟩ ≠ x) (h4: ⟨"%34"⟩ ≠ x) (h5: ⟨"%35"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part20⟧) =
  State.buffers (Γ st ⟦part20; dropfelt x⟧) := by
    unfold part20
    rewrite[drop_past_add (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_get (by trivial),MLIR.run_seq_def,drop_past_add (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_get_single (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part21 : MLIRProgram :=   "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%3"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%34"⟩; "%11" ←ₐ .Const 2; "%38" ←ₐ .Mul ⟨"%37"⟩ ⟨"%11"⟩
def drop_part_part21 (h0: ⟨"%35"⟩ ≠ x) (h1: ⟨"%3"⟩ ≠ x) (h2: ⟨"%36"⟩ ≠ x) (h3: ⟨"%34"⟩ ≠ x) (h4: ⟨"%37"⟩ ≠ x) (h5: ⟨"%11"⟩ ≠ x) (h6: ⟨"%38"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part21⟧) =
  State.buffers (Γ st ⟦part21; dropfelt x⟧) := by
    unfold part21
    rewrite[drop_past_mul (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_add (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_const (by trivial),MLIR.run_seq_def,drop_past_mul_single (by trivial) (by trivial) (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part22 : MLIRProgram :=   "%24" ←ₐ .Get ⟨"data"⟩ 0 13; "%39" ←ₐ .Add ⟨"%38"⟩ ⟨"%24"⟩; "%40" ←ₐ .Sub ⟨"%23"⟩ ⟨"%39"⟩; ?₀ ⟨"%40"⟩
def drop_part_part22 (h0: ⟨"%24"⟩ ≠ x) (h1: ⟨"%38"⟩ ≠ x) (h2: ⟨"%39"⟩ ≠ x) (h3: ⟨"%23"⟩ ≠ x) (h4: ⟨"%40"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part22⟧) =
  State.buffers (Γ st ⟦part22; dropfelt x⟧) := by
    unfold part22
    rewrite[drop_past_get (by trivial),MLIR.run_seq_def,drop_past_add (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_sub (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_eqz_single (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part23 : MLIRProgram :=   "%42" ←ₐ .Get ⟨"data"⟩ 0 4; "%43" ←ₐ .Mul ⟨"%42"⟩ ⟨"%7"⟩; "%45" ←ₐ .Get ⟨"data"⟩ 0 2; "%46" ←ₐ .Mul ⟨"%45"⟩ ⟨"%11"⟩
def drop_part_part23 (h0: ⟨"%42"⟩ ≠ x) (h1: ⟨"%7"⟩ ≠ x) (h2: ⟨"%43"⟩ ≠ x) (h3: ⟨"%45"⟩ ≠ x) (h4: ⟨"%11"⟩ ≠ x) (h5: ⟨"%46"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part23⟧) =
  State.buffers (Γ st ⟦part23; dropfelt x⟧) := by
    unfold part23
    rewrite[drop_past_get (by trivial),MLIR.run_seq_def,drop_past_mul (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_get (by trivial),MLIR.run_seq_def,drop_past_mul_single (by trivial) (by trivial) (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part24 : MLIRProgram :=   "%47" ←ₐ .Get ⟨"data"⟩ 0 12; "%48" ←ₐ .Mul ⟨"%47"⟩ ⟨"%13"⟩; "%49" ←ₐ .Add ⟨"%48"⟩ ⟨"%46"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 11
def drop_part_part24 (h0: ⟨"%47"⟩ ≠ x) (h1: ⟨"%13"⟩ ≠ x) (h2: ⟨"%48"⟩ ≠ x) (h3: ⟨"%46"⟩ ≠ x) (h4: ⟨"%49"⟩ ≠ x) (h5: ⟨"%44"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part24⟧) =
  State.buffers (Γ st ⟦part24; dropfelt x⟧) := by
    unfold part24
    rewrite[drop_past_get (by trivial),MLIR.run_seq_def,drop_past_mul (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_add (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_get_single (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part25 : MLIRProgram :=   "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%44"⟩; "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%15"⟩; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%43"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 3
def drop_part_part25 (h0: ⟨"%49"⟩ ≠ x) (h1: ⟨"%44"⟩ ≠ x) (h2: ⟨"%50"⟩ ≠ x) (h3: ⟨"%15"⟩ ≠ x) (h4: ⟨"%51"⟩ ≠ x) (h5: ⟨"%43"⟩ ≠ x) (h6: ⟨"%52"⟩ ≠ x) (h7: ⟨"%41"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part25⟧) =
  State.buffers (Γ st ⟦part25; dropfelt x⟧) := by
    unfold part25
    rewrite[drop_past_add (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_mul (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_add (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_get_single (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part26 : MLIRProgram :=   "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%41"⟩; "%54" ←ₐ .Sub ⟨"%22"⟩ ⟨"%53"⟩; ?₀ ⟨"%54"⟩; "%56" ←ₐ .Get ⟨"data"⟩ 0 7
def drop_part_part26 (h0: ⟨"%52"⟩ ≠ x) (h1: ⟨"%41"⟩ ≠ x) (h2: ⟨"%53"⟩ ≠ x) (h3: ⟨"%22"⟩ ≠ x) (h4: ⟨"%54"⟩ ≠ x) (h5: ⟨"%56"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part26⟧) =
  State.buffers (Γ st ⟦part26; dropfelt x⟧) := by
    unfold part26
    rewrite[drop_past_add (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_sub (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_eqz (by trivial),MLIR.run_seq_def,drop_past_get_single (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part27 : MLIRProgram :=   "%57" ←ₐ .Mul ⟨"%56"⟩ ⟨"%7"⟩; "%59" ←ₐ .Get ⟨"data"⟩ 0 15; "%60" ←ₐ .Mul ⟨"%59"⟩ ⟨"%7"⟩; "%58" ←ₐ .Get ⟨"data"⟩ 0 5
def drop_part_part27 (h0: ⟨"%56"⟩ ≠ x) (h1: ⟨"%7"⟩ ≠ x) (h2: ⟨"%57"⟩ ≠ x) (h3: ⟨"%59"⟩ ≠ x) (h4: ⟨"%60"⟩ ≠ x) (h5: ⟨"%58"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part27⟧) =
  State.buffers (Γ st ⟦part27; dropfelt x⟧) := by
    unfold part27
    rewrite[drop_past_mul (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_get (by trivial),MLIR.run_seq_def,drop_past_mul (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_get_single (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part28 : MLIRProgram :=   "%61" ←ₐ .Add ⟨"%60"⟩ ⟨"%58"⟩; "%62" ←ₐ .Mul ⟨"%61"⟩ ⟨"%15"⟩; "%63" ←ₐ .Get ⟨"data"⟩ 0 14; "%64" ←ₐ .Mul ⟨"%63"⟩ ⟨"%19"⟩
def drop_part_part28 (h0: ⟨"%60"⟩ ≠ x) (h1: ⟨"%58"⟩ ≠ x) (h2: ⟨"%61"⟩ ≠ x) (h3: ⟨"%15"⟩ ≠ x) (h4: ⟨"%62"⟩ ≠ x) (h5: ⟨"%63"⟩ ≠ x) (h6: ⟨"%19"⟩ ≠ x) (h7: ⟨"%64"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part28⟧) =
  State.buffers (Γ st ⟦part28; dropfelt x⟧) := by
    unfold part28
    rewrite[drop_past_add (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_mul (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_get (by trivial),MLIR.run_seq_def,drop_past_mul_single (by trivial) (by trivial) (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part29 : MLIRProgram :=   "%65" ←ₐ .Add ⟨"%64"⟩ ⟨"%62"⟩; "%66" ←ₐ .Add ⟨"%65"⟩ ⟨"%57"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 6; "%67" ←ₐ .Add ⟨"%66"⟩ ⟨"%55"⟩
def drop_part_part29 (h0: ⟨"%64"⟩ ≠ x) (h1: ⟨"%62"⟩ ≠ x) (h2: ⟨"%65"⟩ ≠ x) (h3: ⟨"%57"⟩ ≠ x) (h4: ⟨"%66"⟩ ≠ x) (h5: ⟨"%55"⟩ ≠ x) (h6: ⟨"%67"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part29⟧) =
  State.buffers (Γ st ⟦part29; dropfelt x⟧) := by
    unfold part29
    rewrite[drop_past_add (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_add (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_get (by trivial),MLIR.run_seq_def,drop_past_add_single (by trivial) (by trivial) (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part30 : MLIRProgram :=   "%68" ←ₐ .Sub ⟨"%21"⟩ ⟨"%67"⟩; ?₀ ⟨"%68"⟩; "%70" ←ₐ .Get ⟨"data"⟩ 0 16; "%71" ←ₐ .Mul ⟨"%70"⟩ ⟨"%19"⟩
def drop_part_part30 (h0: ⟨"%21"⟩ ≠ x) (h1: ⟨"%67"⟩ ≠ x) (h2: ⟨"%68"⟩ ≠ x) (h3: ⟨"%70"⟩ ≠ x) (h4: ⟨"%19"⟩ ≠ x) (h5: ⟨"%71"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part30; rest⟧) =
  State.buffers (Γ st ⟦part30; dropfelt x; rest⟧) := by
    unfold part30
    rewrite [MLIR.run_seq_def,←MLIR.seq_assoc,MLIR.run_seq_def,←MLIR.seq_assoc,MLIR.run_seq_def,←MLIR.seq_assoc,MLIR.run_seq_def,←MLIR.seq_assoc, MLIR.run_seq_def]
    rewrite [MLIR.run_seq_def,←MLIR.seq_assoc,MLIR.run_seq_def,←MLIR.seq_assoc,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rewrite [←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def,←MLIR.run_seq_def]
    rewrite[drop_past_sub (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_eqz (by trivial),MLIR.run_seq_def,drop_past_get (by trivial),MLIR.run_seq_def,drop_past_mul (by trivial) (by trivial) (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl
def part31 : MLIRProgram :=   "%69" ←ₐ .Get ⟨"data"⟩ 0 17; "%72" ←ₐ .Add ⟨"%71"⟩ ⟨"%69"⟩; "%73" ←ₐ .Sub ⟨"%20"⟩ ⟨"%72"⟩; ?₀ ⟨"%73"⟩
def drop_part_part31 (h0: ⟨"%69"⟩ ≠ x) (h1: ⟨"%71"⟩ ≠ x) (h2: ⟨"%72"⟩ ≠ x) (h3: ⟨"%20"⟩ ≠ x) (h4: ⟨"%73"⟩ ≠ x):
  State.buffers (Γ st ⟦dropfelt x; part31⟧) =
  State.buffers (Γ st ⟦part31; dropfelt x⟧) := by
    unfold part31
    rewrite[drop_past_get (by trivial),MLIR.run_seq_def,drop_past_add (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_sub (by trivial) (by trivial) (by trivial),MLIR.run_seq_def,drop_past_eqz_single (by trivial)]
    rewrite[MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def,MLIR.run_seq_def]
    rfl

end Risc0.ComputeDecode.Witness.Code