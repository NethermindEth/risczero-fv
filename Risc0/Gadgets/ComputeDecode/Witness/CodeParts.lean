import Risc0.Gadgets.ComputeDecode.Witness.CodeReordered

namespace Risc0.ComputeDecode.Witness.Code

open MLIRNotation

def part0 : MLIRProgram :=   "%19" ←ₐ .Const 128; "%23" ←ₐ .Get ⟨"in"⟩ 0 3; nondet ( "%74" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%19"⟩ ); "%18" ←ₐ .Const 1997537281
def part1 : MLIRProgram :=   nondet ( "%75" ←ₐ .Mul ⟨"%74"⟩ ⟨"%18"⟩; ⟨"data"⟩[10] ←ᵢ ⟨"%75"⟩ ); "%17" ←ₐ .Const 96; nondet ( "%76" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%17"⟩ )
def part2 : MLIRProgram :=   "%16" ←ₐ .Const 1950351361; nondet ( "%77" ←ₐ .Mul ⟨"%76"⟩ ⟨"%16"⟩; ⟨"data"⟩[1] ←ᵢ ⟨"%77"⟩ ); "%15" ←ₐ .Const 16
def part3 : MLIRProgram :=   nondet ( "%78" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%15"⟩ ); "%14" ←ₐ .Const 1887436801; nondet ( "%79" ←ₐ .Mul ⟨"%78"⟩ ⟨"%14"⟩; ⟨"data"⟩[9] ←ᵢ ⟨"%79"⟩ )
def part4 : MLIRProgram :=   "%13" ←ₐ .Const 8; nondet ( "%80" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%13"⟩ ); "%12" ←ₐ .Const 1761607681; nondet ( "%81" ←ₐ .Mul ⟨"%80"⟩ ⟨"%12"⟩ )
def part5 : MLIRProgram :=   nondet ( ⟨"data"⟩[8] ←ᵢ ⟨"%81"⟩ ); "%10" ←ₐ .Const 6; nondet ( "%82" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%10"⟩ ); "%9" ←ₐ .Const 1006632961
def part6 : MLIRProgram :=   nondet ( "%83" ←ₐ .Mul ⟨"%82"⟩ ⟨"%9"⟩; ⟨"data"⟩[0] ←ᵢ ⟨"%83"⟩ ); "%8" ←ₐ .Const 1; nondet ( "%84" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%8"⟩ )
def part7 : MLIRProgram :=   nondet ( ⟨"data"⟩[13] ←ᵢ ⟨"%84"⟩ ); "%22" ←ₐ .Get ⟨"in"⟩ 0 2; nondet ( "%85" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%19"⟩; "%86" ←ₐ .Mul ⟨"%85"⟩ ⟨"%18"⟩ )
def part8 : MLIRProgram :=   nondet ( ⟨"data"⟩[12] ←ᵢ ⟨"%86"⟩; "%87" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%17"⟩; "%88" ←ₐ .Mul ⟨"%87"⟩ ⟨"%16"⟩; ⟨"data"⟩[2] ←ᵢ ⟨"%88"⟩ )
def part9 : MLIRProgram :=   nondet ( "%89" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%15"⟩; "%90" ←ₐ .Mul ⟨"%89"⟩ ⟨"%14"⟩; ⟨"data"⟩[11] ←ᵢ ⟨"%90"⟩ ); "%6" ←ₐ .Const 12
def part10 : MLIRProgram :=   nondet ( "%91" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%6"⟩ ); "%5" ←ₐ .Const 1509949441; nondet ( "%92" ←ₐ .Mul ⟨"%91"⟩ ⟨"%5"⟩; ⟨"data"⟩[4] ←ᵢ ⟨"%92"⟩ )
def part11 : MLIRProgram :=   "%4" ←ₐ .Const 3; nondet ( "%93" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%4"⟩; ⟨"data"⟩[3] ←ᵢ ⟨"%93"⟩ ); "%21" ←ₐ .Get ⟨"in"⟩ 0 1
def part12 : MLIRProgram :=   nondet ( "%94" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%19"⟩; "%95" ←ₐ .Mul ⟨"%94"⟩ ⟨"%18"⟩; ⟨"data"⟩[14] ←ᵢ ⟨"%95"⟩ ); "%3" ←ₐ .Const 64
def part13 : MLIRProgram :=   nondet ( "%96" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%3"⟩ ); "%2" ←ₐ .Const 1981808641; nondet ( "%97" ←ₐ .Mul ⟨"%96"⟩ ⟨"%2"⟩; ⟨"data"⟩[15] ←ᵢ ⟨"%97"⟩ )
def part14 : MLIRProgram :=   "%1" ←ₐ .Const 48; nondet ( "%98" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%1"⟩; "%99" ←ₐ .Mul ⟨"%98"⟩ ⟨"%14"⟩; ⟨"data"⟩[5] ←ᵢ ⟨"%99"⟩ )
def part15 : MLIRProgram :=   nondet ( "%100" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%6"⟩; "%101" ←ₐ .Mul ⟨"%100"⟩ ⟨"%5"⟩; ⟨"data"⟩[7] ←ᵢ ⟨"%101"⟩; "%102" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%4"⟩ )
def part16 : MLIRProgram :=   nondet ( ⟨"data"⟩[6] ←ᵢ ⟨"%102"⟩ ); "%20" ←ₐ .Get ⟨"in"⟩ 0 0; nondet ( "%103" ←ₐ .BitAnd ⟨"%20"⟩ ⟨"%19"⟩; "%104" ←ₐ .Mul ⟨"%103"⟩ ⟨"%18"⟩ )
def part17 : MLIRProgram :=   nondet ( ⟨"data"⟩[16] ←ᵢ ⟨"%104"⟩ ); "%0" ←ₐ .Const 127; nondet ( "%105" ←ₐ .BitAnd ⟨"%20"⟩ ⟨"%0"⟩; ⟨"data"⟩[17] ←ᵢ ⟨"%105"⟩ )
def part18 : MLIRProgram :=   "%7" ←ₐ .Const 4; "%26" ←ₐ .Get ⟨"data"⟩ 0 8; "%27" ←ₐ .Mul ⟨"%26"⟩ ⟨"%7"⟩; "%28" ←ₐ .Get ⟨"data"⟩ 0 9
def part19 : MLIRProgram :=   "%29" ←ₐ .Mul ⟨"%28"⟩ ⟨"%13"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 1; "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%15"⟩; "%32" ←ₐ .Add ⟨"%31"⟩ ⟨"%29"⟩
def part20 : MLIRProgram :=   "%33" ←ₐ .Add ⟨"%32"⟩ ⟨"%27"⟩; "%25" ←ₐ .Get ⟨"data"⟩ 0 0; "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%25"⟩; "%35" ←ₐ .Get ⟨"data"⟩ 0 10
def part21 : MLIRProgram :=   "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%3"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%34"⟩; "%11" ←ₐ .Const 2; "%38" ←ₐ .Mul ⟨"%37"⟩ ⟨"%11"⟩
def part22 : MLIRProgram :=   "%24" ←ₐ .Get ⟨"data"⟩ 0 13; "%39" ←ₐ .Add ⟨"%38"⟩ ⟨"%24"⟩; "%40" ←ₐ .Sub ⟨"%23"⟩ ⟨"%39"⟩; ?₀ ⟨"%40"⟩
def part23 : MLIRProgram :=   "%42" ←ₐ .Get ⟨"data"⟩ 0 4; "%43" ←ₐ .Mul ⟨"%42"⟩ ⟨"%7"⟩; "%45" ←ₐ .Get ⟨"data"⟩ 0 2; "%46" ←ₐ .Mul ⟨"%45"⟩ ⟨"%11"⟩
def part24 : MLIRProgram :=   "%47" ←ₐ .Get ⟨"data"⟩ 0 12; "%48" ←ₐ .Mul ⟨"%47"⟩ ⟨"%13"⟩; "%49" ←ₐ .Add ⟨"%48"⟩ ⟨"%46"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 11
def part25 : MLIRProgram :=   "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%44"⟩; "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%15"⟩; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%43"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 3
def part26 : MLIRProgram :=   "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%41"⟩; "%54" ←ₐ .Sub ⟨"%22"⟩ ⟨"%53"⟩; ?₀ ⟨"%54"⟩; "%56" ←ₐ .Get ⟨"data"⟩ 0 7
def part27 : MLIRProgram :=   "%57" ←ₐ .Mul ⟨"%56"⟩ ⟨"%7"⟩; "%59" ←ₐ .Get ⟨"data"⟩ 0 15; "%60" ←ₐ .Mul ⟨"%59"⟩ ⟨"%7"⟩; "%58" ←ₐ .Get ⟨"data"⟩ 0 5
def part28 : MLIRProgram :=   "%61" ←ₐ .Add ⟨"%60"⟩ ⟨"%58"⟩; "%62" ←ₐ .Mul ⟨"%61"⟩ ⟨"%15"⟩; "%63" ←ₐ .Get ⟨"data"⟩ 0 14; "%64" ←ₐ .Mul ⟨"%63"⟩ ⟨"%19"⟩
def part29 : MLIRProgram :=   "%65" ←ₐ .Add ⟨"%64"⟩ ⟨"%62"⟩; "%66" ←ₐ .Add ⟨"%65"⟩ ⟨"%57"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 6; "%67" ←ₐ .Add ⟨"%66"⟩ ⟨"%55"⟩
def part30 : MLIRProgram :=   "%68" ←ₐ .Sub ⟨"%21"⟩ ⟨"%67"⟩; ?₀ ⟨"%68"⟩; "%70" ←ₐ .Get ⟨"data"⟩ 0 16; "%71" ←ₐ .Mul ⟨"%70"⟩ ⟨"%19"⟩
def part31 : MLIRProgram :=   "%69" ←ₐ .Get ⟨"data"⟩ 0 17; "%72" ←ₐ .Add ⟨"%71"⟩ ⟨"%69"⟩; "%73" ←ₐ .Sub ⟨"%20"⟩ ⟨"%72"⟩; ?₀ ⟨"%73"⟩

abbrev parts_combined : MLIRProgram :=
  part0; part1; part2; part3; part4; part5; part6; part7; part8; part9; part10; part11; part12; part13; part14; part15; part16; part17; part18; part19; part20; part21; part22; part23; part24; part25; part26; part27; part28; part29; part30; part31
lemma parts_combine {st: State} :
  Γ st ⟦parts_combined⟧ =
  Γ st ⟦opt_full⟧ := by
  unfold opt_full parts_combined
  unfold part0
  rewrite [MLIR.part_assoc_ddnd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part1
  rewrite [MLIR.part_assoc_nndn]
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part2
  rewrite [MLIR.part_assoc_dnnd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part3
  rewrite [MLIR.part_assoc_ndnn]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part4
  rewrite [MLIR.part_assoc_dndn]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part5
  rewrite [MLIR.part_assoc_ndnd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part6
  rewrite [MLIR.part_assoc_nndn]
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part7
  rewrite [MLIR.part_assoc_ndnn]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part8
  rewrite [MLIR.part_assoc_nnnn]
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part9
  rewrite [MLIR.part_assoc_nnnd]
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part10
  rewrite [MLIR.part_assoc_ndnn]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part11
  rewrite [MLIR.part_assoc_dnnd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part12
  rewrite [MLIR.part_assoc_nnnd]
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part13
  rewrite [MLIR.part_assoc_ndnn]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part14
  rewrite [MLIR.part_assoc_dnnn]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part15
  rewrite [MLIR.part_assoc_nnnn]
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part16
  rewrite [MLIR.part_assoc_ndnn]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part17
  rewrite [MLIR.part_assoc_ndnn]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part18
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part19
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part20
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part21
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part22
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part23
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part24
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part25
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part26
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part27
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part28
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part29
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part30
  rewrite [MLIR.part_assoc_dddd]
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part31
  rfl
end Risc0.ComputeDecode.Witness.Code