import Risc0.Gadgets.computeDecode.Witness.CodeReordered

namespace Risc0.computeDecode.Witness.Code

open MLIRNotation

def part0 : MLIRProgram :=   "%3" ←ₐ .Const 0; nondet ( ⟨"data"⟩[10] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[1] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[9] ←ᵢ ⟨"%3"⟩ )
def part1 : MLIRProgram :=   nondet ( ⟨"data"⟩[8] ←ᵢ ⟨"%3"⟩ ); "%7" ←ₐ .Const 2; nondet ( ⟨"data"⟩[0] ←ᵢ ⟨"%7"⟩; ⟨"data"⟩[13] ←ᵢ ⟨"%3"⟩ )
def part2 : MLIRProgram :=   nondet ( ⟨"data"⟩[12] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[2] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[11] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[4] ←ᵢ ⟨"%3"⟩ )
def part3 : MLIRProgram :=   "%6" ←ₐ .Const 3; nondet ( ⟨"data"⟩[3] ←ᵢ ⟨"%6"⟩; ⟨"data"⟩[14] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[15] ←ᵢ ⟨"%3"⟩ )
def part4 : MLIRProgram :=   nondet ( ⟨"data"⟩[5] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[7] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[6] ←ᵢ ⟨"%7"⟩; ⟨"data"⟩[16] ←ᵢ ⟨"%3"⟩ )
def part5 : MLIRProgram :=   "%8" ←ₐ .Const 1; nondet ( ⟨"data"⟩[17] ←ᵢ ⟨"%8"⟩ ); "%5" ←ₐ .Const 4; "%11" ←ₐ .Get ⟨"data"⟩ 0 8
def part6 : MLIRProgram :=   "%12" ←ₐ .Mul ⟨"%11"⟩ ⟨"%5"⟩; "%1" ←ₐ .Const 8; "%13" ←ₐ .Get ⟨"data"⟩ 0 9; "%14" ←ₐ .Mul ⟨"%13"⟩ ⟨"%1"⟩
def part7 : MLIRProgram :=   "%2" ←ₐ .Const 16; "%15" ←ₐ .Get ⟨"data"⟩ 0 1; "%16" ←ₐ .Mul ⟨"%15"⟩ ⟨"%2"⟩; "%17" ←ₐ .Add ⟨"%16"⟩ ⟨"%14"⟩
def part8 : MLIRProgram :=   "%18" ←ₐ .Add ⟨"%17"⟩ ⟨"%12"⟩; "%10" ←ₐ .Get ⟨"data"⟩ 0 0; "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%10"⟩; "%0" ←ₐ .Const 64
def part9 : MLIRProgram :=   "%20" ←ₐ .Get ⟨"data"⟩ 0 10; "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%0"⟩; "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩; "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%7"⟩
def part10 : MLIRProgram :=   "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%5"⟩ ⟨"%24"⟩; ?₀ ⟨"%25"⟩
def part11 : MLIRProgram :=   "%27" ←ₐ .Get ⟨"data"⟩ 0 4; "%28" ←ₐ .Mul ⟨"%27"⟩ ⟨"%5"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 2; "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%7"⟩
def part12 : MLIRProgram :=   "%32" ←ₐ .Get ⟨"data"⟩ 0 12; "%33" ←ₐ .Mul ⟨"%32"⟩ ⟨"%1"⟩; "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%31"⟩; "%29" ←ₐ .Get ⟨"data"⟩ 0 11
def part13 : MLIRProgram :=   "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%29"⟩; "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%28"⟩; "%26" ←ₐ .Get ⟨"data"⟩ 0 3
def part14 : MLIRProgram :=   "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%26"⟩; "%39" ←ₐ .Sub ⟨"%6"⟩ ⟨"%38"⟩; ?₀ ⟨"%39"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 7
def part15 : MLIRProgram :=   "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 15; "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 5
def part16 : MLIRProgram :=   "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14
def part17 : MLIRProgram :=   "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6
def part18 : MLIRProgram :=   "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16
def part19 : MLIRProgram :=   "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩
def part20 : MLIRProgram :=   ?₀ ⟨"%58"⟩

def part0_to_end : MLIRProgram :=   "%3" ←ₐ .Const 0; nondet ( ⟨"data"⟩[10] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[1] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[9] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[8] ←ᵢ ⟨"%3"⟩ ); "%7" ←ₐ .Const 2; nondet ( ⟨"data"⟩[0] ←ᵢ ⟨"%7"⟩; ⟨"data"⟩[13] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[12] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[2] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[11] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[4] ←ᵢ ⟨"%3"⟩ ); "%6" ←ₐ .Const 3; nondet ( ⟨"data"⟩[3] ←ᵢ ⟨"%6"⟩; ⟨"data"⟩[14] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[15] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[5] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[7] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[6] ←ᵢ ⟨"%7"⟩; ⟨"data"⟩[16] ←ᵢ ⟨"%3"⟩ ); "%8" ←ₐ .Const 1; nondet ( ⟨"data"⟩[17] ←ᵢ ⟨"%8"⟩ ); "%5" ←ₐ .Const 4; "%11" ←ₐ .Get ⟨"data"⟩ 0 8; "%12" ←ₐ .Mul ⟨"%11"⟩ ⟨"%5"⟩; "%1" ←ₐ .Const 8; "%13" ←ₐ .Get ⟨"data"⟩ 0 9; "%14" ←ₐ .Mul ⟨"%13"⟩ ⟨"%1"⟩; "%2" ←ₐ .Const 16; "%15" ←ₐ .Get ⟨"data"⟩ 0 1; "%16" ←ₐ .Mul ⟨"%15"⟩ ⟨"%2"⟩; "%17" ←ₐ .Add ⟨"%16"⟩ ⟨"%14"⟩; "%18" ←ₐ .Add ⟨"%17"⟩ ⟨"%12"⟩; "%10" ←ₐ .Get ⟨"data"⟩ 0 0; "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%10"⟩; "%0" ←ₐ .Const 64; "%20" ←ₐ .Get ⟨"data"⟩ 0 10; "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%0"⟩; "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩; "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%7"⟩; "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%5"⟩ ⟨"%24"⟩; ?₀ ⟨"%25"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 4; "%28" ←ₐ .Mul ⟨"%27"⟩ ⟨"%5"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 2; "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%7"⟩; "%32" ←ₐ .Get ⟨"data"⟩ 0 12; "%33" ←ₐ .Mul ⟨"%32"⟩ ⟨"%1"⟩; "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%31"⟩; "%29" ←ₐ .Get ⟨"data"⟩ 0 11; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%29"⟩; "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%28"⟩; "%26" ←ₐ .Get ⟨"data"⟩ 0 3; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%26"⟩; "%39" ←ₐ .Sub ⟨"%6"⟩ ⟨"%38"⟩; ?₀ ⟨"%39"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 7; "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 15; "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 5; "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part1_to_end : MLIRProgram :=   nondet ( ⟨"data"⟩[8] ←ᵢ ⟨"%3"⟩ ); "%7" ←ₐ .Const 2; nondet ( ⟨"data"⟩[0] ←ᵢ ⟨"%7"⟩; ⟨"data"⟩[13] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[12] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[2] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[11] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[4] ←ᵢ ⟨"%3"⟩ ); "%6" ←ₐ .Const 3; nondet ( ⟨"data"⟩[3] ←ᵢ ⟨"%6"⟩; ⟨"data"⟩[14] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[15] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[5] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[7] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[6] ←ᵢ ⟨"%7"⟩; ⟨"data"⟩[16] ←ᵢ ⟨"%3"⟩ ); "%8" ←ₐ .Const 1; nondet ( ⟨"data"⟩[17] ←ᵢ ⟨"%8"⟩ ); "%5" ←ₐ .Const 4; "%11" ←ₐ .Get ⟨"data"⟩ 0 8; "%12" ←ₐ .Mul ⟨"%11"⟩ ⟨"%5"⟩; "%1" ←ₐ .Const 8; "%13" ←ₐ .Get ⟨"data"⟩ 0 9; "%14" ←ₐ .Mul ⟨"%13"⟩ ⟨"%1"⟩; "%2" ←ₐ .Const 16; "%15" ←ₐ .Get ⟨"data"⟩ 0 1; "%16" ←ₐ .Mul ⟨"%15"⟩ ⟨"%2"⟩; "%17" ←ₐ .Add ⟨"%16"⟩ ⟨"%14"⟩; "%18" ←ₐ .Add ⟨"%17"⟩ ⟨"%12"⟩; "%10" ←ₐ .Get ⟨"data"⟩ 0 0; "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%10"⟩; "%0" ←ₐ .Const 64; "%20" ←ₐ .Get ⟨"data"⟩ 0 10; "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%0"⟩; "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩; "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%7"⟩; "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%5"⟩ ⟨"%24"⟩; ?₀ ⟨"%25"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 4; "%28" ←ₐ .Mul ⟨"%27"⟩ ⟨"%5"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 2; "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%7"⟩; "%32" ←ₐ .Get ⟨"data"⟩ 0 12; "%33" ←ₐ .Mul ⟨"%32"⟩ ⟨"%1"⟩; "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%31"⟩; "%29" ←ₐ .Get ⟨"data"⟩ 0 11; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%29"⟩; "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%28"⟩; "%26" ←ₐ .Get ⟨"data"⟩ 0 3; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%26"⟩; "%39" ←ₐ .Sub ⟨"%6"⟩ ⟨"%38"⟩; ?₀ ⟨"%39"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 7; "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 15; "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 5; "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part2_to_end : MLIRProgram :=   nondet ( ⟨"data"⟩[12] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[2] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[11] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[4] ←ᵢ ⟨"%3"⟩ ); "%6" ←ₐ .Const 3; nondet ( ⟨"data"⟩[3] ←ᵢ ⟨"%6"⟩; ⟨"data"⟩[14] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[15] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[5] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[7] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[6] ←ᵢ ⟨"%7"⟩; ⟨"data"⟩[16] ←ᵢ ⟨"%3"⟩ ); "%8" ←ₐ .Const 1; nondet ( ⟨"data"⟩[17] ←ᵢ ⟨"%8"⟩ ); "%5" ←ₐ .Const 4; "%11" ←ₐ .Get ⟨"data"⟩ 0 8; "%12" ←ₐ .Mul ⟨"%11"⟩ ⟨"%5"⟩; "%1" ←ₐ .Const 8; "%13" ←ₐ .Get ⟨"data"⟩ 0 9; "%14" ←ₐ .Mul ⟨"%13"⟩ ⟨"%1"⟩; "%2" ←ₐ .Const 16; "%15" ←ₐ .Get ⟨"data"⟩ 0 1; "%16" ←ₐ .Mul ⟨"%15"⟩ ⟨"%2"⟩; "%17" ←ₐ .Add ⟨"%16"⟩ ⟨"%14"⟩; "%18" ←ₐ .Add ⟨"%17"⟩ ⟨"%12"⟩; "%10" ←ₐ .Get ⟨"data"⟩ 0 0; "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%10"⟩; "%0" ←ₐ .Const 64; "%20" ←ₐ .Get ⟨"data"⟩ 0 10; "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%0"⟩; "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩; "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%7"⟩; "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%5"⟩ ⟨"%24"⟩; ?₀ ⟨"%25"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 4; "%28" ←ₐ .Mul ⟨"%27"⟩ ⟨"%5"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 2; "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%7"⟩; "%32" ←ₐ .Get ⟨"data"⟩ 0 12; "%33" ←ₐ .Mul ⟨"%32"⟩ ⟨"%1"⟩; "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%31"⟩; "%29" ←ₐ .Get ⟨"data"⟩ 0 11; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%29"⟩; "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%28"⟩; "%26" ←ₐ .Get ⟨"data"⟩ 0 3; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%26"⟩; "%39" ←ₐ .Sub ⟨"%6"⟩ ⟨"%38"⟩; ?₀ ⟨"%39"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 7; "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 15; "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 5; "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part3_to_end : MLIRProgram :=   "%6" ←ₐ .Const 3; nondet ( ⟨"data"⟩[3] ←ᵢ ⟨"%6"⟩; ⟨"data"⟩[14] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[15] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[5] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[7] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[6] ←ᵢ ⟨"%7"⟩; ⟨"data"⟩[16] ←ᵢ ⟨"%3"⟩ ); "%8" ←ₐ .Const 1; nondet ( ⟨"data"⟩[17] ←ᵢ ⟨"%8"⟩ ); "%5" ←ₐ .Const 4; "%11" ←ₐ .Get ⟨"data"⟩ 0 8; "%12" ←ₐ .Mul ⟨"%11"⟩ ⟨"%5"⟩; "%1" ←ₐ .Const 8; "%13" ←ₐ .Get ⟨"data"⟩ 0 9; "%14" ←ₐ .Mul ⟨"%13"⟩ ⟨"%1"⟩; "%2" ←ₐ .Const 16; "%15" ←ₐ .Get ⟨"data"⟩ 0 1; "%16" ←ₐ .Mul ⟨"%15"⟩ ⟨"%2"⟩; "%17" ←ₐ .Add ⟨"%16"⟩ ⟨"%14"⟩; "%18" ←ₐ .Add ⟨"%17"⟩ ⟨"%12"⟩; "%10" ←ₐ .Get ⟨"data"⟩ 0 0; "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%10"⟩; "%0" ←ₐ .Const 64; "%20" ←ₐ .Get ⟨"data"⟩ 0 10; "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%0"⟩; "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩; "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%7"⟩; "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%5"⟩ ⟨"%24"⟩; ?₀ ⟨"%25"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 4; "%28" ←ₐ .Mul ⟨"%27"⟩ ⟨"%5"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 2; "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%7"⟩; "%32" ←ₐ .Get ⟨"data"⟩ 0 12; "%33" ←ₐ .Mul ⟨"%32"⟩ ⟨"%1"⟩; "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%31"⟩; "%29" ←ₐ .Get ⟨"data"⟩ 0 11; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%29"⟩; "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%28"⟩; "%26" ←ₐ .Get ⟨"data"⟩ 0 3; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%26"⟩; "%39" ←ₐ .Sub ⟨"%6"⟩ ⟨"%38"⟩; ?₀ ⟨"%39"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 7; "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 15; "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 5; "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part4_to_end : MLIRProgram :=   nondet ( ⟨"data"⟩[5] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[7] ←ᵢ ⟨"%3"⟩; ⟨"data"⟩[6] ←ᵢ ⟨"%7"⟩; ⟨"data"⟩[16] ←ᵢ ⟨"%3"⟩ ); "%8" ←ₐ .Const 1; nondet ( ⟨"data"⟩[17] ←ᵢ ⟨"%8"⟩ ); "%5" ←ₐ .Const 4; "%11" ←ₐ .Get ⟨"data"⟩ 0 8; "%12" ←ₐ .Mul ⟨"%11"⟩ ⟨"%5"⟩; "%1" ←ₐ .Const 8; "%13" ←ₐ .Get ⟨"data"⟩ 0 9; "%14" ←ₐ .Mul ⟨"%13"⟩ ⟨"%1"⟩; "%2" ←ₐ .Const 16; "%15" ←ₐ .Get ⟨"data"⟩ 0 1; "%16" ←ₐ .Mul ⟨"%15"⟩ ⟨"%2"⟩; "%17" ←ₐ .Add ⟨"%16"⟩ ⟨"%14"⟩; "%18" ←ₐ .Add ⟨"%17"⟩ ⟨"%12"⟩; "%10" ←ₐ .Get ⟨"data"⟩ 0 0; "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%10"⟩; "%0" ←ₐ .Const 64; "%20" ←ₐ .Get ⟨"data"⟩ 0 10; "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%0"⟩; "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩; "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%7"⟩; "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%5"⟩ ⟨"%24"⟩; ?₀ ⟨"%25"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 4; "%28" ←ₐ .Mul ⟨"%27"⟩ ⟨"%5"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 2; "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%7"⟩; "%32" ←ₐ .Get ⟨"data"⟩ 0 12; "%33" ←ₐ .Mul ⟨"%32"⟩ ⟨"%1"⟩; "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%31"⟩; "%29" ←ₐ .Get ⟨"data"⟩ 0 11; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%29"⟩; "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%28"⟩; "%26" ←ₐ .Get ⟨"data"⟩ 0 3; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%26"⟩; "%39" ←ₐ .Sub ⟨"%6"⟩ ⟨"%38"⟩; ?₀ ⟨"%39"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 7; "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 15; "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 5; "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part5_to_end : MLIRProgram :=   "%8" ←ₐ .Const 1; nondet ( ⟨"data"⟩[17] ←ᵢ ⟨"%8"⟩ ); "%5" ←ₐ .Const 4; "%11" ←ₐ .Get ⟨"data"⟩ 0 8; "%12" ←ₐ .Mul ⟨"%11"⟩ ⟨"%5"⟩; "%1" ←ₐ .Const 8; "%13" ←ₐ .Get ⟨"data"⟩ 0 9; "%14" ←ₐ .Mul ⟨"%13"⟩ ⟨"%1"⟩; "%2" ←ₐ .Const 16; "%15" ←ₐ .Get ⟨"data"⟩ 0 1; "%16" ←ₐ .Mul ⟨"%15"⟩ ⟨"%2"⟩; "%17" ←ₐ .Add ⟨"%16"⟩ ⟨"%14"⟩; "%18" ←ₐ .Add ⟨"%17"⟩ ⟨"%12"⟩; "%10" ←ₐ .Get ⟨"data"⟩ 0 0; "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%10"⟩; "%0" ←ₐ .Const 64; "%20" ←ₐ .Get ⟨"data"⟩ 0 10; "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%0"⟩; "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩; "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%7"⟩; "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%5"⟩ ⟨"%24"⟩; ?₀ ⟨"%25"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 4; "%28" ←ₐ .Mul ⟨"%27"⟩ ⟨"%5"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 2; "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%7"⟩; "%32" ←ₐ .Get ⟨"data"⟩ 0 12; "%33" ←ₐ .Mul ⟨"%32"⟩ ⟨"%1"⟩; "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%31"⟩; "%29" ←ₐ .Get ⟨"data"⟩ 0 11; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%29"⟩; "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%28"⟩; "%26" ←ₐ .Get ⟨"data"⟩ 0 3; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%26"⟩; "%39" ←ₐ .Sub ⟨"%6"⟩ ⟨"%38"⟩; ?₀ ⟨"%39"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 7; "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 15; "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 5; "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part6_to_end : MLIRProgram :=   "%12" ←ₐ .Mul ⟨"%11"⟩ ⟨"%5"⟩; "%1" ←ₐ .Const 8; "%13" ←ₐ .Get ⟨"data"⟩ 0 9; "%14" ←ₐ .Mul ⟨"%13"⟩ ⟨"%1"⟩; "%2" ←ₐ .Const 16; "%15" ←ₐ .Get ⟨"data"⟩ 0 1; "%16" ←ₐ .Mul ⟨"%15"⟩ ⟨"%2"⟩; "%17" ←ₐ .Add ⟨"%16"⟩ ⟨"%14"⟩; "%18" ←ₐ .Add ⟨"%17"⟩ ⟨"%12"⟩; "%10" ←ₐ .Get ⟨"data"⟩ 0 0; "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%10"⟩; "%0" ←ₐ .Const 64; "%20" ←ₐ .Get ⟨"data"⟩ 0 10; "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%0"⟩; "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩; "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%7"⟩; "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%5"⟩ ⟨"%24"⟩; ?₀ ⟨"%25"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 4; "%28" ←ₐ .Mul ⟨"%27"⟩ ⟨"%5"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 2; "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%7"⟩; "%32" ←ₐ .Get ⟨"data"⟩ 0 12; "%33" ←ₐ .Mul ⟨"%32"⟩ ⟨"%1"⟩; "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%31"⟩; "%29" ←ₐ .Get ⟨"data"⟩ 0 11; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%29"⟩; "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%28"⟩; "%26" ←ₐ .Get ⟨"data"⟩ 0 3; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%26"⟩; "%39" ←ₐ .Sub ⟨"%6"⟩ ⟨"%38"⟩; ?₀ ⟨"%39"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 7; "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 15; "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 5; "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part7_to_end : MLIRProgram :=   "%2" ←ₐ .Const 16; "%15" ←ₐ .Get ⟨"data"⟩ 0 1; "%16" ←ₐ .Mul ⟨"%15"⟩ ⟨"%2"⟩; "%17" ←ₐ .Add ⟨"%16"⟩ ⟨"%14"⟩; "%18" ←ₐ .Add ⟨"%17"⟩ ⟨"%12"⟩; "%10" ←ₐ .Get ⟨"data"⟩ 0 0; "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%10"⟩; "%0" ←ₐ .Const 64; "%20" ←ₐ .Get ⟨"data"⟩ 0 10; "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%0"⟩; "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩; "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%7"⟩; "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%5"⟩ ⟨"%24"⟩; ?₀ ⟨"%25"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 4; "%28" ←ₐ .Mul ⟨"%27"⟩ ⟨"%5"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 2; "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%7"⟩; "%32" ←ₐ .Get ⟨"data"⟩ 0 12; "%33" ←ₐ .Mul ⟨"%32"⟩ ⟨"%1"⟩; "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%31"⟩; "%29" ←ₐ .Get ⟨"data"⟩ 0 11; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%29"⟩; "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%28"⟩; "%26" ←ₐ .Get ⟨"data"⟩ 0 3; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%26"⟩; "%39" ←ₐ .Sub ⟨"%6"⟩ ⟨"%38"⟩; ?₀ ⟨"%39"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 7; "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 15; "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 5; "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part8_to_end : MLIRProgram :=   "%18" ←ₐ .Add ⟨"%17"⟩ ⟨"%12"⟩; "%10" ←ₐ .Get ⟨"data"⟩ 0 0; "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%10"⟩; "%0" ←ₐ .Const 64; "%20" ←ₐ .Get ⟨"data"⟩ 0 10; "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%0"⟩; "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩; "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%7"⟩; "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%5"⟩ ⟨"%24"⟩; ?₀ ⟨"%25"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 4; "%28" ←ₐ .Mul ⟨"%27"⟩ ⟨"%5"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 2; "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%7"⟩; "%32" ←ₐ .Get ⟨"data"⟩ 0 12; "%33" ←ₐ .Mul ⟨"%32"⟩ ⟨"%1"⟩; "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%31"⟩; "%29" ←ₐ .Get ⟨"data"⟩ 0 11; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%29"⟩; "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%28"⟩; "%26" ←ₐ .Get ⟨"data"⟩ 0 3; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%26"⟩; "%39" ←ₐ .Sub ⟨"%6"⟩ ⟨"%38"⟩; ?₀ ⟨"%39"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 7; "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 15; "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 5; "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part9_to_end : MLIRProgram :=   "%20" ←ₐ .Get ⟨"data"⟩ 0 10; "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%0"⟩; "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩; "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%7"⟩; "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%5"⟩ ⟨"%24"⟩; ?₀ ⟨"%25"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 4; "%28" ←ₐ .Mul ⟨"%27"⟩ ⟨"%5"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 2; "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%7"⟩; "%32" ←ₐ .Get ⟨"data"⟩ 0 12; "%33" ←ₐ .Mul ⟨"%32"⟩ ⟨"%1"⟩; "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%31"⟩; "%29" ←ₐ .Get ⟨"data"⟩ 0 11; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%29"⟩; "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%28"⟩; "%26" ←ₐ .Get ⟨"data"⟩ 0 3; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%26"⟩; "%39" ←ₐ .Sub ⟨"%6"⟩ ⟨"%38"⟩; ?₀ ⟨"%39"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 7; "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 15; "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 5; "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part10_to_end : MLIRProgram :=   "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%5"⟩ ⟨"%24"⟩; ?₀ ⟨"%25"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 4; "%28" ←ₐ .Mul ⟨"%27"⟩ ⟨"%5"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 2; "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%7"⟩; "%32" ←ₐ .Get ⟨"data"⟩ 0 12; "%33" ←ₐ .Mul ⟨"%32"⟩ ⟨"%1"⟩; "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%31"⟩; "%29" ←ₐ .Get ⟨"data"⟩ 0 11; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%29"⟩; "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%28"⟩; "%26" ←ₐ .Get ⟨"data"⟩ 0 3; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%26"⟩; "%39" ←ₐ .Sub ⟨"%6"⟩ ⟨"%38"⟩; ?₀ ⟨"%39"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 7; "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 15; "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 5; "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part11_to_end : MLIRProgram :=   "%27" ←ₐ .Get ⟨"data"⟩ 0 4; "%28" ←ₐ .Mul ⟨"%27"⟩ ⟨"%5"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 2; "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%7"⟩; "%32" ←ₐ .Get ⟨"data"⟩ 0 12; "%33" ←ₐ .Mul ⟨"%32"⟩ ⟨"%1"⟩; "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%31"⟩; "%29" ←ₐ .Get ⟨"data"⟩ 0 11; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%29"⟩; "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%28"⟩; "%26" ←ₐ .Get ⟨"data"⟩ 0 3; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%26"⟩; "%39" ←ₐ .Sub ⟨"%6"⟩ ⟨"%38"⟩; ?₀ ⟨"%39"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 7; "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 15; "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 5; "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part12_to_end : MLIRProgram :=   "%32" ←ₐ .Get ⟨"data"⟩ 0 12; "%33" ←ₐ .Mul ⟨"%32"⟩ ⟨"%1"⟩; "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%31"⟩; "%29" ←ₐ .Get ⟨"data"⟩ 0 11; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%29"⟩; "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%28"⟩; "%26" ←ₐ .Get ⟨"data"⟩ 0 3; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%26"⟩; "%39" ←ₐ .Sub ⟨"%6"⟩ ⟨"%38"⟩; ?₀ ⟨"%39"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 7; "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 15; "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 5; "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part13_to_end : MLIRProgram :=   "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%29"⟩; "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%2"⟩; "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%28"⟩; "%26" ←ₐ .Get ⟨"data"⟩ 0 3; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%26"⟩; "%39" ←ₐ .Sub ⟨"%6"⟩ ⟨"%38"⟩; ?₀ ⟨"%39"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 7; "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 15; "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 5; "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part14_to_end : MLIRProgram :=   "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%26"⟩; "%39" ←ₐ .Sub ⟨"%6"⟩ ⟨"%38"⟩; ?₀ ⟨"%39"⟩; "%41" ←ₐ .Get ⟨"data"⟩ 0 7; "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 15; "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 5; "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part15_to_end : MLIRProgram :=   "%42" ←ₐ .Mul ⟨"%41"⟩ ⟨"%5"⟩; "%44" ←ₐ .Get ⟨"data"⟩ 0 15; "%45" ←ₐ .Mul ⟨"%44"⟩ ⟨"%5"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 5; "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part16_to_end : MLIRProgram :=   "%46" ←ₐ .Add ⟨"%45"⟩ ⟨"%43"⟩; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%2"⟩; "%4" ←ₐ .Const 128; "%48" ←ₐ .Get ⟨"data"⟩ 0 14; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part17_to_end : MLIRProgram :=   "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%4"⟩; "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%47"⟩; "%51" ←ₐ .Add ⟨"%50"⟩ ⟨"%42"⟩; "%40" ←ₐ .Get ⟨"data"⟩ 0 6; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part18_to_end : MLIRProgram :=   "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%40"⟩; "%53" ←ₐ .Sub ⟨"%7"⟩ ⟨"%52"⟩; ?₀ ⟨"%53"⟩; "%55" ←ₐ .Get ⟨"data"⟩ 0 16; "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part19_to_end : MLIRProgram :=   "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%4"⟩; "%54" ←ₐ .Get ⟨"data"⟩ 0 17; "%57" ←ₐ .Add ⟨"%56"⟩ ⟨"%54"⟩; "%58" ←ₐ .Sub ⟨"%8"⟩ ⟨"%57"⟩; ?₀ ⟨"%58"⟩
def part20_to_end : MLIRProgram :=   ?₀ ⟨"%58"⟩

abbrev parts_combined : MLIRProgram :=
  part0; part1; part2; part3; part4; part5; part6; part7; part8; part9; part10; part11; part12; part13; part14; part15; part16; part17; part18; part19; part20

lemma parts_combine20 :
  Γ st ⟦part20⟧ =
  Γ st ⟦part20_to_end⟧ := by
    rfl
lemma parts_combine19 :
  Γ st ⟦part19; part20⟧ =
  Γ st ⟦part19_to_end⟧ := by
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
    rewrite [parts_combine20]
    rfl
lemma parts_combine18 :
  Γ st ⟦part18; part19; part20⟧ =
  Γ st ⟦part18_to_end⟧ := by
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
    rewrite [parts_combine19]
    rfl
lemma parts_combine17 :
  Γ st ⟦part17; part18; part19; part20⟧ =
  Γ st ⟦part17_to_end⟧ := by
    unfold part17
    rewrite [MLIR.part_assoc_dddd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine18]
    rfl
lemma parts_combine16 :
  Γ st ⟦part16; part17; part18; part19; part20⟧ =
  Γ st ⟦part16_to_end⟧ := by
    unfold part16
    rewrite [MLIR.part_assoc_dddd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine17]
    rfl
lemma parts_combine15 :
  Γ st ⟦part15; part16; part17; part18; part19; part20⟧ =
  Γ st ⟦part15_to_end⟧ := by
    unfold part15
    rewrite [MLIR.part_assoc_dddd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine16]
    rfl
lemma parts_combine14 :
  Γ st ⟦part14; part15; part16; part17; part18; part19; part20⟧ =
  Γ st ⟦part14_to_end⟧ := by
    unfold part14
    rewrite [MLIR.part_assoc_dddd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine15]
    rfl
lemma parts_combine13 :
  Γ st ⟦part13; part14; part15; part16; part17; part18; part19; part20⟧ =
  Γ st ⟦part13_to_end⟧ := by
    unfold part13
    rewrite [MLIR.part_assoc_dddd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine14]
    rfl
lemma parts_combine12 :
  Γ st ⟦part12; part13; part14; part15; part16; part17; part18; part19; part20⟧ =
  Γ st ⟦part12_to_end⟧ := by
    unfold part12
    rewrite [MLIR.part_assoc_dddd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine13]
    rfl
lemma parts_combine11 :
  Γ st ⟦part11; part12; part13; part14; part15; part16; part17; part18; part19; part20⟧ =
  Γ st ⟦part11_to_end⟧ := by
    unfold part11
    rewrite [MLIR.part_assoc_dddd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine12]
    rfl
lemma parts_combine10 :
  Γ st ⟦part10; part11; part12; part13; part14; part15; part16; part17; part18; part19; part20⟧ =
  Γ st ⟦part10_to_end⟧ := by
    unfold part10
    rewrite [MLIR.part_assoc_dddd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine11]
    rfl
lemma parts_combine9 :
  Γ st ⟦part9; part10; part11; part12; part13; part14; part15; part16; part17; part18; part19; part20⟧ =
  Γ st ⟦part9_to_end⟧ := by
    unfold part9
    rewrite [MLIR.part_assoc_dddd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine10]
    rfl
lemma parts_combine8 :
  Γ st ⟦part8; part9; part10; part11; part12; part13; part14; part15; part16; part17; part18; part19; part20⟧ =
  Γ st ⟦part8_to_end⟧ := by
    unfold part8
    rewrite [MLIR.part_assoc_dddd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine9]
    rfl
lemma parts_combine7 :
  Γ st ⟦part7; part8; part9; part10; part11; part12; part13; part14; part15; part16; part17; part18; part19; part20⟧ =
  Γ st ⟦part7_to_end⟧ := by
    unfold part7
    rewrite [MLIR.part_assoc_dddd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine8]
    rfl
lemma parts_combine6 :
  Γ st ⟦part6; part7; part8; part9; part10; part11; part12; part13; part14; part15; part16; part17; part18; part19; part20⟧ =
  Γ st ⟦part6_to_end⟧ := by
    unfold part6
    rewrite [MLIR.part_assoc_dddd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine7]
    rfl
lemma parts_combine5 :
  Γ st ⟦part5; part6; part7; part8; part9; part10; part11; part12; part13; part14; part15; part16; part17; part18; part19; part20⟧ =
  Γ st ⟦part5_to_end⟧ := by
    unfold part5
    rewrite [MLIR.part_assoc_dndd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine6]
    rfl
lemma parts_combine4 :
  Γ st ⟦part4; part5; part6; part7; part8; part9; part10; part11; part12; part13; part14; part15; part16; part17; part18; part19; part20⟧ =
  Γ st ⟦part4_to_end⟧ := by
    unfold part4
    rewrite [MLIR.part_assoc_nnnn]
    apply MLIR.nondet_step_eq
    intro st
    apply MLIR.nondet_step_eq
    intro st
    apply MLIR.nondet_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine5]
    rfl
lemma parts_combine3 :
  Γ st ⟦part3; part4; part5; part6; part7; part8; part9; part10; part11; part12; part13; part14; part15; part16; part17; part18; part19; part20⟧ =
  Γ st ⟦part3_to_end⟧ := by
    unfold part3
    rewrite [MLIR.part_assoc_dnnn]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.nondet_step_eq
    intro st
    apply MLIR.nondet_step_eq
    intro st
    apply MLIR.nondet_step_eq
    intro st
    rewrite [parts_combine4]
    rfl
lemma parts_combine2 :
  Γ st ⟦part2; part3; part4; part5; part6; part7; part8; part9; part10; part11; part12; part13; part14; part15; part16; part17; part18; part19; part20⟧ =
  Γ st ⟦part2_to_end⟧ := by
    unfold part2
    rewrite [MLIR.part_assoc_nnnn]
    apply MLIR.nondet_step_eq
    intro st
    apply MLIR.nondet_step_eq
    intro st
    apply MLIR.nondet_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine3]
    rfl
lemma parts_combine1 :
  Γ st ⟦part1; part2; part3; part4; part5; part6; part7; part8; part9; part10; part11; part12; part13; part14; part15; part16; part17; part18; part19; part20⟧ =
  Γ st ⟦part1_to_end⟧ := by
    unfold part1
    rewrite [MLIR.part_assoc_ndnn]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.nondet_step_eq
    intro st
    apply MLIR.nondet_step_eq
    intro st
    rewrite [parts_combine2]
    rfl
lemma parts_combine0 :
  Γ st ⟦part0; part1; part2; part3; part4; part5; part6; part7; part8; part9; part10; part11; part12; part13; part14; part15; part16; part17; part18; part19; part20⟧ =
  Γ st ⟦part0_to_end⟧ := by
    unfold part0
    rewrite [MLIR.part_assoc_dnnn]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.nondet_step_eq
    intro st
    apply MLIR.nondet_step_eq
    intro st
    apply MLIR.nondet_step_eq
    intro st
    rewrite [parts_combine1]
    rfl
lemma parts_combine :
  Γ st ⟦parts_combined⟧ =
  Γ st ⟦opt_full⟧ := 
    parts_combine0
end Risc0.computeDecode.Witness.Code