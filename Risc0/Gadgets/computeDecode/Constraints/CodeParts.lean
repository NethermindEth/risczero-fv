import Risc0.Gadgets.computeDecode.Constraints.CodeReordered

namespace Risc0.computeDecode.Constraints.Code

open MLIRNotation

def part0 : MLIRProgram :=   "%8" ←ₐ ⊤; "%3" ←ₐ .Const 4; "%11" ←ₐ .Get ⟨"data"⟩ 0 8; "%12" ←ₐ .Mul ⟨"%11"⟩ ⟨"%3"⟩
def part1 : MLIRProgram :=   "%6" ←ₐ .Const 8; "%13" ←ₐ .Get ⟨"data"⟩ 0 9; "%14" ←ₐ .Mul ⟨"%13"⟩ ⟨"%6"⟩; "%5" ←ₐ .Const 16
def part2 : MLIRProgram :=   "%15" ←ₐ .Get ⟨"data"⟩ 0 1; "%16" ←ₐ .Mul ⟨"%15"⟩ ⟨"%5"⟩; "%17" ←ₐ .Add ⟨"%16"⟩ ⟨"%14"⟩; "%18" ←ₐ .Add ⟨"%17"⟩ ⟨"%12"⟩
def part3 : MLIRProgram :=   "%10" ←ₐ .Get ⟨"data"⟩ 0 0; "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%10"⟩; "%7" ←ₐ .Const 64; "%20" ←ₐ .Get ⟨"data"⟩ 0 10
def part4 : MLIRProgram :=   "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%7"⟩; "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩; "%1" ←ₐ .Const 2; "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%1"⟩
def part5 : MLIRProgram :=   "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%3"⟩ ⟨"%24"⟩; "%26" ←ₐ ⟨"%8"⟩ &₀ ⟨"%25"⟩
def part6 : MLIRProgram :=   "%28" ←ₐ .Get ⟨"data"⟩ 0 4; "%29" ←ₐ .Mul ⟨"%28"⟩ ⟨"%3"⟩; "%31" ←ₐ .Get ⟨"data"⟩ 0 2; "%32" ←ₐ .Mul ⟨"%31"⟩ ⟨"%1"⟩
def part7 : MLIRProgram :=   "%33" ←ₐ .Get ⟨"data"⟩ 0 12; "%34" ←ₐ .Mul ⟨"%33"⟩ ⟨"%6"⟩; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%32"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 11
def part8 : MLIRProgram :=   "%36" ←ₐ .Add ⟨"%35"⟩ ⟨"%30"⟩; "%37" ←ₐ .Mul ⟨"%36"⟩ ⟨"%5"⟩; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%29"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 3
def part9 : MLIRProgram :=   "%39" ←ₐ .Add ⟨"%38"⟩ ⟨"%27"⟩; "%2" ←ₐ .Const 3; "%40" ←ₐ .Sub ⟨"%2"⟩ ⟨"%39"⟩; "%41" ←ₐ ⟨"%26"⟩ &₀ ⟨"%40"⟩
def part10 : MLIRProgram :=   "%43" ←ₐ .Get ⟨"data"⟩ 0 7; "%44" ←ₐ .Mul ⟨"%43"⟩ ⟨"%3"⟩; "%46" ←ₐ .Get ⟨"data"⟩ 0 15; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%3"⟩
def part11 : MLIRProgram :=   "%45" ←ₐ .Get ⟨"data"⟩ 0 5; "%48" ←ₐ .Add ⟨"%47"⟩ ⟨"%45"⟩; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%5"⟩; "%4" ←ₐ .Const 128
def part12 : MLIRProgram :=   "%50" ←ₐ .Get ⟨"data"⟩ 0 14; "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%4"⟩; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%49"⟩; "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%44"⟩
def part13 : MLIRProgram :=   "%42" ←ₐ .Get ⟨"data"⟩ 0 6; "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%42"⟩; "%55" ←ₐ .Sub ⟨"%1"⟩ ⟨"%54"⟩; "%56" ←ₐ ⟨"%41"⟩ &₀ ⟨"%55"⟩
def part14 : MLIRProgram :=   "%58" ←ₐ .Get ⟨"data"⟩ 0 16; "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%4"⟩; "%57" ←ₐ .Get ⟨"data"⟩ 0 17; "%60" ←ₐ .Add ⟨"%59"⟩ ⟨"%57"⟩
def part15 : MLIRProgram :=   "%0" ←ₐ .Const 1; "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩; "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩

def part0_to_end : MLIRProgram :=   "%8" ←ₐ ⊤; "%3" ←ₐ .Const 4; "%11" ←ₐ .Get ⟨"data"⟩ 0 8; "%12" ←ₐ .Mul ⟨"%11"⟩ ⟨"%3"⟩; "%6" ←ₐ .Const 8; "%13" ←ₐ .Get ⟨"data"⟩ 0 9; "%14" ←ₐ .Mul ⟨"%13"⟩ ⟨"%6"⟩; "%5" ←ₐ .Const 16; "%15" ←ₐ .Get ⟨"data"⟩ 0 1; "%16" ←ₐ .Mul ⟨"%15"⟩ ⟨"%5"⟩; "%17" ←ₐ .Add ⟨"%16"⟩ ⟨"%14"⟩; "%18" ←ₐ .Add ⟨"%17"⟩ ⟨"%12"⟩; "%10" ←ₐ .Get ⟨"data"⟩ 0 0; "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%10"⟩; "%7" ←ₐ .Const 64; "%20" ←ₐ .Get ⟨"data"⟩ 0 10; "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%7"⟩; "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩; "%1" ←ₐ .Const 2; "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%1"⟩; "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%3"⟩ ⟨"%24"⟩; "%26" ←ₐ ⟨"%8"⟩ &₀ ⟨"%25"⟩; "%28" ←ₐ .Get ⟨"data"⟩ 0 4; "%29" ←ₐ .Mul ⟨"%28"⟩ ⟨"%3"⟩; "%31" ←ₐ .Get ⟨"data"⟩ 0 2; "%32" ←ₐ .Mul ⟨"%31"⟩ ⟨"%1"⟩; "%33" ←ₐ .Get ⟨"data"⟩ 0 12; "%34" ←ₐ .Mul ⟨"%33"⟩ ⟨"%6"⟩; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%32"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 11; "%36" ←ₐ .Add ⟨"%35"⟩ ⟨"%30"⟩; "%37" ←ₐ .Mul ⟨"%36"⟩ ⟨"%5"⟩; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%29"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 3; "%39" ←ₐ .Add ⟨"%38"⟩ ⟨"%27"⟩; "%2" ←ₐ .Const 3; "%40" ←ₐ .Sub ⟨"%2"⟩ ⟨"%39"⟩; "%41" ←ₐ ⟨"%26"⟩ &₀ ⟨"%40"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 7; "%44" ←ₐ .Mul ⟨"%43"⟩ ⟨"%3"⟩; "%46" ←ₐ .Get ⟨"data"⟩ 0 15; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%3"⟩; "%45" ←ₐ .Get ⟨"data"⟩ 0 5; "%48" ←ₐ .Add ⟨"%47"⟩ ⟨"%45"⟩; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%5"⟩; "%4" ←ₐ .Const 128; "%50" ←ₐ .Get ⟨"data"⟩ 0 14; "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%4"⟩; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%49"⟩; "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%44"⟩; "%42" ←ₐ .Get ⟨"data"⟩ 0 6; "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%42"⟩; "%55" ←ₐ .Sub ⟨"%1"⟩ ⟨"%54"⟩; "%56" ←ₐ ⟨"%41"⟩ &₀ ⟨"%55"⟩; "%58" ←ₐ .Get ⟨"data"⟩ 0 16; "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%4"⟩; "%57" ←ₐ .Get ⟨"data"⟩ 0 17; "%60" ←ₐ .Add ⟨"%59"⟩ ⟨"%57"⟩; "%0" ←ₐ .Const 1; "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩; "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩
def part1_to_end : MLIRProgram :=   "%6" ←ₐ .Const 8; "%13" ←ₐ .Get ⟨"data"⟩ 0 9; "%14" ←ₐ .Mul ⟨"%13"⟩ ⟨"%6"⟩; "%5" ←ₐ .Const 16; "%15" ←ₐ .Get ⟨"data"⟩ 0 1; "%16" ←ₐ .Mul ⟨"%15"⟩ ⟨"%5"⟩; "%17" ←ₐ .Add ⟨"%16"⟩ ⟨"%14"⟩; "%18" ←ₐ .Add ⟨"%17"⟩ ⟨"%12"⟩; "%10" ←ₐ .Get ⟨"data"⟩ 0 0; "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%10"⟩; "%7" ←ₐ .Const 64; "%20" ←ₐ .Get ⟨"data"⟩ 0 10; "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%7"⟩; "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩; "%1" ←ₐ .Const 2; "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%1"⟩; "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%3"⟩ ⟨"%24"⟩; "%26" ←ₐ ⟨"%8"⟩ &₀ ⟨"%25"⟩; "%28" ←ₐ .Get ⟨"data"⟩ 0 4; "%29" ←ₐ .Mul ⟨"%28"⟩ ⟨"%3"⟩; "%31" ←ₐ .Get ⟨"data"⟩ 0 2; "%32" ←ₐ .Mul ⟨"%31"⟩ ⟨"%1"⟩; "%33" ←ₐ .Get ⟨"data"⟩ 0 12; "%34" ←ₐ .Mul ⟨"%33"⟩ ⟨"%6"⟩; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%32"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 11; "%36" ←ₐ .Add ⟨"%35"⟩ ⟨"%30"⟩; "%37" ←ₐ .Mul ⟨"%36"⟩ ⟨"%5"⟩; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%29"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 3; "%39" ←ₐ .Add ⟨"%38"⟩ ⟨"%27"⟩; "%2" ←ₐ .Const 3; "%40" ←ₐ .Sub ⟨"%2"⟩ ⟨"%39"⟩; "%41" ←ₐ ⟨"%26"⟩ &₀ ⟨"%40"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 7; "%44" ←ₐ .Mul ⟨"%43"⟩ ⟨"%3"⟩; "%46" ←ₐ .Get ⟨"data"⟩ 0 15; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%3"⟩; "%45" ←ₐ .Get ⟨"data"⟩ 0 5; "%48" ←ₐ .Add ⟨"%47"⟩ ⟨"%45"⟩; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%5"⟩; "%4" ←ₐ .Const 128; "%50" ←ₐ .Get ⟨"data"⟩ 0 14; "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%4"⟩; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%49"⟩; "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%44"⟩; "%42" ←ₐ .Get ⟨"data"⟩ 0 6; "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%42"⟩; "%55" ←ₐ .Sub ⟨"%1"⟩ ⟨"%54"⟩; "%56" ←ₐ ⟨"%41"⟩ &₀ ⟨"%55"⟩; "%58" ←ₐ .Get ⟨"data"⟩ 0 16; "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%4"⟩; "%57" ←ₐ .Get ⟨"data"⟩ 0 17; "%60" ←ₐ .Add ⟨"%59"⟩ ⟨"%57"⟩; "%0" ←ₐ .Const 1; "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩; "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩
def part2_to_end : MLIRProgram :=   "%15" ←ₐ .Get ⟨"data"⟩ 0 1; "%16" ←ₐ .Mul ⟨"%15"⟩ ⟨"%5"⟩; "%17" ←ₐ .Add ⟨"%16"⟩ ⟨"%14"⟩; "%18" ←ₐ .Add ⟨"%17"⟩ ⟨"%12"⟩; "%10" ←ₐ .Get ⟨"data"⟩ 0 0; "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%10"⟩; "%7" ←ₐ .Const 64; "%20" ←ₐ .Get ⟨"data"⟩ 0 10; "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%7"⟩; "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩; "%1" ←ₐ .Const 2; "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%1"⟩; "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%3"⟩ ⟨"%24"⟩; "%26" ←ₐ ⟨"%8"⟩ &₀ ⟨"%25"⟩; "%28" ←ₐ .Get ⟨"data"⟩ 0 4; "%29" ←ₐ .Mul ⟨"%28"⟩ ⟨"%3"⟩; "%31" ←ₐ .Get ⟨"data"⟩ 0 2; "%32" ←ₐ .Mul ⟨"%31"⟩ ⟨"%1"⟩; "%33" ←ₐ .Get ⟨"data"⟩ 0 12; "%34" ←ₐ .Mul ⟨"%33"⟩ ⟨"%6"⟩; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%32"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 11; "%36" ←ₐ .Add ⟨"%35"⟩ ⟨"%30"⟩; "%37" ←ₐ .Mul ⟨"%36"⟩ ⟨"%5"⟩; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%29"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 3; "%39" ←ₐ .Add ⟨"%38"⟩ ⟨"%27"⟩; "%2" ←ₐ .Const 3; "%40" ←ₐ .Sub ⟨"%2"⟩ ⟨"%39"⟩; "%41" ←ₐ ⟨"%26"⟩ &₀ ⟨"%40"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 7; "%44" ←ₐ .Mul ⟨"%43"⟩ ⟨"%3"⟩; "%46" ←ₐ .Get ⟨"data"⟩ 0 15; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%3"⟩; "%45" ←ₐ .Get ⟨"data"⟩ 0 5; "%48" ←ₐ .Add ⟨"%47"⟩ ⟨"%45"⟩; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%5"⟩; "%4" ←ₐ .Const 128; "%50" ←ₐ .Get ⟨"data"⟩ 0 14; "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%4"⟩; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%49"⟩; "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%44"⟩; "%42" ←ₐ .Get ⟨"data"⟩ 0 6; "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%42"⟩; "%55" ←ₐ .Sub ⟨"%1"⟩ ⟨"%54"⟩; "%56" ←ₐ ⟨"%41"⟩ &₀ ⟨"%55"⟩; "%58" ←ₐ .Get ⟨"data"⟩ 0 16; "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%4"⟩; "%57" ←ₐ .Get ⟨"data"⟩ 0 17; "%60" ←ₐ .Add ⟨"%59"⟩ ⟨"%57"⟩; "%0" ←ₐ .Const 1; "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩; "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩
def part3_to_end : MLIRProgram :=   "%10" ←ₐ .Get ⟨"data"⟩ 0 0; "%19" ←ₐ .Add ⟨"%18"⟩ ⟨"%10"⟩; "%7" ←ₐ .Const 64; "%20" ←ₐ .Get ⟨"data"⟩ 0 10; "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%7"⟩; "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩; "%1" ←ₐ .Const 2; "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%1"⟩; "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%3"⟩ ⟨"%24"⟩; "%26" ←ₐ ⟨"%8"⟩ &₀ ⟨"%25"⟩; "%28" ←ₐ .Get ⟨"data"⟩ 0 4; "%29" ←ₐ .Mul ⟨"%28"⟩ ⟨"%3"⟩; "%31" ←ₐ .Get ⟨"data"⟩ 0 2; "%32" ←ₐ .Mul ⟨"%31"⟩ ⟨"%1"⟩; "%33" ←ₐ .Get ⟨"data"⟩ 0 12; "%34" ←ₐ .Mul ⟨"%33"⟩ ⟨"%6"⟩; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%32"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 11; "%36" ←ₐ .Add ⟨"%35"⟩ ⟨"%30"⟩; "%37" ←ₐ .Mul ⟨"%36"⟩ ⟨"%5"⟩; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%29"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 3; "%39" ←ₐ .Add ⟨"%38"⟩ ⟨"%27"⟩; "%2" ←ₐ .Const 3; "%40" ←ₐ .Sub ⟨"%2"⟩ ⟨"%39"⟩; "%41" ←ₐ ⟨"%26"⟩ &₀ ⟨"%40"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 7; "%44" ←ₐ .Mul ⟨"%43"⟩ ⟨"%3"⟩; "%46" ←ₐ .Get ⟨"data"⟩ 0 15; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%3"⟩; "%45" ←ₐ .Get ⟨"data"⟩ 0 5; "%48" ←ₐ .Add ⟨"%47"⟩ ⟨"%45"⟩; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%5"⟩; "%4" ←ₐ .Const 128; "%50" ←ₐ .Get ⟨"data"⟩ 0 14; "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%4"⟩; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%49"⟩; "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%44"⟩; "%42" ←ₐ .Get ⟨"data"⟩ 0 6; "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%42"⟩; "%55" ←ₐ .Sub ⟨"%1"⟩ ⟨"%54"⟩; "%56" ←ₐ ⟨"%41"⟩ &₀ ⟨"%55"⟩; "%58" ←ₐ .Get ⟨"data"⟩ 0 16; "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%4"⟩; "%57" ←ₐ .Get ⟨"data"⟩ 0 17; "%60" ←ₐ .Add ⟨"%59"⟩ ⟨"%57"⟩; "%0" ←ₐ .Const 1; "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩; "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩
def part4_to_end : MLIRProgram :=   "%21" ←ₐ .Mul ⟨"%20"⟩ ⟨"%7"⟩; "%22" ←ₐ .Add ⟨"%21"⟩ ⟨"%19"⟩; "%1" ←ₐ .Const 2; "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%1"⟩; "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%3"⟩ ⟨"%24"⟩; "%26" ←ₐ ⟨"%8"⟩ &₀ ⟨"%25"⟩; "%28" ←ₐ .Get ⟨"data"⟩ 0 4; "%29" ←ₐ .Mul ⟨"%28"⟩ ⟨"%3"⟩; "%31" ←ₐ .Get ⟨"data"⟩ 0 2; "%32" ←ₐ .Mul ⟨"%31"⟩ ⟨"%1"⟩; "%33" ←ₐ .Get ⟨"data"⟩ 0 12; "%34" ←ₐ .Mul ⟨"%33"⟩ ⟨"%6"⟩; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%32"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 11; "%36" ←ₐ .Add ⟨"%35"⟩ ⟨"%30"⟩; "%37" ←ₐ .Mul ⟨"%36"⟩ ⟨"%5"⟩; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%29"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 3; "%39" ←ₐ .Add ⟨"%38"⟩ ⟨"%27"⟩; "%2" ←ₐ .Const 3; "%40" ←ₐ .Sub ⟨"%2"⟩ ⟨"%39"⟩; "%41" ←ₐ ⟨"%26"⟩ &₀ ⟨"%40"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 7; "%44" ←ₐ .Mul ⟨"%43"⟩ ⟨"%3"⟩; "%46" ←ₐ .Get ⟨"data"⟩ 0 15; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%3"⟩; "%45" ←ₐ .Get ⟨"data"⟩ 0 5; "%48" ←ₐ .Add ⟨"%47"⟩ ⟨"%45"⟩; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%5"⟩; "%4" ←ₐ .Const 128; "%50" ←ₐ .Get ⟨"data"⟩ 0 14; "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%4"⟩; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%49"⟩; "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%44"⟩; "%42" ←ₐ .Get ⟨"data"⟩ 0 6; "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%42"⟩; "%55" ←ₐ .Sub ⟨"%1"⟩ ⟨"%54"⟩; "%56" ←ₐ ⟨"%41"⟩ &₀ ⟨"%55"⟩; "%58" ←ₐ .Get ⟨"data"⟩ 0 16; "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%4"⟩; "%57" ←ₐ .Get ⟨"data"⟩ 0 17; "%60" ←ₐ .Add ⟨"%59"⟩ ⟨"%57"⟩; "%0" ←ₐ .Const 1; "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩; "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩
def part5_to_end : MLIRProgram :=   "%9" ←ₐ .Get ⟨"data"⟩ 0 13; "%24" ←ₐ .Add ⟨"%23"⟩ ⟨"%9"⟩; "%25" ←ₐ .Sub ⟨"%3"⟩ ⟨"%24"⟩; "%26" ←ₐ ⟨"%8"⟩ &₀ ⟨"%25"⟩; "%28" ←ₐ .Get ⟨"data"⟩ 0 4; "%29" ←ₐ .Mul ⟨"%28"⟩ ⟨"%3"⟩; "%31" ←ₐ .Get ⟨"data"⟩ 0 2; "%32" ←ₐ .Mul ⟨"%31"⟩ ⟨"%1"⟩; "%33" ←ₐ .Get ⟨"data"⟩ 0 12; "%34" ←ₐ .Mul ⟨"%33"⟩ ⟨"%6"⟩; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%32"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 11; "%36" ←ₐ .Add ⟨"%35"⟩ ⟨"%30"⟩; "%37" ←ₐ .Mul ⟨"%36"⟩ ⟨"%5"⟩; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%29"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 3; "%39" ←ₐ .Add ⟨"%38"⟩ ⟨"%27"⟩; "%2" ←ₐ .Const 3; "%40" ←ₐ .Sub ⟨"%2"⟩ ⟨"%39"⟩; "%41" ←ₐ ⟨"%26"⟩ &₀ ⟨"%40"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 7; "%44" ←ₐ .Mul ⟨"%43"⟩ ⟨"%3"⟩; "%46" ←ₐ .Get ⟨"data"⟩ 0 15; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%3"⟩; "%45" ←ₐ .Get ⟨"data"⟩ 0 5; "%48" ←ₐ .Add ⟨"%47"⟩ ⟨"%45"⟩; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%5"⟩; "%4" ←ₐ .Const 128; "%50" ←ₐ .Get ⟨"data"⟩ 0 14; "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%4"⟩; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%49"⟩; "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%44"⟩; "%42" ←ₐ .Get ⟨"data"⟩ 0 6; "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%42"⟩; "%55" ←ₐ .Sub ⟨"%1"⟩ ⟨"%54"⟩; "%56" ←ₐ ⟨"%41"⟩ &₀ ⟨"%55"⟩; "%58" ←ₐ .Get ⟨"data"⟩ 0 16; "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%4"⟩; "%57" ←ₐ .Get ⟨"data"⟩ 0 17; "%60" ←ₐ .Add ⟨"%59"⟩ ⟨"%57"⟩; "%0" ←ₐ .Const 1; "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩; "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩
def part6_to_end : MLIRProgram :=   "%28" ←ₐ .Get ⟨"data"⟩ 0 4; "%29" ←ₐ .Mul ⟨"%28"⟩ ⟨"%3"⟩; "%31" ←ₐ .Get ⟨"data"⟩ 0 2; "%32" ←ₐ .Mul ⟨"%31"⟩ ⟨"%1"⟩; "%33" ←ₐ .Get ⟨"data"⟩ 0 12; "%34" ←ₐ .Mul ⟨"%33"⟩ ⟨"%6"⟩; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%32"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 11; "%36" ←ₐ .Add ⟨"%35"⟩ ⟨"%30"⟩; "%37" ←ₐ .Mul ⟨"%36"⟩ ⟨"%5"⟩; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%29"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 3; "%39" ←ₐ .Add ⟨"%38"⟩ ⟨"%27"⟩; "%2" ←ₐ .Const 3; "%40" ←ₐ .Sub ⟨"%2"⟩ ⟨"%39"⟩; "%41" ←ₐ ⟨"%26"⟩ &₀ ⟨"%40"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 7; "%44" ←ₐ .Mul ⟨"%43"⟩ ⟨"%3"⟩; "%46" ←ₐ .Get ⟨"data"⟩ 0 15; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%3"⟩; "%45" ←ₐ .Get ⟨"data"⟩ 0 5; "%48" ←ₐ .Add ⟨"%47"⟩ ⟨"%45"⟩; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%5"⟩; "%4" ←ₐ .Const 128; "%50" ←ₐ .Get ⟨"data"⟩ 0 14; "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%4"⟩; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%49"⟩; "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%44"⟩; "%42" ←ₐ .Get ⟨"data"⟩ 0 6; "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%42"⟩; "%55" ←ₐ .Sub ⟨"%1"⟩ ⟨"%54"⟩; "%56" ←ₐ ⟨"%41"⟩ &₀ ⟨"%55"⟩; "%58" ←ₐ .Get ⟨"data"⟩ 0 16; "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%4"⟩; "%57" ←ₐ .Get ⟨"data"⟩ 0 17; "%60" ←ₐ .Add ⟨"%59"⟩ ⟨"%57"⟩; "%0" ←ₐ .Const 1; "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩; "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩
def part7_to_end : MLIRProgram :=   "%33" ←ₐ .Get ⟨"data"⟩ 0 12; "%34" ←ₐ .Mul ⟨"%33"⟩ ⟨"%6"⟩; "%35" ←ₐ .Add ⟨"%34"⟩ ⟨"%32"⟩; "%30" ←ₐ .Get ⟨"data"⟩ 0 11; "%36" ←ₐ .Add ⟨"%35"⟩ ⟨"%30"⟩; "%37" ←ₐ .Mul ⟨"%36"⟩ ⟨"%5"⟩; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%29"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 3; "%39" ←ₐ .Add ⟨"%38"⟩ ⟨"%27"⟩; "%2" ←ₐ .Const 3; "%40" ←ₐ .Sub ⟨"%2"⟩ ⟨"%39"⟩; "%41" ←ₐ ⟨"%26"⟩ &₀ ⟨"%40"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 7; "%44" ←ₐ .Mul ⟨"%43"⟩ ⟨"%3"⟩; "%46" ←ₐ .Get ⟨"data"⟩ 0 15; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%3"⟩; "%45" ←ₐ .Get ⟨"data"⟩ 0 5; "%48" ←ₐ .Add ⟨"%47"⟩ ⟨"%45"⟩; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%5"⟩; "%4" ←ₐ .Const 128; "%50" ←ₐ .Get ⟨"data"⟩ 0 14; "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%4"⟩; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%49"⟩; "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%44"⟩; "%42" ←ₐ .Get ⟨"data"⟩ 0 6; "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%42"⟩; "%55" ←ₐ .Sub ⟨"%1"⟩ ⟨"%54"⟩; "%56" ←ₐ ⟨"%41"⟩ &₀ ⟨"%55"⟩; "%58" ←ₐ .Get ⟨"data"⟩ 0 16; "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%4"⟩; "%57" ←ₐ .Get ⟨"data"⟩ 0 17; "%60" ←ₐ .Add ⟨"%59"⟩ ⟨"%57"⟩; "%0" ←ₐ .Const 1; "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩; "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩
def part8_to_end : MLIRProgram :=   "%36" ←ₐ .Add ⟨"%35"⟩ ⟨"%30"⟩; "%37" ←ₐ .Mul ⟨"%36"⟩ ⟨"%5"⟩; "%38" ←ₐ .Add ⟨"%37"⟩ ⟨"%29"⟩; "%27" ←ₐ .Get ⟨"data"⟩ 0 3; "%39" ←ₐ .Add ⟨"%38"⟩ ⟨"%27"⟩; "%2" ←ₐ .Const 3; "%40" ←ₐ .Sub ⟨"%2"⟩ ⟨"%39"⟩; "%41" ←ₐ ⟨"%26"⟩ &₀ ⟨"%40"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 7; "%44" ←ₐ .Mul ⟨"%43"⟩ ⟨"%3"⟩; "%46" ←ₐ .Get ⟨"data"⟩ 0 15; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%3"⟩; "%45" ←ₐ .Get ⟨"data"⟩ 0 5; "%48" ←ₐ .Add ⟨"%47"⟩ ⟨"%45"⟩; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%5"⟩; "%4" ←ₐ .Const 128; "%50" ←ₐ .Get ⟨"data"⟩ 0 14; "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%4"⟩; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%49"⟩; "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%44"⟩; "%42" ←ₐ .Get ⟨"data"⟩ 0 6; "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%42"⟩; "%55" ←ₐ .Sub ⟨"%1"⟩ ⟨"%54"⟩; "%56" ←ₐ ⟨"%41"⟩ &₀ ⟨"%55"⟩; "%58" ←ₐ .Get ⟨"data"⟩ 0 16; "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%4"⟩; "%57" ←ₐ .Get ⟨"data"⟩ 0 17; "%60" ←ₐ .Add ⟨"%59"⟩ ⟨"%57"⟩; "%0" ←ₐ .Const 1; "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩; "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩
def part9_to_end : MLIRProgram :=   "%39" ←ₐ .Add ⟨"%38"⟩ ⟨"%27"⟩; "%2" ←ₐ .Const 3; "%40" ←ₐ .Sub ⟨"%2"⟩ ⟨"%39"⟩; "%41" ←ₐ ⟨"%26"⟩ &₀ ⟨"%40"⟩; "%43" ←ₐ .Get ⟨"data"⟩ 0 7; "%44" ←ₐ .Mul ⟨"%43"⟩ ⟨"%3"⟩; "%46" ←ₐ .Get ⟨"data"⟩ 0 15; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%3"⟩; "%45" ←ₐ .Get ⟨"data"⟩ 0 5; "%48" ←ₐ .Add ⟨"%47"⟩ ⟨"%45"⟩; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%5"⟩; "%4" ←ₐ .Const 128; "%50" ←ₐ .Get ⟨"data"⟩ 0 14; "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%4"⟩; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%49"⟩; "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%44"⟩; "%42" ←ₐ .Get ⟨"data"⟩ 0 6; "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%42"⟩; "%55" ←ₐ .Sub ⟨"%1"⟩ ⟨"%54"⟩; "%56" ←ₐ ⟨"%41"⟩ &₀ ⟨"%55"⟩; "%58" ←ₐ .Get ⟨"data"⟩ 0 16; "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%4"⟩; "%57" ←ₐ .Get ⟨"data"⟩ 0 17; "%60" ←ₐ .Add ⟨"%59"⟩ ⟨"%57"⟩; "%0" ←ₐ .Const 1; "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩; "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩
def part10_to_end : MLIRProgram :=   "%43" ←ₐ .Get ⟨"data"⟩ 0 7; "%44" ←ₐ .Mul ⟨"%43"⟩ ⟨"%3"⟩; "%46" ←ₐ .Get ⟨"data"⟩ 0 15; "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%3"⟩; "%45" ←ₐ .Get ⟨"data"⟩ 0 5; "%48" ←ₐ .Add ⟨"%47"⟩ ⟨"%45"⟩; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%5"⟩; "%4" ←ₐ .Const 128; "%50" ←ₐ .Get ⟨"data"⟩ 0 14; "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%4"⟩; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%49"⟩; "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%44"⟩; "%42" ←ₐ .Get ⟨"data"⟩ 0 6; "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%42"⟩; "%55" ←ₐ .Sub ⟨"%1"⟩ ⟨"%54"⟩; "%56" ←ₐ ⟨"%41"⟩ &₀ ⟨"%55"⟩; "%58" ←ₐ .Get ⟨"data"⟩ 0 16; "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%4"⟩; "%57" ←ₐ .Get ⟨"data"⟩ 0 17; "%60" ←ₐ .Add ⟨"%59"⟩ ⟨"%57"⟩; "%0" ←ₐ .Const 1; "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩; "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩
def part11_to_end : MLIRProgram :=   "%45" ←ₐ .Get ⟨"data"⟩ 0 5; "%48" ←ₐ .Add ⟨"%47"⟩ ⟨"%45"⟩; "%49" ←ₐ .Mul ⟨"%48"⟩ ⟨"%5"⟩; "%4" ←ₐ .Const 128; "%50" ←ₐ .Get ⟨"data"⟩ 0 14; "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%4"⟩; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%49"⟩; "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%44"⟩; "%42" ←ₐ .Get ⟨"data"⟩ 0 6; "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%42"⟩; "%55" ←ₐ .Sub ⟨"%1"⟩ ⟨"%54"⟩; "%56" ←ₐ ⟨"%41"⟩ &₀ ⟨"%55"⟩; "%58" ←ₐ .Get ⟨"data"⟩ 0 16; "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%4"⟩; "%57" ←ₐ .Get ⟨"data"⟩ 0 17; "%60" ←ₐ .Add ⟨"%59"⟩ ⟨"%57"⟩; "%0" ←ₐ .Const 1; "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩; "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩
def part12_to_end : MLIRProgram :=   "%50" ←ₐ .Get ⟨"data"⟩ 0 14; "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%4"⟩; "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%49"⟩; "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%44"⟩; "%42" ←ₐ .Get ⟨"data"⟩ 0 6; "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%42"⟩; "%55" ←ₐ .Sub ⟨"%1"⟩ ⟨"%54"⟩; "%56" ←ₐ ⟨"%41"⟩ &₀ ⟨"%55"⟩; "%58" ←ₐ .Get ⟨"data"⟩ 0 16; "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%4"⟩; "%57" ←ₐ .Get ⟨"data"⟩ 0 17; "%60" ←ₐ .Add ⟨"%59"⟩ ⟨"%57"⟩; "%0" ←ₐ .Const 1; "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩; "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩
def part13_to_end : MLIRProgram :=   "%42" ←ₐ .Get ⟨"data"⟩ 0 6; "%54" ←ₐ .Add ⟨"%53"⟩ ⟨"%42"⟩; "%55" ←ₐ .Sub ⟨"%1"⟩ ⟨"%54"⟩; "%56" ←ₐ ⟨"%41"⟩ &₀ ⟨"%55"⟩; "%58" ←ₐ .Get ⟨"data"⟩ 0 16; "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%4"⟩; "%57" ←ₐ .Get ⟨"data"⟩ 0 17; "%60" ←ₐ .Add ⟨"%59"⟩ ⟨"%57"⟩; "%0" ←ₐ .Const 1; "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩; "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩
def part14_to_end : MLIRProgram :=   "%58" ←ₐ .Get ⟨"data"⟩ 0 16; "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%4"⟩; "%57" ←ₐ .Get ⟨"data"⟩ 0 17; "%60" ←ₐ .Add ⟨"%59"⟩ ⟨"%57"⟩; "%0" ←ₐ .Const 1; "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩; "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩
def part15_to_end : MLIRProgram :=   "%0" ←ₐ .Const 1; "%61" ←ₐ .Sub ⟨"%0"⟩ ⟨"%60"⟩; "%62" ←ₐ ⟨"%56"⟩ &₀ ⟨"%61"⟩

abbrev parts_combined : MLIRProgram :=
  part0; part1; part2; part3; part4; part5; part6; part7; part8; part9; part10; part11; part12; part13; part14; part15

lemma parts_combine15 :
  Γ st ⟦part15⟧ =
  Γ st ⟦part15_to_end⟧ := by
    rfl
lemma parts_combine14 :
  Γ st ⟦part14; part15⟧ =
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
  Γ st ⟦part13; part14; part15⟧ =
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
  Γ st ⟦part12; part13; part14; part15⟧ =
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
  Γ st ⟦part11; part12; part13; part14; part15⟧ =
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
  Γ st ⟦part10; part11; part12; part13; part14; part15⟧ =
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
  Γ st ⟦part9; part10; part11; part12; part13; part14; part15⟧ =
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
  Γ st ⟦part8; part9; part10; part11; part12; part13; part14; part15⟧ =
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
  Γ st ⟦part7; part8; part9; part10; part11; part12; part13; part14; part15⟧ =
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
  Γ st ⟦part6; part7; part8; part9; part10; part11; part12; part13; part14; part15⟧ =
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
  Γ st ⟦part5; part6; part7; part8; part9; part10; part11; part12; part13; part14; part15⟧ =
  Γ st ⟦part5_to_end⟧ := by
    unfold part5
    rewrite [MLIR.part_assoc_dddd]
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
  Γ st ⟦part4; part5; part6; part7; part8; part9; part10; part11; part12; part13; part14; part15⟧ =
  Γ st ⟦part4_to_end⟧ := by
    unfold part4
    rewrite [MLIR.part_assoc_dddd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine5]
    rfl
lemma parts_combine3 :
  Γ st ⟦part3; part4; part5; part6; part7; part8; part9; part10; part11; part12; part13; part14; part15⟧ =
  Γ st ⟦part3_to_end⟧ := by
    unfold part3
    rewrite [MLIR.part_assoc_dddd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine4]
    rfl
lemma parts_combine2 :
  Γ st ⟦part2; part3; part4; part5; part6; part7; part8; part9; part10; part11; part12; part13; part14; part15⟧ =
  Γ st ⟦part2_to_end⟧ := by
    unfold part2
    rewrite [MLIR.part_assoc_dddd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine3]
    rfl
lemma parts_combine1 :
  Γ st ⟦part1; part2; part3; part4; part5; part6; part7; part8; part9; part10; part11; part12; part13; part14; part15⟧ =
  Γ st ⟦part1_to_end⟧ := by
    unfold part1
    rewrite [MLIR.part_assoc_dddd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine2]
    rfl
lemma parts_combine0 :
  Γ st ⟦part0; part1; part2; part3; part4; part5; part6; part7; part8; part9; part10; part11; part12; part13; part14; part15⟧ =
  Γ st ⟦part0_to_end⟧ := by
    unfold part0
    rewrite [MLIR.part_assoc_dddd]
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    apply MLIR.seq_step_eq
    intro st
    rewrite [parts_combine1]
    rfl
lemma parts_combine :
  Γ st ⟦parts_combined⟧ =
  Γ st ⟦opt_full⟧ := 
    parts_combine0
end Risc0.computeDecode.Constraints.Code