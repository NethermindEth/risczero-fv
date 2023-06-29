import Risc0.Basic
import Risc0.Lemmas

namespace Risc0.OneHot20.Witness.Code

open MLIRNotation

def full : MLIRProgram :=
  "%0" ←ₐ .Const 19;
  "%1" ←ₐ .Const 18;
  "%2" ←ₐ .Const 17;
  "%3" ←ₐ .Const 16;
  "%4" ←ₐ .Const 15;
  "%5" ←ₐ .Const 14;
  "%6" ←ₐ .Const 13;
  "%7" ←ₐ .Const 12;
  "%8" ←ₐ .Const 11;
  "%9" ←ₐ .Const 10;
  "%10" ←ₐ .Const 9;
  "%11" ←ₐ .Const 8;
  "%12" ←ₐ .Const 7;
  "%13" ←ₐ .Const 6;
  "%14" ←ₐ .Const 5;
  "%15" ←ₐ .Const 4;
  "%16" ←ₐ .Const 3;
  "%17" ←ₐ .Const 2;
  "%18" ←ₐ .Const 1;
  "%19" ←ₐ .Const 0;
  "%20" ←ₐ .Get ⟨"code"⟩ 0 0;
  nondet (
    "%138" ←ₐ ??₀⟨"%20"⟩;
    ⟨"data"⟩[0] ←ᵢ ⟨"%138"⟩;
    "%139" ←ₐ .Sub ⟨"%20"⟩ ⟨"%18"⟩;
    "%140" ←ₐ ??₀⟨"%139"⟩;
    ⟨"data"⟩[1] ←ᵢ ⟨"%140"⟩;
    "%141" ←ₐ .Sub ⟨"%20"⟩ ⟨"%17"⟩;
    "%142" ←ₐ ??₀⟨"%141"⟩;
    ⟨"data"⟩[2] ←ᵢ ⟨"%142"⟩;
    "%143" ←ₐ .Sub ⟨"%20"⟩ ⟨"%16"⟩;
    "%144" ←ₐ ??₀⟨"%143"⟩;
    ⟨"data"⟩[3] ←ᵢ ⟨"%144"⟩;
    "%145" ←ₐ .Sub ⟨"%20"⟩ ⟨"%15"⟩;
    "%146" ←ₐ ??₀⟨"%145"⟩;
    ⟨"data"⟩[4] ←ᵢ ⟨"%146"⟩;
    "%147" ←ₐ .Sub ⟨"%20"⟩ ⟨"%14"⟩;
    "%148" ←ₐ ??₀⟨"%147"⟩;
    ⟨"data"⟩[5] ←ᵢ ⟨"%148"⟩;
    "%149" ←ₐ .Sub ⟨"%20"⟩ ⟨"%13"⟩;
    "%150" ←ₐ ??₀⟨"%149"⟩;
    ⟨"data"⟩[6] ←ᵢ ⟨"%150"⟩;
    "%151" ←ₐ .Sub ⟨"%20"⟩ ⟨"%12"⟩;
    "%152" ←ₐ ??₀⟨"%151"⟩;
    ⟨"data"⟩[7] ←ᵢ ⟨"%152"⟩;
    "%153" ←ₐ .Sub ⟨"%20"⟩ ⟨"%11"⟩;
    "%154" ←ₐ ??₀⟨"%153"⟩;
    ⟨"data"⟩[8] ←ᵢ ⟨"%154"⟩;
    "%155" ←ₐ .Sub ⟨"%20"⟩ ⟨"%10"⟩;
    "%156" ←ₐ ??₀⟨"%155"⟩;
    ⟨"data"⟩[9] ←ᵢ ⟨"%156"⟩;
    "%157" ←ₐ .Sub ⟨"%20"⟩ ⟨"%9"⟩;
    "%158" ←ₐ ??₀⟨"%157"⟩;
    ⟨"data"⟩[10] ←ᵢ ⟨"%158"⟩;
    "%159" ←ₐ .Sub ⟨"%20"⟩ ⟨"%8"⟩;
    "%160" ←ₐ ??₀⟨"%159"⟩;
    ⟨"data"⟩[11] ←ᵢ ⟨"%160"⟩;
    "%161" ←ₐ .Sub ⟨"%20"⟩ ⟨"%7"⟩;
    "%162" ←ₐ ??₀⟨"%161"⟩;
    ⟨"data"⟩[12] ←ᵢ ⟨"%162"⟩;
    "%163" ←ₐ .Sub ⟨"%20"⟩ ⟨"%6"⟩;
    "%164" ←ₐ ??₀⟨"%163"⟩;
    ⟨"data"⟩[13] ←ᵢ ⟨"%164"⟩;
    "%165" ←ₐ .Sub ⟨"%20"⟩ ⟨"%5"⟩;
    "%166" ←ₐ ??₀⟨"%165"⟩;
    ⟨"data"⟩[14] ←ᵢ ⟨"%166"⟩;
    "%167" ←ₐ .Sub ⟨"%20"⟩ ⟨"%4"⟩;
    "%168" ←ₐ ??₀⟨"%167"⟩;
    ⟨"data"⟩[15] ←ᵢ ⟨"%168"⟩;
    "%169" ←ₐ .Sub ⟨"%20"⟩ ⟨"%3"⟩;
    "%170" ←ₐ ??₀⟨"%169"⟩;
    ⟨"data"⟩[16] ←ᵢ ⟨"%170"⟩;
    "%171" ←ₐ .Sub ⟨"%20"⟩ ⟨"%2"⟩;
    "%172" ←ₐ ??₀⟨"%171"⟩;
    ⟨"data"⟩[17] ←ᵢ ⟨"%172"⟩;
    "%173" ←ₐ .Sub ⟨"%20"⟩ ⟨"%1"⟩;
    "%174" ←ₐ ??₀⟨"%173"⟩;
    ⟨"data"⟩[18] ←ᵢ ⟨"%174"⟩;
    "%175" ←ₐ .Sub ⟨"%20"⟩ ⟨"%0"⟩;
    "%176" ←ₐ ??₀⟨"%175"⟩;
    ⟨"data"⟩[19] ←ᵢ ⟨"%176"⟩
  );
  "%21" ←ₐ .Get ⟨"data"⟩ 0 1;
  "%22" ←ₐ .Get ⟨"data"⟩ 0 2;
  "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%17"⟩;
  "%24" ←ₐ .Add ⟨"%21"⟩ ⟨"%23"⟩;
  "%25" ←ₐ .Get ⟨"data"⟩ 0 3;
  "%26" ←ₐ .Mul ⟨"%25"⟩ ⟨"%16"⟩;
  "%27" ←ₐ .Add ⟨"%24"⟩ ⟨"%26"⟩;
  "%28" ←ₐ .Get ⟨"data"⟩ 0 4;
  "%29" ←ₐ .Mul ⟨"%28"⟩ ⟨"%15"⟩;
  "%30" ←ₐ .Add ⟨"%27"⟩ ⟨"%29"⟩;
  "%31" ←ₐ .Get ⟨"data"⟩ 0 5;
  "%32" ←ₐ .Mul ⟨"%31"⟩ ⟨"%14"⟩;
  "%33" ←ₐ .Add ⟨"%30"⟩ ⟨"%32"⟩;
  "%34" ←ₐ .Get ⟨"data"⟩ 0 6;
  "%35" ←ₐ .Mul ⟨"%34"⟩ ⟨"%13"⟩;
  "%36" ←ₐ .Add ⟨"%33"⟩ ⟨"%35"⟩;
  "%37" ←ₐ .Get ⟨"data"⟩ 0 7;
  "%38" ←ₐ .Mul ⟨"%37"⟩ ⟨"%12"⟩;
  "%39" ←ₐ .Add ⟨"%36"⟩ ⟨"%38"⟩;
  "%40" ←ₐ .Get ⟨"data"⟩ 0 8;
  "%41" ←ₐ .Mul ⟨"%40"⟩ ⟨"%11"⟩;
  "%42" ←ₐ .Add ⟨"%39"⟩ ⟨"%41"⟩;
  "%43" ←ₐ .Get ⟨"data"⟩ 0 9;
  "%44" ←ₐ .Mul ⟨"%43"⟩ ⟨"%10"⟩;
  "%45" ←ₐ .Add ⟨"%42"⟩ ⟨"%44"⟩;
  "%46" ←ₐ .Get ⟨"data"⟩ 0 10;
  "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%9"⟩;
  "%48" ←ₐ .Add ⟨"%45"⟩ ⟨"%47"⟩;
  "%49" ←ₐ .Get ⟨"data"⟩ 0 11;
  "%50" ←ₐ .Mul ⟨"%49"⟩ ⟨"%8"⟩;
  "%51" ←ₐ .Add ⟨"%48"⟩ ⟨"%50"⟩;
  "%52" ←ₐ .Get ⟨"data"⟩ 0 12;
  "%53" ←ₐ .Mul ⟨"%52"⟩ ⟨"%7"⟩;
  "%54" ←ₐ .Add ⟨"%51"⟩ ⟨"%53"⟩;
  "%55" ←ₐ .Get ⟨"data"⟩ 0 13;
  "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%6"⟩;
  "%57" ←ₐ .Add ⟨"%54"⟩ ⟨"%56"⟩;
  "%58" ←ₐ .Get ⟨"data"⟩ 0 14;
  "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%5"⟩;
  "%60" ←ₐ .Add ⟨"%57"⟩ ⟨"%59"⟩;
  "%61" ←ₐ .Get ⟨"data"⟩ 0 15;
  "%62" ←ₐ .Mul ⟨"%61"⟩ ⟨"%4"⟩;
  "%63" ←ₐ .Add ⟨"%60"⟩ ⟨"%62"⟩;
  "%64" ←ₐ .Get ⟨"data"⟩ 0 16;
  "%65" ←ₐ .Mul ⟨"%64"⟩ ⟨"%3"⟩;
  "%66" ←ₐ .Add ⟨"%63"⟩ ⟨"%65"⟩;
  "%67" ←ₐ .Get ⟨"data"⟩ 0 17;
  "%68" ←ₐ .Mul ⟨"%67"⟩ ⟨"%2"⟩;
  "%69" ←ₐ .Add ⟨"%66"⟩ ⟨"%68"⟩;
  "%70" ←ₐ .Get ⟨"data"⟩ 0 18;
  "%71" ←ₐ .Mul ⟨"%70"⟩ ⟨"%1"⟩;
  "%72" ←ₐ .Add ⟨"%69"⟩ ⟨"%71"⟩;
  "%73" ←ₐ .Get ⟨"data"⟩ 0 19;
  "%74" ←ₐ .Mul ⟨"%73"⟩ ⟨"%0"⟩;
  "%75" ←ₐ .Add ⟨"%72"⟩ ⟨"%74"⟩;
  "%76" ←ₐ .Sub ⟨"%75"⟩ ⟨"%20"⟩;
  ?₀ ⟨"%76"⟩;
  "%77" ←ₐ .Get ⟨"data"⟩ 0 0;
  "%78" ←ₐ .Sub ⟨"%18"⟩ ⟨"%77"⟩;
  "%79" ←ₐ .Mul ⟨"%77"⟩ ⟨"%78"⟩;
  ?₀ ⟨"%79"⟩;
  "%80" ←ₐ .Sub ⟨"%18"⟩ ⟨"%21"⟩;
  "%81" ←ₐ .Mul ⟨"%21"⟩ ⟨"%80"⟩;
  ?₀ ⟨"%81"⟩;
  "%82" ←ₐ .Add ⟨"%77"⟩ ⟨"%21"⟩;
  "%83" ←ₐ .Sub ⟨"%18"⟩ ⟨"%22"⟩;
  "%84" ←ₐ .Mul ⟨"%22"⟩ ⟨"%83"⟩;
  ?₀ ⟨"%84"⟩;
  "%85" ←ₐ .Add ⟨"%82"⟩ ⟨"%22"⟩;
  "%86" ←ₐ .Sub ⟨"%18"⟩ ⟨"%25"⟩;
  "%87" ←ₐ .Mul ⟨"%25"⟩ ⟨"%86"⟩;
  ?₀ ⟨"%87"⟩;
  "%88" ←ₐ .Add ⟨"%85"⟩ ⟨"%25"⟩;
  "%89" ←ₐ .Sub ⟨"%18"⟩ ⟨"%28"⟩;
  "%90" ←ₐ .Mul ⟨"%28"⟩ ⟨"%89"⟩;
  ?₀ ⟨"%90"⟩;
  "%91" ←ₐ .Add ⟨"%88"⟩ ⟨"%28"⟩;
  "%92" ←ₐ .Sub ⟨"%18"⟩ ⟨"%31"⟩;
  "%93" ←ₐ .Mul ⟨"%31"⟩ ⟨"%92"⟩;
  ?₀ ⟨"%93"⟩;
  "%94" ←ₐ .Add ⟨"%91"⟩ ⟨"%31"⟩;
  "%95" ←ₐ .Sub ⟨"%18"⟩ ⟨"%34"⟩;
  "%96" ←ₐ .Mul ⟨"%34"⟩ ⟨"%95"⟩;
  ?₀ ⟨"%96"⟩;
  "%97" ←ₐ .Add ⟨"%94"⟩ ⟨"%34"⟩;
  "%98" ←ₐ .Sub ⟨"%18"⟩ ⟨"%37"⟩;
  "%99" ←ₐ .Mul ⟨"%37"⟩ ⟨"%98"⟩;
  ?₀ ⟨"%99"⟩;
  "%100" ←ₐ .Add ⟨"%97"⟩ ⟨"%37"⟩;
  "%101" ←ₐ .Sub ⟨"%18"⟩ ⟨"%40"⟩;
  "%102" ←ₐ .Mul ⟨"%40"⟩ ⟨"%101"⟩;
  ?₀ ⟨"%102"⟩;
  "%103" ←ₐ .Add ⟨"%100"⟩ ⟨"%40"⟩;
  "%104" ←ₐ .Sub ⟨"%18"⟩ ⟨"%43"⟩;
  "%105" ←ₐ .Mul ⟨"%43"⟩ ⟨"%104"⟩;
  ?₀ ⟨"%105"⟩;
  "%106" ←ₐ .Add ⟨"%103"⟩ ⟨"%43"⟩;
  "%107" ←ₐ .Sub ⟨"%18"⟩ ⟨"%46"⟩;
  "%108" ←ₐ .Mul ⟨"%46"⟩ ⟨"%107"⟩;
  ?₀ ⟨"%108"⟩;
  "%109" ←ₐ .Add ⟨"%106"⟩ ⟨"%46"⟩;
  "%110" ←ₐ .Sub ⟨"%18"⟩ ⟨"%49"⟩;
  "%111" ←ₐ .Mul ⟨"%49"⟩ ⟨"%110"⟩;
  ?₀ ⟨"%111"⟩;
  "%112" ←ₐ .Add ⟨"%109"⟩ ⟨"%49"⟩;
  "%113" ←ₐ .Sub ⟨"%18"⟩ ⟨"%52"⟩;
  "%114" ←ₐ .Mul ⟨"%52"⟩ ⟨"%113"⟩;
  ?₀ ⟨"%114"⟩;
  "%115" ←ₐ .Add ⟨"%112"⟩ ⟨"%52"⟩;
  "%116" ←ₐ .Sub ⟨"%18"⟩ ⟨"%55"⟩;
  "%117" ←ₐ .Mul ⟨"%55"⟩ ⟨"%116"⟩;
  ?₀ ⟨"%117"⟩;
  "%118" ←ₐ .Add ⟨"%115"⟩ ⟨"%55"⟩;
  "%119" ←ₐ .Sub ⟨"%18"⟩ ⟨"%58"⟩;
  "%120" ←ₐ .Mul ⟨"%58"⟩ ⟨"%119"⟩;
  ?₀ ⟨"%120"⟩;
  "%121" ←ₐ .Add ⟨"%118"⟩ ⟨"%58"⟩;
  "%122" ←ₐ .Sub ⟨"%18"⟩ ⟨"%61"⟩;
  "%123" ←ₐ .Mul ⟨"%61"⟩ ⟨"%122"⟩;
  ?₀ ⟨"%123"⟩;
  "%124" ←ₐ .Add ⟨"%121"⟩ ⟨"%61"⟩;
  "%125" ←ₐ .Sub ⟨"%18"⟩ ⟨"%64"⟩;
  "%126" ←ₐ .Mul ⟨"%64"⟩ ⟨"%125"⟩;
  ?₀ ⟨"%126"⟩;
  "%127" ←ₐ .Add ⟨"%124"⟩ ⟨"%64"⟩;
  "%128" ←ₐ .Sub ⟨"%18"⟩ ⟨"%67"⟩;
  "%129" ←ₐ .Mul ⟨"%67"⟩ ⟨"%128"⟩;
  ?₀ ⟨"%129"⟩;
  "%130" ←ₐ .Add ⟨"%127"⟩ ⟨"%67"⟩;
  "%131" ←ₐ .Sub ⟨"%18"⟩ ⟨"%70"⟩;
  "%132" ←ₐ .Mul ⟨"%70"⟩ ⟨"%131"⟩;
  ?₀ ⟨"%132"⟩;
  "%133" ←ₐ .Add ⟨"%130"⟩ ⟨"%70"⟩;
  "%134" ←ₐ .Sub ⟨"%18"⟩ ⟨"%73"⟩;
  "%135" ←ₐ .Mul ⟨"%73"⟩ ⟨"%134"⟩;
  ?₀ ⟨"%135"⟩;
  "%136" ←ₐ .Add ⟨"%133"⟩ ⟨"%73"⟩;
  "%137" ←ₐ .Sub ⟨"%136"⟩ ⟨"%18"⟩;
  ?₀ ⟨"%137"⟩
def getReturn (st: State) : BufferAtTime :=
  st.buffers ⟨"data"⟩ |>.get!.getLast!
def run (st: State) : BufferAtTime :=
  getReturn (full.runProgram st)
def part0 : MLIRProgram :=
  "%0" ←ₐ .Const 19;
  "%1" ←ₐ .Const 18;
  "%2" ←ₐ .Const 17;
  "%3" ←ₐ .Const 16
def part1 : MLIRProgram :=
  "%4" ←ₐ .Const 15;
  "%5" ←ₐ .Const 14;
  "%6" ←ₐ .Const 13;
  "%7" ←ₐ .Const 12
def part2 : MLIRProgram :=
  "%8" ←ₐ .Const 11;
  "%9" ←ₐ .Const 10;
  "%10" ←ₐ .Const 9;
  "%11" ←ₐ .Const 8
def part3 : MLIRProgram :=
  "%12" ←ₐ .Const 7;
  "%13" ←ₐ .Const 6;
  "%14" ←ₐ .Const 5;
  "%15" ←ₐ .Const 4
def part4 : MLIRProgram :=
  "%16" ←ₐ .Const 3;
  "%17" ←ₐ .Const 2;
  "%18" ←ₐ .Const 1;
  "%19" ←ₐ .Const 0
def part5 : MLIRProgram :=
  "%20" ←ₐ .Get ⟨"code"⟩ 0 0;
  nondet (
    "%138" ←ₐ ??₀⟨"%20"⟩;
    ⟨"data"⟩[0] ←ᵢ ⟨"%138"⟩;
    "%139" ←ₐ .Sub ⟨"%20"⟩ ⟨"%18"⟩
  )
def part6 : MLIRProgram :=
  nondet (
    "%140" ←ₐ ??₀⟨"%139"⟩;
    ⟨"data"⟩[1] ←ᵢ ⟨"%140"⟩;
    "%141" ←ₐ .Sub ⟨"%20"⟩ ⟨"%17"⟩;
    "%142" ←ₐ ??₀⟨"%141"⟩
  )
def part7 : MLIRProgram :=
  nondet (
    ⟨"data"⟩[2] ←ᵢ ⟨"%142"⟩;
    "%143" ←ₐ .Sub ⟨"%20"⟩ ⟨"%16"⟩;
    "%144" ←ₐ ??₀⟨"%143"⟩;
    ⟨"data"⟩[3] ←ᵢ ⟨"%144"⟩
  )
def part8 : MLIRProgram :=
  nondet (
    "%145" ←ₐ .Sub ⟨"%20"⟩ ⟨"%15"⟩;
    "%146" ←ₐ ??₀⟨"%145"⟩;
    ⟨"data"⟩[4] ←ᵢ ⟨"%146"⟩;
    "%147" ←ₐ .Sub ⟨"%20"⟩ ⟨"%14"⟩
  )
def part9 : MLIRProgram :=
  nondet (
    "%148" ←ₐ ??₀⟨"%147"⟩;
    ⟨"data"⟩[5] ←ᵢ ⟨"%148"⟩;
    "%149" ←ₐ .Sub ⟨"%20"⟩ ⟨"%13"⟩;
    "%150" ←ₐ ??₀⟨"%149"⟩
  )
def part10 : MLIRProgram :=
  nondet (
    ⟨"data"⟩[6] ←ᵢ ⟨"%150"⟩;
    "%151" ←ₐ .Sub ⟨"%20"⟩ ⟨"%12"⟩;
    "%152" ←ₐ ??₀⟨"%151"⟩;
    ⟨"data"⟩[7] ←ᵢ ⟨"%152"⟩
  )
def part11 : MLIRProgram :=
  nondet (
    "%153" ←ₐ .Sub ⟨"%20"⟩ ⟨"%11"⟩;
    "%154" ←ₐ ??₀⟨"%153"⟩;
    ⟨"data"⟩[8] ←ᵢ ⟨"%154"⟩;
    "%155" ←ₐ .Sub ⟨"%20"⟩ ⟨"%10"⟩
  )
def part12 : MLIRProgram :=
  nondet (
    "%156" ←ₐ ??₀⟨"%155"⟩;
    ⟨"data"⟩[9] ←ᵢ ⟨"%156"⟩;
    "%157" ←ₐ .Sub ⟨"%20"⟩ ⟨"%9"⟩;
    "%158" ←ₐ ??₀⟨"%157"⟩
  )
def part13 : MLIRProgram :=
  nondet (
    ⟨"data"⟩[10] ←ᵢ ⟨"%158"⟩;
    "%159" ←ₐ .Sub ⟨"%20"⟩ ⟨"%8"⟩;
    "%160" ←ₐ ??₀⟨"%159"⟩;
    ⟨"data"⟩[11] ←ᵢ ⟨"%160"⟩
  )
def part14 : MLIRProgram :=
  nondet (
    "%161" ←ₐ .Sub ⟨"%20"⟩ ⟨"%7"⟩;
    "%162" ←ₐ ??₀⟨"%161"⟩;
    ⟨"data"⟩[12] ←ᵢ ⟨"%162"⟩;
    "%163" ←ₐ .Sub ⟨"%20"⟩ ⟨"%6"⟩
  )
def part15 : MLIRProgram :=
  nondet (
    "%164" ←ₐ ??₀⟨"%163"⟩;
    ⟨"data"⟩[13] ←ᵢ ⟨"%164"⟩;
    "%165" ←ₐ .Sub ⟨"%20"⟩ ⟨"%5"⟩;
    "%166" ←ₐ ??₀⟨"%165"⟩
  )
def part16 : MLIRProgram :=
  nondet (
    ⟨"data"⟩[14] ←ᵢ ⟨"%166"⟩;
    "%167" ←ₐ .Sub ⟨"%20"⟩ ⟨"%4"⟩;
    "%168" ←ₐ ??₀⟨"%167"⟩;
    ⟨"data"⟩[15] ←ᵢ ⟨"%168"⟩
  )
def part17 : MLIRProgram :=
  nondet (
    "%169" ←ₐ .Sub ⟨"%20"⟩ ⟨"%3"⟩;
    "%170" ←ₐ ??₀⟨"%169"⟩;
    ⟨"data"⟩[16] ←ᵢ ⟨"%170"⟩;
    "%171" ←ₐ .Sub ⟨"%20"⟩ ⟨"%2"⟩
  )
def part18 : MLIRProgram :=
  nondet (
    "%172" ←ₐ ??₀⟨"%171"⟩;
    ⟨"data"⟩[17] ←ᵢ ⟨"%172"⟩;
    "%173" ←ₐ .Sub ⟨"%20"⟩ ⟨"%1"⟩;
    "%174" ←ₐ ??₀⟨"%173"⟩
  )
def part19 : MLIRProgram :=
  nondet (
    ⟨"data"⟩[18] ←ᵢ ⟨"%174"⟩;
    "%175" ←ₐ .Sub ⟨"%20"⟩ ⟨"%0"⟩;
    "%176" ←ₐ ??₀⟨"%175"⟩;
    ⟨"data"⟩[19] ←ᵢ ⟨"%176"⟩
  )
def part20 : MLIRProgram :=
  "%21" ←ₐ .Get ⟨"data"⟩ 0 1;
  "%22" ←ₐ .Get ⟨"data"⟩ 0 2;
  "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%17"⟩;
  "%24" ←ₐ .Add ⟨"%21"⟩ ⟨"%23"⟩
def part21 : MLIRProgram :=
  "%25" ←ₐ .Get ⟨"data"⟩ 0 3;
  "%26" ←ₐ .Mul ⟨"%25"⟩ ⟨"%16"⟩;
  "%27" ←ₐ .Add ⟨"%24"⟩ ⟨"%26"⟩;
  "%28" ←ₐ .Get ⟨"data"⟩ 0 4
def part22 : MLIRProgram :=
  "%29" ←ₐ .Mul ⟨"%28"⟩ ⟨"%15"⟩;
  "%30" ←ₐ .Add ⟨"%27"⟩ ⟨"%29"⟩;
  "%31" ←ₐ .Get ⟨"data"⟩ 0 5;
  "%32" ←ₐ .Mul ⟨"%31"⟩ ⟨"%14"⟩
def part23 : MLIRProgram :=
  "%33" ←ₐ .Add ⟨"%30"⟩ ⟨"%32"⟩;
  "%34" ←ₐ .Get ⟨"data"⟩ 0 6;
  "%35" ←ₐ .Mul ⟨"%34"⟩ ⟨"%13"⟩;
  "%36" ←ₐ .Add ⟨"%33"⟩ ⟨"%35"⟩
def part24 : MLIRProgram :=
  "%37" ←ₐ .Get ⟨"data"⟩ 0 7;
  "%38" ←ₐ .Mul ⟨"%37"⟩ ⟨"%12"⟩;
  "%39" ←ₐ .Add ⟨"%36"⟩ ⟨"%38"⟩;
  "%40" ←ₐ .Get ⟨"data"⟩ 0 8
def part25 : MLIRProgram :=
  "%41" ←ₐ .Mul ⟨"%40"⟩ ⟨"%11"⟩;
  "%42" ←ₐ .Add ⟨"%39"⟩ ⟨"%41"⟩;
  "%43" ←ₐ .Get ⟨"data"⟩ 0 9;
  "%44" ←ₐ .Mul ⟨"%43"⟩ ⟨"%10"⟩
def part26 : MLIRProgram :=
  "%45" ←ₐ .Add ⟨"%42"⟩ ⟨"%44"⟩;
  "%46" ←ₐ .Get ⟨"data"⟩ 0 10;
  "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%9"⟩;
  "%48" ←ₐ .Add ⟨"%45"⟩ ⟨"%47"⟩
def part27 : MLIRProgram :=
  "%49" ←ₐ .Get ⟨"data"⟩ 0 11;
  "%50" ←ₐ .Mul ⟨"%49"⟩ ⟨"%8"⟩;
  "%51" ←ₐ .Add ⟨"%48"⟩ ⟨"%50"⟩;
  "%52" ←ₐ .Get ⟨"data"⟩ 0 12
def part28 : MLIRProgram :=
  "%53" ←ₐ .Mul ⟨"%52"⟩ ⟨"%7"⟩;
  "%54" ←ₐ .Add ⟨"%51"⟩ ⟨"%53"⟩;
  "%55" ←ₐ .Get ⟨"data"⟩ 0 13;
  "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%6"⟩
def part29 : MLIRProgram :=
  "%57" ←ₐ .Add ⟨"%54"⟩ ⟨"%56"⟩;
  "%58" ←ₐ .Get ⟨"data"⟩ 0 14;
  "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%5"⟩;
  "%60" ←ₐ .Add ⟨"%57"⟩ ⟨"%59"⟩
def part30 : MLIRProgram :=
  "%61" ←ₐ .Get ⟨"data"⟩ 0 15;
  "%62" ←ₐ .Mul ⟨"%61"⟩ ⟨"%4"⟩;
  "%63" ←ₐ .Add ⟨"%60"⟩ ⟨"%62"⟩;
  "%64" ←ₐ .Get ⟨"data"⟩ 0 16
def part31 : MLIRProgram :=
  "%65" ←ₐ .Mul ⟨"%64"⟩ ⟨"%3"⟩;
  "%66" ←ₐ .Add ⟨"%63"⟩ ⟨"%65"⟩;
  "%67" ←ₐ .Get ⟨"data"⟩ 0 17;
  "%68" ←ₐ .Mul ⟨"%67"⟩ ⟨"%2"⟩
def part32 : MLIRProgram :=
  "%69" ←ₐ .Add ⟨"%66"⟩ ⟨"%68"⟩;
  "%70" ←ₐ .Get ⟨"data"⟩ 0 18;
  "%71" ←ₐ .Mul ⟨"%70"⟩ ⟨"%1"⟩;
  "%72" ←ₐ .Add ⟨"%69"⟩ ⟨"%71"⟩
def part33 : MLIRProgram :=
  "%73" ←ₐ .Get ⟨"data"⟩ 0 19;
  "%74" ←ₐ .Mul ⟨"%73"⟩ ⟨"%0"⟩;
  "%75" ←ₐ .Add ⟨"%72"⟩ ⟨"%74"⟩;
  "%76" ←ₐ .Sub ⟨"%75"⟩ ⟨"%20"⟩
def part34 : MLIRProgram :=
  ?₀ ⟨"%76"⟩;
  "%77" ←ₐ .Get ⟨"data"⟩ 0 0;
  "%78" ←ₐ .Sub ⟨"%18"⟩ ⟨"%77"⟩;
  "%79" ←ₐ .Mul ⟨"%77"⟩ ⟨"%78"⟩
def part35 : MLIRProgram :=
  ?₀ ⟨"%79"⟩;
  "%80" ←ₐ .Sub ⟨"%18"⟩ ⟨"%21"⟩;
  "%81" ←ₐ .Mul ⟨"%21"⟩ ⟨"%80"⟩;
  ?₀ ⟨"%81"⟩
def part36 : MLIRProgram :=
  "%82" ←ₐ .Add ⟨"%77"⟩ ⟨"%21"⟩;
  "%83" ←ₐ .Sub ⟨"%18"⟩ ⟨"%22"⟩;
  "%84" ←ₐ .Mul ⟨"%22"⟩ ⟨"%83"⟩;
  ?₀ ⟨"%84"⟩
def part37 : MLIRProgram :=
  "%85" ←ₐ .Add ⟨"%82"⟩ ⟨"%22"⟩;
  "%86" ←ₐ .Sub ⟨"%18"⟩ ⟨"%25"⟩;
  "%87" ←ₐ .Mul ⟨"%25"⟩ ⟨"%86"⟩;
  ?₀ ⟨"%87"⟩
def part38 : MLIRProgram :=
  "%88" ←ₐ .Add ⟨"%85"⟩ ⟨"%25"⟩;
  "%89" ←ₐ .Sub ⟨"%18"⟩ ⟨"%28"⟩;
  "%90" ←ₐ .Mul ⟨"%28"⟩ ⟨"%89"⟩;
  ?₀ ⟨"%90"⟩
def part39 : MLIRProgram :=
  "%91" ←ₐ .Add ⟨"%88"⟩ ⟨"%28"⟩;
  "%92" ←ₐ .Sub ⟨"%18"⟩ ⟨"%31"⟩;
  "%93" ←ₐ .Mul ⟨"%31"⟩ ⟨"%92"⟩;
  ?₀ ⟨"%93"⟩
def part40 : MLIRProgram :=
  "%94" ←ₐ .Add ⟨"%91"⟩ ⟨"%31"⟩;
  "%95" ←ₐ .Sub ⟨"%18"⟩ ⟨"%34"⟩;
  "%96" ←ₐ .Mul ⟨"%34"⟩ ⟨"%95"⟩;
  ?₀ ⟨"%96"⟩
def part41 : MLIRProgram :=
  "%97" ←ₐ .Add ⟨"%94"⟩ ⟨"%34"⟩;
  "%98" ←ₐ .Sub ⟨"%18"⟩ ⟨"%37"⟩;
  "%99" ←ₐ .Mul ⟨"%37"⟩ ⟨"%98"⟩;
  ?₀ ⟨"%99"⟩
def part42 : MLIRProgram :=
  "%100" ←ₐ .Add ⟨"%97"⟩ ⟨"%37"⟩;
  "%101" ←ₐ .Sub ⟨"%18"⟩ ⟨"%40"⟩;
  "%102" ←ₐ .Mul ⟨"%40"⟩ ⟨"%101"⟩;
  ?₀ ⟨"%102"⟩
def part43 : MLIRProgram :=
  "%103" ←ₐ .Add ⟨"%100"⟩ ⟨"%40"⟩;
  "%104" ←ₐ .Sub ⟨"%18"⟩ ⟨"%43"⟩;
  "%105" ←ₐ .Mul ⟨"%43"⟩ ⟨"%104"⟩;
  ?₀ ⟨"%105"⟩
def part44 : MLIRProgram :=
  "%106" ←ₐ .Add ⟨"%103"⟩ ⟨"%43"⟩;
  "%107" ←ₐ .Sub ⟨"%18"⟩ ⟨"%46"⟩;
  "%108" ←ₐ .Mul ⟨"%46"⟩ ⟨"%107"⟩;
  ?₀ ⟨"%108"⟩
def part45 : MLIRProgram :=
  "%109" ←ₐ .Add ⟨"%106"⟩ ⟨"%46"⟩;
  "%110" ←ₐ .Sub ⟨"%18"⟩ ⟨"%49"⟩;
  "%111" ←ₐ .Mul ⟨"%49"⟩ ⟨"%110"⟩;
  ?₀ ⟨"%111"⟩
def part46 : MLIRProgram :=
  "%112" ←ₐ .Add ⟨"%109"⟩ ⟨"%49"⟩;
  "%113" ←ₐ .Sub ⟨"%18"⟩ ⟨"%52"⟩;
  "%114" ←ₐ .Mul ⟨"%52"⟩ ⟨"%113"⟩;
  ?₀ ⟨"%114"⟩
def part47 : MLIRProgram :=
  "%115" ←ₐ .Add ⟨"%112"⟩ ⟨"%52"⟩;
  "%116" ←ₐ .Sub ⟨"%18"⟩ ⟨"%55"⟩;
  "%117" ←ₐ .Mul ⟨"%55"⟩ ⟨"%116"⟩;
  ?₀ ⟨"%117"⟩
def part48 : MLIRProgram :=
  "%118" ←ₐ .Add ⟨"%115"⟩ ⟨"%55"⟩;
  "%119" ←ₐ .Sub ⟨"%18"⟩ ⟨"%58"⟩;
  "%120" ←ₐ .Mul ⟨"%58"⟩ ⟨"%119"⟩;
  ?₀ ⟨"%120"⟩
def part49 : MLIRProgram :=
  "%121" ←ₐ .Add ⟨"%118"⟩ ⟨"%58"⟩;
  "%122" ←ₐ .Sub ⟨"%18"⟩ ⟨"%61"⟩;
  "%123" ←ₐ .Mul ⟨"%61"⟩ ⟨"%122"⟩;
  ?₀ ⟨"%123"⟩
def part50 : MLIRProgram :=
  "%124" ←ₐ .Add ⟨"%121"⟩ ⟨"%61"⟩;
  "%125" ←ₐ .Sub ⟨"%18"⟩ ⟨"%64"⟩;
  "%126" ←ₐ .Mul ⟨"%64"⟩ ⟨"%125"⟩;
  ?₀ ⟨"%126"⟩
def part51 : MLIRProgram :=
  "%127" ←ₐ .Add ⟨"%124"⟩ ⟨"%64"⟩;
  "%128" ←ₐ .Sub ⟨"%18"⟩ ⟨"%67"⟩;
  "%129" ←ₐ .Mul ⟨"%67"⟩ ⟨"%128"⟩;
  ?₀ ⟨"%129"⟩
def part52 : MLIRProgram :=
  "%130" ←ₐ .Add ⟨"%127"⟩ ⟨"%67"⟩;
  "%131" ←ₐ .Sub ⟨"%18"⟩ ⟨"%70"⟩;
  "%132" ←ₐ .Mul ⟨"%70"⟩ ⟨"%131"⟩;
  ?₀ ⟨"%132"⟩
def part53 : MLIRProgram :=
  "%133" ←ₐ .Add ⟨"%130"⟩ ⟨"%70"⟩;
  "%134" ←ₐ .Sub ⟨"%18"⟩ ⟨"%73"⟩;
  "%135" ←ₐ .Mul ⟨"%73"⟩ ⟨"%134"⟩;
  ?₀ ⟨"%135"⟩
def part54 : MLIRProgram :=
  "%136" ←ₐ .Add ⟨"%133"⟩ ⟨"%73"⟩;
  "%137" ←ₐ .Sub ⟨"%136"⟩ ⟨"%18"⟩;
  ?₀ ⟨"%137"⟩

abbrev parts_combined : MLIRProgram :=
  part0; part1; part2; part3; part4; part5; part6; part7; part8; part9; part10; part11; part12; part13; part14; part15; part16; part17; part18; part19; part20; part21; part22; part23; part24; part25; part26; part27; part28; part29; part30; part31; part32; part33; part34; part35; part36; part37; part38; part39; part40; part41; part42; part43; part44; part45; part46; part47; part48; part49; part50; part51; part52; part53; part54
lemma parts_combine {st: State} :
  Γ st ⟦parts_combined⟧ =
  Γ st ⟦full⟧ := by
  unfold full parts_combined
  unfold part0
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part1
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part2
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part3
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part4
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part5
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part6
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part7
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part8
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part9
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part10
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part11
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part12
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part13
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part14
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part15
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part16
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part17
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part18
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_step_eq
  intro st
  unfold part19
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.nondet_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part20
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part21
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part22
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part23
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part24
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part25
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part26
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part27
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part28
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part29
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part30
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part31
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part32
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part33
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part34
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part35
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part36
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part37
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part38
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part39
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part40
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part41
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part42
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part43
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part44
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part45
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part46
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part47
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part48
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part49
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part50
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part51
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part52
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part53
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.nested_seq_step_eq
  intro st
  apply MLIR.seq_step_eq
  intro st
  unfold part54
  rfl

end Risc0.OneHot20.Witness.Code
