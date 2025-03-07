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
def getReturn (st: State) (res_data: BufferAtTime) : Prop :=
  ((st.buffers ⟨"data"⟩ |>.get!.getLast!) = res_data)
∧ ¬ st.isFailed
def run (st: State) (res_data: BufferAtTime): Prop :=
  getReturn (full.runProgram st) res_data

end Code

def start_state (input_code: BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨"code"⟩, [input_code]), (⟨"data"⟩, [[.none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none, .none]])]
  , felts := Map.empty
  , props := Map.empty
  , isFailed := false
  , bufferWidths := Map.fromList [(⟨"code"⟩, 1), (⟨"data"⟩, 20)]
  , cycle := 0
  , vars := [⟨"code"⟩, ⟨"data"⟩]
  }

end Risc0.OneHot20.Witness
