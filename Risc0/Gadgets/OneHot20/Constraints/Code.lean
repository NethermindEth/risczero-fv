import Risc0.Basic
import Risc0.Lemmas

namespace Risc0.OneHot20.Constraints.Code

open MLIRNotation

def full : MLIRProgram :=
  "%0" ←ₐ .Const 1;
  "%1" ←ₐ .Const 2;
  "%2" ←ₐ .Const 3;
  "%3" ←ₐ .Const 4;
  "%4" ←ₐ .Const 5;
  "%5" ←ₐ .Const 6;
  "%6" ←ₐ .Const 7;
  "%7" ←ₐ .Const 8;
  "%8" ←ₐ .Const 9;
  "%9" ←ₐ .Const 10;
  "%10" ←ₐ .Const 11;
  "%11" ←ₐ .Const 12;
  "%12" ←ₐ .Const 13;
  "%13" ←ₐ .Const 14;
  "%14" ←ₐ .Const 15;
  "%15" ←ₐ .Const 16;
  "%16" ←ₐ .Const 17;
  "%17" ←ₐ .Const 18;
  "%18" ←ₐ .Const 19;
  "%19" ←ₐ ⊤;
  "%20" ←ₐ .Get ⟨"code"⟩ 0 0;
  "%21" ←ₐ .Get ⟨"data"⟩ 0 1;
  "%22" ←ₐ .Get ⟨"data"⟩ 0 2;
  "%23" ←ₐ .Mul ⟨"%22"⟩ ⟨"%1"⟩;
  "%24" ←ₐ .Add ⟨"%21"⟩ ⟨"%23"⟩;
  "%25" ←ₐ .Get ⟨"data"⟩ 0 3;
  "%26" ←ₐ .Mul ⟨"%25"⟩ ⟨"%2"⟩;
  "%27" ←ₐ .Add ⟨"%24"⟩ ⟨"%26"⟩;
  "%28" ←ₐ .Get ⟨"data"⟩ 0 4;
  "%29" ←ₐ .Mul ⟨"%28"⟩ ⟨"%3"⟩;
  "%30" ←ₐ .Add ⟨"%27"⟩ ⟨"%29"⟩;
  "%31" ←ₐ .Get ⟨"data"⟩ 0 5;
  "%32" ←ₐ .Mul ⟨"%31"⟩ ⟨"%4"⟩;
  "%33" ←ₐ .Add ⟨"%30"⟩ ⟨"%32"⟩;
  "%34" ←ₐ .Get ⟨"data"⟩ 0 6;
  "%35" ←ₐ .Mul ⟨"%34"⟩ ⟨"%5"⟩;
  "%36" ←ₐ .Add ⟨"%33"⟩ ⟨"%35"⟩;
  "%37" ←ₐ .Get ⟨"data"⟩ 0 7;
  "%38" ←ₐ .Mul ⟨"%37"⟩ ⟨"%6"⟩;
  "%39" ←ₐ .Add ⟨"%36"⟩ ⟨"%38"⟩;
  "%40" ←ₐ .Get ⟨"data"⟩ 0 8;
  "%41" ←ₐ .Mul ⟨"%40"⟩ ⟨"%7"⟩;
  "%42" ←ₐ .Add ⟨"%39"⟩ ⟨"%41"⟩;
  "%43" ←ₐ .Get ⟨"data"⟩ 0 9;
  "%44" ←ₐ .Mul ⟨"%43"⟩ ⟨"%8"⟩;
  "%45" ←ₐ .Add ⟨"%42"⟩ ⟨"%44"⟩;
  "%46" ←ₐ .Get ⟨"data"⟩ 0 10;
  "%47" ←ₐ .Mul ⟨"%46"⟩ ⟨"%9"⟩;
  "%48" ←ₐ .Add ⟨"%45"⟩ ⟨"%47"⟩;
  "%49" ←ₐ .Get ⟨"data"⟩ 0 11;
  "%50" ←ₐ .Mul ⟨"%49"⟩ ⟨"%10"⟩;
  "%51" ←ₐ .Add ⟨"%48"⟩ ⟨"%50"⟩;
  "%52" ←ₐ .Get ⟨"data"⟩ 0 12;
  "%53" ←ₐ .Mul ⟨"%52"⟩ ⟨"%11"⟩;
  "%54" ←ₐ .Add ⟨"%51"⟩ ⟨"%53"⟩;
  "%55" ←ₐ .Get ⟨"data"⟩ 0 13;
  "%56" ←ₐ .Mul ⟨"%55"⟩ ⟨"%12"⟩;
  "%57" ←ₐ .Add ⟨"%54"⟩ ⟨"%56"⟩;
  "%58" ←ₐ .Get ⟨"data"⟩ 0 14;
  "%59" ←ₐ .Mul ⟨"%58"⟩ ⟨"%13"⟩;
  "%60" ←ₐ .Add ⟨"%57"⟩ ⟨"%59"⟩;
  "%61" ←ₐ .Get ⟨"data"⟩ 0 15;
  "%62" ←ₐ .Mul ⟨"%61"⟩ ⟨"%14"⟩;
  "%63" ←ₐ .Add ⟨"%60"⟩ ⟨"%62"⟩;
  "%64" ←ₐ .Get ⟨"data"⟩ 0 16;
  "%65" ←ₐ .Mul ⟨"%64"⟩ ⟨"%15"⟩;
  "%66" ←ₐ .Add ⟨"%63"⟩ ⟨"%65"⟩;
  "%67" ←ₐ .Get ⟨"data"⟩ 0 17;
  "%68" ←ₐ .Mul ⟨"%67"⟩ ⟨"%16"⟩;
  "%69" ←ₐ .Add ⟨"%66"⟩ ⟨"%68"⟩;
  "%70" ←ₐ .Get ⟨"data"⟩ 0 18;
  "%71" ←ₐ .Mul ⟨"%70"⟩ ⟨"%17"⟩;
  "%72" ←ₐ .Add ⟨"%69"⟩ ⟨"%71"⟩;
  "%73" ←ₐ .Get ⟨"data"⟩ 0 19;
  "%74" ←ₐ .Mul ⟨"%73"⟩ ⟨"%18"⟩;
  "%75" ←ₐ .Add ⟨"%72"⟩ ⟨"%74"⟩;
  "%76" ←ₐ .Sub ⟨"%75"⟩ ⟨"%20"⟩;
  "%77" ←ₐ ⟨"%19"⟩ &₀ ⟨"%76"⟩;
  "%78" ←ₐ .Get ⟨"data"⟩ 0 0;
  "%79" ←ₐ .Sub ⟨"%0"⟩ ⟨"%78"⟩;
  "%80" ←ₐ .Mul ⟨"%78"⟩ ⟨"%79"⟩;
  "%81" ←ₐ ⟨"%77"⟩ &₀ ⟨"%80"⟩;
  "%82" ←ₐ .Sub ⟨"%0"⟩ ⟨"%21"⟩;
  "%83" ←ₐ .Mul ⟨"%21"⟩ ⟨"%82"⟩;
  "%84" ←ₐ ⟨"%81"⟩ &₀ ⟨"%83"⟩;
  "%85" ←ₐ .Add ⟨"%78"⟩ ⟨"%21"⟩;
  "%86" ←ₐ .Sub ⟨"%0"⟩ ⟨"%22"⟩;
  "%87" ←ₐ .Mul ⟨"%22"⟩ ⟨"%86"⟩;
  "%88" ←ₐ ⟨"%84"⟩ &₀ ⟨"%87"⟩;
  "%89" ←ₐ .Add ⟨"%85"⟩ ⟨"%22"⟩;
  "%90" ←ₐ .Sub ⟨"%0"⟩ ⟨"%25"⟩;
  "%91" ←ₐ .Mul ⟨"%25"⟩ ⟨"%90"⟩;
  "%92" ←ₐ ⟨"%88"⟩ &₀ ⟨"%91"⟩;
  "%93" ←ₐ .Add ⟨"%89"⟩ ⟨"%25"⟩;
  "%94" ←ₐ .Sub ⟨"%0"⟩ ⟨"%28"⟩;
  "%95" ←ₐ .Mul ⟨"%28"⟩ ⟨"%94"⟩;
  "%96" ←ₐ ⟨"%92"⟩ &₀ ⟨"%95"⟩;
  "%97" ←ₐ .Add ⟨"%93"⟩ ⟨"%28"⟩;
  "%98" ←ₐ .Sub ⟨"%0"⟩ ⟨"%31"⟩;
  "%99" ←ₐ .Mul ⟨"%31"⟩ ⟨"%98"⟩;
  "%100" ←ₐ ⟨"%96"⟩ &₀ ⟨"%99"⟩;
  "%101" ←ₐ .Add ⟨"%97"⟩ ⟨"%31"⟩;
  "%102" ←ₐ .Sub ⟨"%0"⟩ ⟨"%34"⟩;
  "%103" ←ₐ .Mul ⟨"%34"⟩ ⟨"%102"⟩;
  "%104" ←ₐ ⟨"%100"⟩ &₀ ⟨"%103"⟩;
  "%105" ←ₐ .Add ⟨"%101"⟩ ⟨"%34"⟩;
  "%106" ←ₐ .Sub ⟨"%0"⟩ ⟨"%37"⟩;
  "%107" ←ₐ .Mul ⟨"%37"⟩ ⟨"%106"⟩;
  "%108" ←ₐ ⟨"%104"⟩ &₀ ⟨"%107"⟩;
  "%109" ←ₐ .Add ⟨"%105"⟩ ⟨"%37"⟩;
  "%110" ←ₐ .Sub ⟨"%0"⟩ ⟨"%40"⟩;
  "%111" ←ₐ .Mul ⟨"%40"⟩ ⟨"%110"⟩;
  "%112" ←ₐ ⟨"%108"⟩ &₀ ⟨"%111"⟩;
  "%113" ←ₐ .Add ⟨"%109"⟩ ⟨"%40"⟩;
  "%114" ←ₐ .Sub ⟨"%0"⟩ ⟨"%43"⟩;
  "%115" ←ₐ .Mul ⟨"%43"⟩ ⟨"%114"⟩;
  "%116" ←ₐ ⟨"%112"⟩ &₀ ⟨"%115"⟩;
  "%117" ←ₐ .Add ⟨"%113"⟩ ⟨"%43"⟩;
  "%118" ←ₐ .Sub ⟨"%0"⟩ ⟨"%46"⟩;
  "%119" ←ₐ .Mul ⟨"%46"⟩ ⟨"%118"⟩;
  "%120" ←ₐ ⟨"%116"⟩ &₀ ⟨"%119"⟩;
  "%121" ←ₐ .Add ⟨"%117"⟩ ⟨"%46"⟩;
  "%122" ←ₐ .Sub ⟨"%0"⟩ ⟨"%49"⟩;
  "%123" ←ₐ .Mul ⟨"%49"⟩ ⟨"%122"⟩;
  "%124" ←ₐ ⟨"%120"⟩ &₀ ⟨"%123"⟩;
  "%125" ←ₐ .Add ⟨"%121"⟩ ⟨"%49"⟩;
  "%126" ←ₐ .Sub ⟨"%0"⟩ ⟨"%52"⟩;
  "%127" ←ₐ .Mul ⟨"%52"⟩ ⟨"%126"⟩;
  "%128" ←ₐ ⟨"%124"⟩ &₀ ⟨"%127"⟩;
  "%129" ←ₐ .Add ⟨"%125"⟩ ⟨"%52"⟩;
  "%130" ←ₐ .Sub ⟨"%0"⟩ ⟨"%55"⟩;
  "%131" ←ₐ .Mul ⟨"%55"⟩ ⟨"%130"⟩;
  "%132" ←ₐ ⟨"%128"⟩ &₀ ⟨"%131"⟩;
  "%133" ←ₐ .Add ⟨"%129"⟩ ⟨"%55"⟩;
  "%134" ←ₐ .Sub ⟨"%0"⟩ ⟨"%58"⟩;
  "%135" ←ₐ .Mul ⟨"%58"⟩ ⟨"%134"⟩;
  "%136" ←ₐ ⟨"%132"⟩ &₀ ⟨"%135"⟩;
  "%137" ←ₐ .Add ⟨"%133"⟩ ⟨"%58"⟩;
  "%138" ←ₐ .Sub ⟨"%0"⟩ ⟨"%61"⟩;
  "%139" ←ₐ .Mul ⟨"%61"⟩ ⟨"%138"⟩;
  "%140" ←ₐ ⟨"%136"⟩ &₀ ⟨"%139"⟩;
  "%141" ←ₐ .Add ⟨"%137"⟩ ⟨"%61"⟩;
  "%142" ←ₐ .Sub ⟨"%0"⟩ ⟨"%64"⟩;
  "%143" ←ₐ .Mul ⟨"%64"⟩ ⟨"%142"⟩;
  "%144" ←ₐ ⟨"%140"⟩ &₀ ⟨"%143"⟩;
  "%145" ←ₐ .Add ⟨"%141"⟩ ⟨"%64"⟩;
  "%146" ←ₐ .Sub ⟨"%0"⟩ ⟨"%67"⟩;
  "%147" ←ₐ .Mul ⟨"%67"⟩ ⟨"%146"⟩;
  "%148" ←ₐ ⟨"%144"⟩ &₀ ⟨"%147"⟩;
  "%149" ←ₐ .Add ⟨"%145"⟩ ⟨"%67"⟩;
  "%150" ←ₐ .Sub ⟨"%0"⟩ ⟨"%70"⟩;
  "%151" ←ₐ .Mul ⟨"%70"⟩ ⟨"%150"⟩;
  "%152" ←ₐ ⟨"%148"⟩ &₀ ⟨"%151"⟩;
  "%153" ←ₐ .Add ⟨"%149"⟩ ⟨"%70"⟩;
  "%154" ←ₐ .Sub ⟨"%0"⟩ ⟨"%73"⟩;
  "%155" ←ₐ .Mul ⟨"%73"⟩ ⟨"%154"⟩;
  "%156" ←ₐ ⟨"%152"⟩ &₀ ⟨"%155"⟩;
  "%157" ←ₐ .Add ⟨"%153"⟩ ⟨"%73"⟩;
  "%158" ←ₐ .Sub ⟨"%157"⟩ ⟨"%0"⟩;
  "%159" ←ₐ ⟨"%156"⟩ &₀ ⟨"%158"⟩
def getReturn (st: State) : Prop :=
  st.constraintsInVar ⟨"%159"⟩
def run (st: State) : Prop :=
  getReturn (full.runProgram st)

end Code

def start_state (input data : BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨"code"⟩, [input]), (⟨"data"⟩, [data])]
  , bufferWidths := Map.fromList [(⟨"code"⟩, 1), (⟨"data"⟩, 20)]
  , constraints := []
  , cycle := 0
  , felts := Map.empty
  , props := Map.empty
  , vars := [⟨"code"⟩, ⟨"data"⟩]
  , isFailed := false
  }

end Risc0.OneHot20.Constraints
