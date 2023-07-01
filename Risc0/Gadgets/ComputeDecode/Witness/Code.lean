import Risc0.Basic
import Risc0.Lemmas

namespace Risc0.ComputeDecode.Witness.Code

open MLIRNotation

def full : MLIRProgram :=
  "%0" ←ₐ .Const 127;
  "%1" ←ₐ .Const 48;
  "%2" ←ₐ .Const 1981808641;
  "%3" ←ₐ .Const 64;
  "%4" ←ₐ .Const 3;
  "%5" ←ₐ .Const 1509949441;
  "%6" ←ₐ .Const 12;
  "%7" ←ₐ .Const 4;
  "%8" ←ₐ .Const 1;
  "%9" ←ₐ .Const 1006632961;
  "%10" ←ₐ .Const 6;
  "%11" ←ₐ .Const 2;
  "%12" ←ₐ .Const 1761607681;
  "%13" ←ₐ .Const 8;
  "%14" ←ₐ .Const 1887436801;
  "%15" ←ₐ .Const 16;
  "%16" ←ₐ .Const 1950351361;
  "%17" ←ₐ .Const 96;
  "%18" ←ₐ .Const 1997537281;
  "%19" ←ₐ .Const 128;
  "%20" ←ₐ .Get ⟨"in"⟩ 0 0;
  "%21" ←ₐ .Get ⟨"in"⟩ 0 1;
  "%22" ←ₐ .Get ⟨"in"⟩ 0 2;
  "%23" ←ₐ .Get ⟨"in"⟩ 0 3;
  nondet (
    "%74" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%19"⟩;
    "%75" ←ₐ .Mul ⟨"%74"⟩ ⟨"%18"⟩;
    ⟨"data"⟩[10] ←ᵢ ⟨"%75"⟩;
    "%76" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%17"⟩;
    "%77" ←ₐ .Mul ⟨"%76"⟩ ⟨"%16"⟩;
    ⟨"data"⟩[1] ←ᵢ ⟨"%77"⟩;
    "%78" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%15"⟩;
    "%79" ←ₐ .Mul ⟨"%78"⟩ ⟨"%14"⟩;
    ⟨"data"⟩[9] ←ᵢ ⟨"%79"⟩;
    "%80" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%13"⟩;
    "%81" ←ₐ .Mul ⟨"%80"⟩ ⟨"%12"⟩;
    ⟨"data"⟩[8] ←ᵢ ⟨"%81"⟩;
    "%82" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%10"⟩;
    "%83" ←ₐ .Mul ⟨"%82"⟩ ⟨"%9"⟩;
    ⟨"data"⟩[0] ←ᵢ ⟨"%83"⟩;
    "%84" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%8"⟩;
    ⟨"data"⟩[13] ←ᵢ ⟨"%84"⟩;
    "%85" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%19"⟩;
    "%86" ←ₐ .Mul ⟨"%85"⟩ ⟨"%18"⟩;
    ⟨"data"⟩[12] ←ᵢ ⟨"%86"⟩;
    "%87" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%17"⟩;
    "%88" ←ₐ .Mul ⟨"%87"⟩ ⟨"%16"⟩;
    ⟨"data"⟩[2] ←ᵢ ⟨"%88"⟩;
    "%89" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%15"⟩;
    "%90" ←ₐ .Mul ⟨"%89"⟩ ⟨"%14"⟩;
    ⟨"data"⟩[11] ←ᵢ ⟨"%90"⟩;
    "%91" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%6"⟩;
    "%92" ←ₐ .Mul ⟨"%91"⟩ ⟨"%5"⟩;
    ⟨"data"⟩[4] ←ᵢ ⟨"%92"⟩;
    "%93" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%4"⟩;
    ⟨"data"⟩[3] ←ᵢ ⟨"%93"⟩;
    "%94" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%19"⟩;
    "%95" ←ₐ .Mul ⟨"%94"⟩ ⟨"%18"⟩;
    ⟨"data"⟩[14] ←ᵢ ⟨"%95"⟩;
    "%96" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%3"⟩;
    "%97" ←ₐ .Mul ⟨"%96"⟩ ⟨"%2"⟩;
    ⟨"data"⟩[15] ←ᵢ ⟨"%97"⟩;
    "%98" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%1"⟩;
    "%99" ←ₐ .Mul ⟨"%98"⟩ ⟨"%14"⟩;
    ⟨"data"⟩[5] ←ᵢ ⟨"%99"⟩;
    "%100" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%6"⟩;
    "%101" ←ₐ .Mul ⟨"%100"⟩ ⟨"%5"⟩;
    ⟨"data"⟩[7] ←ᵢ ⟨"%101"⟩;
    "%102" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%4"⟩;
    ⟨"data"⟩[6] ←ᵢ ⟨"%102"⟩;
    "%103" ←ₐ .BitAnd ⟨"%20"⟩ ⟨"%19"⟩;
    "%104" ←ₐ .Mul ⟨"%103"⟩ ⟨"%18"⟩;
    ⟨"data"⟩[16] ←ᵢ ⟨"%104"⟩;
    "%105" ←ₐ .BitAnd ⟨"%20"⟩ ⟨"%0"⟩;
    ⟨"data"⟩[17] ←ᵢ ⟨"%105"⟩
  );
  "%24" ←ₐ .Get ⟨"data"⟩ 0 13;
  "%25" ←ₐ .Get ⟨"data"⟩ 0 0;
  "%26" ←ₐ .Get ⟨"data"⟩ 0 8;
  "%27" ←ₐ .Mul ⟨"%26"⟩ ⟨"%7"⟩;
  "%28" ←ₐ .Get ⟨"data"⟩ 0 9;
  "%29" ←ₐ .Mul ⟨"%28"⟩ ⟨"%13"⟩;
  "%30" ←ₐ .Get ⟨"data"⟩ 0 1;
  "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%15"⟩;
  "%32" ←ₐ .Add ⟨"%31"⟩ ⟨"%29"⟩;
  "%33" ←ₐ .Add ⟨"%32"⟩ ⟨"%27"⟩;
  "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%25"⟩;
  "%35" ←ₐ .Get ⟨"data"⟩ 0 10;
  "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%3"⟩;
  "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%34"⟩;
  "%38" ←ₐ .Mul ⟨"%37"⟩ ⟨"%11"⟩;
  "%39" ←ₐ .Add ⟨"%38"⟩ ⟨"%24"⟩;
  "%40" ←ₐ .Sub ⟨"%23"⟩ ⟨"%39"⟩;
  ?₀ ⟨"%40"⟩;
  "%41" ←ₐ .Get ⟨"data"⟩ 0 3;
  "%42" ←ₐ .Get ⟨"data"⟩ 0 4;
  "%43" ←ₐ .Mul ⟨"%42"⟩ ⟨"%7"⟩;
  "%44" ←ₐ .Get ⟨"data"⟩ 0 11;
  "%45" ←ₐ .Get ⟨"data"⟩ 0 2;
  "%46" ←ₐ .Mul ⟨"%45"⟩ ⟨"%11"⟩;
  "%47" ←ₐ .Get ⟨"data"⟩ 0 12;
  "%48" ←ₐ .Mul ⟨"%47"⟩ ⟨"%13"⟩;
  "%49" ←ₐ .Add ⟨"%48"⟩ ⟨"%46"⟩;
  "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%44"⟩;
  "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%15"⟩;
  "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%43"⟩;
  "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%41"⟩;
  "%54" ←ₐ .Sub ⟨"%22"⟩ ⟨"%53"⟩;
  ?₀ ⟨"%54"⟩;
  "%55" ←ₐ .Get ⟨"data"⟩ 0 6;
  "%56" ←ₐ .Get ⟨"data"⟩ 0 7;
  "%57" ←ₐ .Mul ⟨"%56"⟩ ⟨"%7"⟩;
  "%58" ←ₐ .Get ⟨"data"⟩ 0 5;
  "%59" ←ₐ .Get ⟨"data"⟩ 0 15;
  "%60" ←ₐ .Mul ⟨"%59"⟩ ⟨"%7"⟩;
  "%61" ←ₐ .Add ⟨"%60"⟩ ⟨"%58"⟩;
  "%62" ←ₐ .Mul ⟨"%61"⟩ ⟨"%15"⟩;
  "%63" ←ₐ .Get ⟨"data"⟩ 0 14;
  "%64" ←ₐ .Mul ⟨"%63"⟩ ⟨"%19"⟩;
  "%65" ←ₐ .Add ⟨"%64"⟩ ⟨"%62"⟩;
  "%66" ←ₐ .Add ⟨"%65"⟩ ⟨"%57"⟩;
  "%67" ←ₐ .Add ⟨"%66"⟩ ⟨"%55"⟩;
  "%68" ←ₐ .Sub ⟨"%21"⟩ ⟨"%67"⟩;
  ?₀ ⟨"%68"⟩;
  "%69" ←ₐ .Get ⟨"data"⟩ 0 17;
  "%70" ←ₐ .Get ⟨"data"⟩ 0 16;
  "%71" ←ₐ .Mul ⟨"%70"⟩ ⟨"%19"⟩;
  "%72" ←ₐ .Add ⟨"%71"⟩ ⟨"%69"⟩;
  "%73" ←ₐ .Sub ⟨"%20"⟩ ⟨"%72"⟩;
  ?₀ ⟨"%73"⟩
def getReturn (st: State) : BufferAtTime :=
  st.buffers ⟨"data"⟩ |>.get!.getLast!
def run (st: State) : BufferAtTime :=
  getReturn (full.runProgram st)

end Risc0.ComputeDecode.Witness.Code
