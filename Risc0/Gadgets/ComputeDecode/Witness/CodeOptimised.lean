import Risc0.Gadgets.ComputeDecode.Witness.CodeReordered

namespace Risc0.ComputeDecode.Witness.Code

open MLIRNotation
def full_opt : MLIRProgram :=
  "%19" ←ₐ .Const 128;
  "%23" ←ₐ .Get ⟨"in"⟩ 0 3;
  nondet (
    "%74" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%19"⟩
  );
  "%18" ←ₐ .Const 1997537281;
  nondet (
    "%75" ←ₐ .Mul ⟨"%74"⟩ ⟨"%18"⟩;
    ⟨"data"⟩[10] ←ᵢ ⟨"%75"⟩
  );
  "%17" ←ₐ .Const 96;
  nondet (
    "%76" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%17"⟩
  );
  dropfelt ⟨"%74"⟩;
  dropfelt ⟨"%75"⟩;
  "%16" ←ₐ .Const 1950351361;
  nondet (
    "%77" ←ₐ .Mul ⟨"%76"⟩ ⟨"%16"⟩;
    ⟨"data"⟩[1] ←ᵢ ⟨"%77"⟩
  );
  "%15" ←ₐ .Const 16;
  dropfelt ⟨"%76"⟩;
  dropfelt ⟨"%77"⟩;
  nondet (
    "%78" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%15"⟩
  );
  "%14" ←ₐ .Const 1887436801;
  nondet (
    "%79" ←ₐ .Mul ⟨"%78"⟩ ⟨"%14"⟩;
    ⟨"data"⟩[9] ←ᵢ ⟨"%79"⟩
  );
  dropfelt ⟨"%78"⟩;
  dropfelt ⟨"%79"⟩;
  "%13" ←ₐ .Const 8;
  nondet (
    "%80" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%13"⟩
  );
  "%12" ←ₐ .Const 1761607681;
  nondet (
    "%81" ←ₐ .Mul ⟨"%80"⟩ ⟨"%12"⟩
  );
  dropfelt ⟨"%80"⟩;
  dropfelt ⟨"%80"⟩;
  nondet (
    ⟨"data"⟩[8] ←ᵢ ⟨"%81"⟩
  );
  "%10" ←ₐ .Const 6;
  nondet (
    "%82" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%10"⟩
  );
  "%9" ←ₐ .Const 1006632961;
  dropfelt ⟨"%81"⟩;
  dropfelt ⟨"%10"⟩;
  nondet (
    "%83" ←ₐ .Mul ⟨"%82"⟩ ⟨"%9"⟩;
    ⟨"data"⟩[0] ←ᵢ ⟨"%83"⟩
  );
  "%8" ←ₐ .Const 1;
  nondet (
    "%84" ←ₐ .BitAnd ⟨"%23"⟩ ⟨"%8"⟩
  );
  dropfelt ⟨"%82"⟩;
  dropfelt ⟨"%82"⟩;
  dropfelt ⟨"%83"⟩;
  dropfelt ⟨"%8"⟩;
  nondet (
    ⟨"data"⟩[13] ←ᵢ ⟨"%84"⟩
  );
  "%22" ←ₐ .Get ⟨"in"⟩ 0 2;
  nondet (
    "%85" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%19"⟩;
    "%86" ←ₐ .Mul ⟨"%85"⟩ ⟨"%18"⟩
  );
  dropfelt ⟨"%84"⟩;
  dropfelt ⟨"%85"⟩;
  nondet (
    ⟨"data"⟩[12] ←ᵢ ⟨"%86"⟩;
    "%87" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%17"⟩;
    "%88" ←ₐ .Mul ⟨"%87"⟩ ⟨"%16"⟩;
    ⟨"data"⟩[2] ←ᵢ ⟨"%88"⟩
  );
  dropfelt ⟨"%86"⟩;
  dropfelt ⟨"%17"⟩;
  dropfelt ⟨"%16"⟩;
  dropfelt ⟨"%16"⟩;
  dropfelt ⟨"%88"⟩;
  nondet (
    "%89" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%15"⟩;
    "%90" ←ₐ .Mul ⟨"%89"⟩ ⟨"%14"⟩;
    ⟨"data"⟩[11] ←ᵢ ⟨"%90"⟩
  );
  "%6" ←ₐ .Const 12;
  dropfelt ⟨"%89"⟩;
  dropfelt ⟨"%90"⟩;
  nondet (
    "%91" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%6"⟩
  );
  "%5" ←ₐ .Const 1509949441;
  nondet (
    "%92" ←ₐ .Mul ⟨"%91"⟩ ⟨"%5"⟩;
    ⟨"data"⟩[4] ←ᵢ ⟨"%92"⟩
  );
  dropfelt ⟨"%91"⟩;
  dropfelt ⟨"%92"⟩;
  "%4" ←ₐ .Const 3;
  nondet (
    "%93" ←ₐ .BitAnd ⟨"%22"⟩ ⟨"%4"⟩;
    ⟨"data"⟩[3] ←ᵢ ⟨"%93"⟩
  );
  "%21" ←ₐ .Get ⟨"in"⟩ 0 1;
  dropfelt ⟨"%93"⟩;
  nondet (
    "%94" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%19"⟩;
    "%95" ←ₐ .Mul ⟨"%94"⟩ ⟨"%18"⟩;
    ⟨"data"⟩[14] ←ᵢ ⟨"%95"⟩
  );
  "%3" ←ₐ .Const 64;
  dropfelt ⟨"%94"⟩;
  dropfelt ⟨"%95"⟩;
  nondet (
    "%96" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%3"⟩
  );
  "%2" ←ₐ .Const 1981808641;
  nondet (
    "%97" ←ₐ .Mul ⟨"%96"⟩ ⟨"%2"⟩;
    ⟨"data"⟩[15] ←ᵢ ⟨"%97"⟩
  );
  dropfelt ⟨"%96"⟩;
  dropfelt ⟨"%96"⟩;
  dropfelt ⟨"%97"⟩;
  "%1" ←ₐ .Const 48;
  nondet (
    "%98" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%1"⟩;
    "%99" ←ₐ .Mul ⟨"%98"⟩ ⟨"%14"⟩;
    ⟨"data"⟩[5] ←ᵢ ⟨"%99"⟩
  );
  dropfelt ⟨"%1"⟩;
  dropfelt ⟨"%14"⟩;
  dropfelt ⟨"%14"⟩;
  dropfelt ⟨"%99"⟩;
  nondet (
    "%100" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%6"⟩;
    "%101" ←ₐ .Mul ⟨"%100"⟩ ⟨"%5"⟩;
    ⟨"data"⟩[7] ←ᵢ ⟨"%101"⟩;
    "%102" ←ₐ .BitAnd ⟨"%21"⟩ ⟨"%4"⟩
  );
  dropfelt ⟨"%6"⟩;
  dropfelt ⟨"%5"⟩;
  dropfelt ⟨"%5"⟩;
  dropfelt ⟨"%101"⟩;
  dropfelt ⟨"%4"⟩;
  nondet (
    ⟨"data"⟩[6] ←ᵢ ⟨"%102"⟩
  );
  "%20" ←ₐ .Get ⟨"in"⟩ 0 0;
  nondet (
    "%103" ←ₐ .BitAnd ⟨"%20"⟩ ⟨"%19"⟩;
    "%104" ←ₐ .Mul ⟨"%103"⟩ ⟨"%18"⟩
  );
  dropfelt ⟨"%102"⟩;
  dropfelt ⟨"%18"⟩;
  dropfelt ⟨"%18"⟩;
  nondet (
    ⟨"data"⟩[16] ←ᵢ ⟨"%104"⟩
  );
  "%0" ←ₐ .Const 127;
  nondet (
    "%105" ←ₐ .BitAnd ⟨"%20"⟩ ⟨"%0"⟩;
    ⟨"data"⟩[17] ←ᵢ ⟨"%105"⟩
  );
  dropfelt ⟨"%104"⟩;
  dropfelt ⟨"%0"⟩;
  dropfelt ⟨"%105"⟩;
  "%7" ←ₐ .Const 4;
  "%26" ←ₐ .Get ⟨"data"⟩ 0 8;
  "%27" ←ₐ .Mul ⟨"%26"⟩ ⟨"%7"⟩;
  "%28" ←ₐ .Get ⟨"data"⟩ 0 9;
  dropfelt ⟨"%26"⟩;
  "%29" ←ₐ .Mul ⟨"%28"⟩ ⟨"%13"⟩;
  "%30" ←ₐ .Get ⟨"data"⟩ 0 1;
  "%31" ←ₐ .Mul ⟨"%30"⟩ ⟨"%15"⟩;
  "%32" ←ₐ .Add ⟨"%31"⟩ ⟨"%29"⟩;
  dropfelt ⟨"%28"⟩;
  dropfelt ⟨"%30"⟩;
  dropfelt ⟨"%29"⟩;
  dropfelt ⟨"%29"⟩;
  "%33" ←ₐ .Add ⟨"%32"⟩ ⟨"%27"⟩;
  "%25" ←ₐ .Get ⟨"data"⟩ 0 0;
  "%34" ←ₐ .Add ⟨"%33"⟩ ⟨"%25"⟩;
  "%35" ←ₐ .Get ⟨"data"⟩ 0 10;
  dropfelt ⟨"%27"⟩;
  dropfelt ⟨"%27"⟩;
  dropfelt ⟨"%33"⟩;
  dropfelt ⟨"%33"⟩;
  "%36" ←ₐ .Mul ⟨"%35"⟩ ⟨"%3"⟩;
  "%37" ←ₐ .Add ⟨"%36"⟩ ⟨"%34"⟩;
  "%11" ←ₐ .Const 2;
  "%38" ←ₐ .Mul ⟨"%37"⟩ ⟨"%11"⟩;
  dropfelt ⟨"%3"⟩;
  dropfelt ⟨"%3"⟩;
  dropfelt ⟨"%34"⟩;
  dropfelt ⟨"%34"⟩;
  dropfelt ⟨"%37"⟩;
  "%24" ←ₐ .Get ⟨"data"⟩ 0 13;
  "%39" ←ₐ .Add ⟨"%38"⟩ ⟨"%24"⟩;
  "%40" ←ₐ .Sub ⟨"%23"⟩ ⟨"%39"⟩;
  ?₀ ⟨"%40"⟩;
  dropfelt ⟨"%38"⟩;
  dropfelt ⟨"%38"⟩;
  dropfelt ⟨"%23"⟩;
  dropfelt ⟨"%23"⟩;
  dropfelt ⟨"%40"⟩;
  "%42" ←ₐ .Get ⟨"data"⟩ 0 4;
  "%43" ←ₐ .Mul ⟨"%42"⟩ ⟨"%7"⟩;
  "%45" ←ₐ .Get ⟨"data"⟩ 0 2;
  "%46" ←ₐ .Mul ⟨"%45"⟩ ⟨"%11"⟩;
  dropfelt ⟨"%42"⟩;
  dropfelt ⟨"%11"⟩;
  dropfelt ⟨"%11"⟩;
  "%47" ←ₐ .Get ⟨"data"⟩ 0 12;
  "%48" ←ₐ .Mul ⟨"%47"⟩ ⟨"%13"⟩;
  "%49" ←ₐ .Add ⟨"%48"⟩ ⟨"%46"⟩;
  "%44" ←ₐ .Get ⟨"data"⟩ 0 11;
  dropfelt ⟨"%13"⟩;
  dropfelt ⟨"%13"⟩;
  dropfelt ⟨"%46"⟩;
  dropfelt ⟨"%46"⟩;
  "%50" ←ₐ .Add ⟨"%49"⟩ ⟨"%44"⟩;
  "%51" ←ₐ .Mul ⟨"%50"⟩ ⟨"%15"⟩;
  "%52" ←ₐ .Add ⟨"%51"⟩ ⟨"%43"⟩;
  "%41" ←ₐ .Get ⟨"data"⟩ 0 3;
  dropfelt ⟨"%49"⟩;
  dropfelt ⟨"%49"⟩;
  dropfelt ⟨"%50"⟩;
  dropfelt ⟨"%43"⟩;
  dropfelt ⟨"%43"⟩;
  "%53" ←ₐ .Add ⟨"%52"⟩ ⟨"%41"⟩;
  "%54" ←ₐ .Sub ⟨"%22"⟩ ⟨"%53"⟩;
  ?₀ ⟨"%54"⟩;
  "%56" ←ₐ .Get ⟨"data"⟩ 0 7;
  dropfelt ⟨"%52"⟩;
  dropfelt ⟨"%52"⟩;
  dropfelt ⟨"%22"⟩;
  dropfelt ⟨"%22"⟩;
  dropfelt ⟨"%54"⟩;
  "%57" ←ₐ .Mul ⟨"%56"⟩ ⟨"%7"⟩;
  "%59" ←ₐ .Get ⟨"data"⟩ 0 15;
  "%60" ←ₐ .Mul ⟨"%59"⟩ ⟨"%7"⟩;
  "%58" ←ₐ .Get ⟨"data"⟩ 0 5;
  dropfelt ⟨"%56"⟩;
  dropfelt ⟨"%7"⟩;
  dropfelt ⟨"%7"⟩;
  "%61" ←ₐ .Add ⟨"%60"⟩ ⟨"%58"⟩;
  "%62" ←ₐ .Mul ⟨"%61"⟩ ⟨"%15"⟩;
  "%63" ←ₐ .Get ⟨"data"⟩ 0 14;
  "%64" ←ₐ .Mul ⟨"%63"⟩ ⟨"%19"⟩;
  dropfelt ⟨"%60"⟩;
  dropfelt ⟨"%60"⟩;
  dropfelt ⟨"%15"⟩;
  dropfelt ⟨"%15"⟩;
  dropfelt ⟨"%63"⟩;
  "%65" ←ₐ .Add ⟨"%64"⟩ ⟨"%62"⟩;
  "%66" ←ₐ .Add ⟨"%65"⟩ ⟨"%57"⟩;
  "%55" ←ₐ .Get ⟨"data"⟩ 0 6;
  "%67" ←ₐ .Add ⟨"%66"⟩ ⟨"%55"⟩;
  dropfelt ⟨"%62"⟩;
  dropfelt ⟨"%62"⟩;
  dropfelt ⟨"%57"⟩;
  dropfelt ⟨"%57"⟩;
  dropfelt ⟨"%66"⟩;
  dropfelt ⟨"%66"⟩;
  "%68" ←ₐ .Sub ⟨"%21"⟩ ⟨"%67"⟩;
  ?₀ ⟨"%68"⟩;
  "%70" ←ₐ .Get ⟨"data"⟩ 0 16;
  "%71" ←ₐ .Mul ⟨"%70"⟩ ⟨"%19"⟩;
  dropfelt ⟨"%21"⟩;
  dropfelt ⟨"%21"⟩;
  dropfelt ⟨"%68"⟩;
  dropfelt ⟨"%19"⟩;
  dropfelt ⟨"%19"⟩;
  "%69" ←ₐ .Get ⟨"data"⟩ 0 17;
  "%72" ←ₐ .Add ⟨"%71"⟩ ⟨"%69"⟩;
  "%73" ←ₐ .Sub ⟨"%20"⟩ ⟨"%72"⟩;
  ?₀ ⟨"%73"⟩;
  dropfelt ⟨"%71"⟩;
  dropfelt ⟨"%71"⟩;
  dropfelt ⟨"%20"⟩;
  dropfelt ⟨"%20"⟩;
  dropfelt ⟨"%73"⟩
end Risc0.ComputeDecode.Witness.Code