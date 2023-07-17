import Risc0.State.Defs

namespace Risc0

  lemma Buffer.back_def {st : State} {buf : BufferVar} {back : Back} :
    Buffer.back st buf back offset = st.buffers[buf].get!.get! (st.cycle - back.toNat, offset) := rfl

  lemma Buffer.back_zero : Buffer.back st buf 0 k = st.buffers[buf].get!.get! (st.cycle, k) := rfl

end Risc0
