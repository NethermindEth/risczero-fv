import Risc0.State.Defs

namespace Risc0.State

@[simp]
lemma set!_felts {st : State} {bufferVar : BufferVar} {offset : ℕ} {val : Felt} :
  (st.set! bufferVar offset val).felts = st.felts := by
  unfold set! setBufferElementImpl
  aesop

end Risc0.State
