import Risc0.State.Defs
import Risc0.State.Notation
import Risc0.Cirgen.Defs

namespace Risc0.State

  section MemberAccess
    @[simp]
    lemma set!_felts {st : State} {bufferVar : BufferVar} {offset : ℕ} {val : Felt} :
      (st.set! bufferVar offset val).felts = st.felts := by
      unfold set! setBufferElementImpl
      aesop'

    @[simp]
    lemma set!_cycle {st : State} : (st.set! buf off x).cycle = st.cycle := by
      unfold set! setBufferElementImpl
      aesop'

    @[simp]
    lemma set!_vars {st : State} : (st.set! buf off x).vars = st.vars := by
      unfold set! setBufferElementImpl
      aesop'
  end MemberAccess

  lemma set!_bufferWidths_get_of_ne {st : State} (h : buf ≠ buf') :
    (st.set! buf' index x).bufferWidths[buf] = st.bufferWidths[buf] := by
    unfold set! setBufferElementImpl Buffer.set? 
    aesop'

  lemma set!_buffers_get_of_ne {st : State} (h : buf ≠ buf') : 
    (st.set! buf' index x).buffers[buf] = st.buffers[buf] := by
    unfold set! setBufferElementImpl Map.update
    rw [Map.getElem_def]
    aesop'

  lemma set!_get_getImpl_comm {st : State} : 
    (st[x] ←ₛ getImpl st buf back offset).set! buf' index y =
    (State.set! st buf' index y)[x] ←ₛ getImpl st buf back offset := by
    unfold State.update getImpl
    aesop' <;> unfold set! setBufferElementImpl <;> aesop'

  -- TODO rename get_set!_of_ne?
  lemma get!_set!_of_ne (h : buf ≠ buf') :
    (State.set! st buf' index x).buffers[buf] = st.buffers[buf] := by
    unfold State.set! State.setBufferElementImpl Map.update
    rw [Map.getElem_def]
    aesop'

  @[simp]
  lemma get_set!_getElem {st : State} :
    (State.set! st buf offset val).bufferWidths[buf] =
    st.bufferWidths[buf] := by
    unfold State.set! State.setBufferElementImpl Buffer.set?
    aesop'

end Risc0.State
