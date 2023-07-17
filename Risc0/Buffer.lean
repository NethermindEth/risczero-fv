import Risc0.BasicTypes

namespace Risc0

  -- none is an unset value which can be written to, but not read
  -- some is a set value which can be read, and can only be written to if the new val is equal
  abbrev BufferAtTime := List (Option Felt)
  abbrev Buffer := List BufferAtTime

  namespace Buffer

    abbrev Idx := ℕ × ℕ -- time, data
    abbrev Idx.time : Idx → ℕ := Prod.fst
    abbrev Idx.data : Idx → ℕ := Prod.snd

    def empty : Buffer := []

    def init (size : ℕ) : Buffer := [List.replicate size .none]

    def init' (row : BufferAtTime) : Buffer := [row]

    def last! (buf : Buffer) : BufferAtTime :=
      buf.getLast!

    def copyLast (buf : Buffer) : Buffer := 
      buf.push buf.last!

    def get! (buf : Buffer) (idx : Idx) : Option Felt :=
      List.get! (List.get! buf idx.time) idx.data

    -- @[simp]
    -- lemma www : buffer.get! [[some ...]] (0...k)

    def getBufferAtTime! (buf : Buffer) (timeIdx : ℕ) : BufferAtTime :=
      List.get! buf timeIdx

    def setAllLatest! (buf : Buffer) (val : BufferAtTime) : Buffer :=
      List.set buf (buf.length - 1) val

    def set? (buf : Buffer) (idx: Idx) (val: Felt) : Option Buffer :=
      let bufferAtTime := buf.getBufferAtTime! idx.time
      let oldVal := (bufferAtTime.get! idx.data)
      if oldVal.isEqSome val
      then .some buf
      else
        if oldVal.isNone
        then .some <| List.set buf idx.time (bufferAtTime.set idx.data (.some val))
        else .none

    def isValidUpdate (old new : BufferAtTime) :=
      old.length = new.length ∧
      (List.zip old new).all
        λ (oldElem, newElem) =>
          oldElem.isNone ∨
          oldElem = newElem

    instance {old new} : Decidable (Buffer.isValidUpdate old new) := by
      unfold Buffer.isValidUpdate
      exact inferInstance

    def Idx.from1D (flatOffset width : ℕ) : Idx :=
      (flatOffset.div width, flatOffset.mod width)

    lemma data_idx_le_width (flatOffset width : ℕ) (h: width > 0) : (Idx.from1D flatOffset width).data < width :=
      Nat.mod_lt _ h

  end Buffer

end Risc0
