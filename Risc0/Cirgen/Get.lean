import Risc0.State

namespace Risc0

  def isGetValid (st : State) (buf : BufferVar) (back : Back) (offset : ℕ) :=
    back ≤ st.cycle ∧
    buf ∈ st.vars ∧
    offset < st.bufferWidths[buf].get! ∧
    (Buffer.back st buf back offset).isSome

  lemma isGetValid_def :
    isGetValid st buf back offset = 
    (back ≤ st.cycle ∧
    buf ∈ st.vars ∧
    offset < st.bufferWidths[buf].get! ∧
    (Buffer.back st buf back offset).isSome) := rfl

  instance : Decidable (isGetValid st buf back offset) := by unfold isGetValid; exact inferInstance

  def getImpl (st : State) (buf : BufferVar) (back : Back) (offset : ℕ) :=
    if isGetValid st buf back offset
    then Option.some <| Lit.Val (Buffer.back st buf back offset).get!
    else .none

  lemma getImpl_def : getImpl st buf back offset = 
                      if isGetValid st buf back offset
                      then Option.some <| Lit.Val (Buffer.back st buf back offset).get!
                      else .none := rfl

  --Review: should any of these be simps?
  lemma getImpl_none_or_val : getImpl st buf back offset = .none ∨ ∃ x, getImpl st buf back offset = some (.Val x) := by
    simp [getImpl]
    aesop

  lemma getImpl_val_of_some : getImpl st buf back offset = some lit → ∃ x, lit = .Val x := by
    have h: getImpl st buf back offset = .none ∨ ∃ x, getImpl st buf back offset = some (.Val x) := getImpl_none_or_val
    aesop

  lemma getImpl_skip_none_update : getImpl (st[name] ←ₛ .none) buf back offset = getImpl st buf back offset := by
    simp [State.update, getImpl, isGetValid, Buffer.back]

  lemma getImpl_skip_val_update : getImpl (st[name] ←ₛ .some (.Val x)) buf back offset = getImpl st buf back offset := by
    simp [State.update, getImpl, isGetValid, Buffer.back]

  @[simp]
  lemma getImpl_skip_get_update:
    getImpl (st[name] ←ₛ getImpl st' buf' back' offset') buf back offset =
    getImpl st buf back offset := by
    generalize eq: getImpl st' buf' back' offset' = x
    cases x with
    | none => exact getImpl_skip_none_update
    | some lit =>
      have h: ∃ x, lit = Lit.Val x := getImpl_val_of_some eq
      aesop

  lemma getImpl_skip_set_offset (h: offset ≠ offset'):
    getImpl (State.set! st buf offset val) buf back offset' =
    getImpl st buf back offset' := by
      sorry

end Risc0
