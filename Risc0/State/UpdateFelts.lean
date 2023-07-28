import Risc0.State.Defs

namespace Risc0.State

  lemma updateFelts_def : 
    updateFelts st k v = { st with felts := st.felts[k] ←ₘ v } := rfl

  section MemberAccess
    @[simp]
    lemma updateFelts_buffers : (updateFelts st name x).buffers = st.buffers := by simp [updateFelts]
    @[simp]
    lemma updateFelts_bufferWidths : (updateFelts st name x).bufferWidths = st.bufferWidths := by simp [updateFelts]
    @[simp]
    lemma updateFelts_cycle : (updateFelts st name x).cycle = st.cycle := by simp [updateFelts]
    @[simp]
    lemma updateFelts_isFailed : (updateFelts st name x).isFailed = st.isFailed := by simp [updateFelts]
    @[simp]
    lemma updateFelts_props : (updateFelts st name x).props = st.props := by simp [updateFelts]
    @[simp]
    lemma updateFelts_vars : (updateFelts st name x).vars = st.vars := by simp [updateFelts]
    -- @[simp]
    lemma updateFelts_felts : (updateFelts st name x).felts = st.felts[name] ←ₘ x := by simp [updateFelts]
  end MemberAccess

  @[simp]
  lemma updateFelts_felts_get {st : State} {name : FeltVar} {x : Felt} :
    (updateFelts st name x).felts[name]! = some x := by
    simp [updateFelts, Map.update_def, Map.getElem_def, getElem!]

  -- TODO: This technically shouldn't exist, refine later?
  -- m[k] should not unfold to m k, yet there are instances in automated rewriting
  -- where this somehow occurs.
  @[simp]
  lemma updateFelts_felts_get_wobbly {st : State} {name : FeltVar} {x : Felt} :
    (updateFelts st name x).felts name = some x := updateFelts_felts_get

  -- This simp lemma feels bad with name ≠ name' but somehow it works out in our context.
  @[simp]
  lemma updateFelts_felts_get_ne {st : State} {name name' : FeltVar} {x : Felt}
    (h : name ≠ name') : (updateFelts st name x).felts[name']! = st.felts[name']! := by
    simp [updateFelts, Map.update_def, getElem!, Map.getElem_def]
    aesop'

  @[simp]
  lemma updateFelts_felts_get_ne' {st : State} {name name' : FeltVar} {x : Felt}
    (h : name ≠ name') : (updateFelts st name x).felts[name'] = st.felts[name'] := by
    simp [updateFelts, Map.update_def, getElem!, Map.getElem_def]
    aesop'

  @[simp]
  lemma updateFelts_felts_get_next (h: name ≠ name') : (updateFelts st name x).felts name' = st.felts name' := by
    simp [updateFelts]
    exact Map.update_get_next' h

end Risc0.State
