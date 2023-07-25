import Risc0.State.Defs

namespace Risc0.State

  lemma updateProps_def :
    updateProps st k v = { st with props := st.props[k] ←ₘ v } := rfl

  section MemberAccess
    @[simp]
    lemma updateProps_buffers : (updateProps st name x).buffers = st.buffers := by simp [updateProps]
    @[simp]
    lemma updateProps_bufferWidths : (updateProps st name x).bufferWidths = st.bufferWidths := by simp [updateProps]
    @[simp]
    lemma updateProps_constraints : (updateProps st name x).constraints = st.constraints := by simp [updateProps]
    @[simp]
    lemma updateProps_cycle : (updateProps st name x).cycle = st.cycle := by simp [updateProps]
    @[simp]
    lemma updateProps_isFailed : (updateProps st name x).isFailed = st.isFailed := by simp [updateProps]
    @[simp]
    lemma updateProps_felts : (updateProps st name x).felts = st.felts := by simp [updateProps]
    @[simp]
    lemma updateProps_vars : (updateProps st name x).vars = st.vars := by simp [updateProps]
    -- @[simp]
    lemma updateProps_props : (updateProps st name x).props = st.props[name] ←ₘ x := by simp [updateProps]
  end MemberAccess

  @[simp]
  lemma updateProps_props_get {st : State} {name : PropVar} {x : Prop} :
    (updateProps st name x).props[name]! = some x := by
    simp [updateProps, Map.update_def, Map.getElem_def, getElem!]

  @[simp]
  lemma updateProps_props_get_wobbly {st : State} {name : PropVar} {x : Prop} :
    (updateProps st name x).props name = some x := updateProps_props_get

  -- This simp lemma feels bad with name ≠ name' but somehow it works out in our context.
  @[simp]
  lemma updateProps_props_get_ne {st : State} {name name' : PropVar} {x : Prop}
    (h : name ≠ name') : (updateProps st name x).props[name']! = st.props[name']! := by
    simp [updateProps, Map.update_def, getElem!, Map.getElem_def]
    aesop'

end Risc0.State
