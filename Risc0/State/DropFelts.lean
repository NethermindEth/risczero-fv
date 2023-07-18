import Risc0.State.Defs

namespace Risc0.State

  lemma dropFelts_def {st: State} : st.dropFelts name = { st with felts := st.felts.drop name } := rfl

  section MemberAccess
    lemma dropFelts_buffers : (dropFelts st name).buffers = st.buffers := rfl
    lemma dropFelts_bufferWidths : (dropFelts st name).bufferWidths = st.bufferWidths := rfl
    lemma dropFelts_constraints : (dropFelts st name).constraints = st.constraints := rfl
    lemma dropFelts_cycle : (dropFelts st name).cycle = st.cycle := rfl
    lemma dropFelts_felts : (dropFelts st name).felts = st.felts.drop name := rfl
    lemma dropFelts_isFailed : (dropFelts st name).isFailed = st.isFailed := rfl
    lemma dropFelts_props : (dropFelts st name).props = st.props := rfl
    lemma dropFelts_vars : (dropFelts st name).vars = st.vars := rfl
  end MemberAccess

  section UpdateFelts
    @[simp]
    lemma drop_update_same {st : State} {name : FeltVar} {x : Felt} : 
      dropFelts (updateFelts st name x) name = dropFelts st name := by
      simp [dropFelts, updateFelts]

    -- TODO rename
    @[simp]
    lemma drop_update_swap {st : State} {name name' : FeltVar} {x : Felt} (h : name ≠ name') :
      dropFelts (updateFelts st name x) name' = updateFelts (dropFelts st name') name x := by
      simp [dropFelts, updateFelts]
      exact Map.update_drop_swap h
  end UpdateFelts

  section UpdateProps
    lemma drop_updateProps_swap :
      dropFelts (updateProps st name x) name' = updateProps (dropFelts st name') name x := by
        simp [dropFelts, updateProps]
  end UpdateProps

  -- Naughty
  @[simp]
  lemma get_dropFelts_of_ne {st : State} {x : FeltVar} (h : name ≠ x) :
    Option.get! (st.dropFelts name).felts[x] = Option.get! st.felts[x] := by
    unfold dropFelts Map.drop
    rw [Map.getElem_def]
    aesop

  @[simp]
  lemma get_dropFelts_of_ne' {st : State} {x : FeltVar} (h : name ≠ x) :
    Option.get! ((st.dropFelts name).felts x) = Option.get! (st.felts x) := by
    unfold dropFelts Map.drop
    aesop

end Risc0.State
