import Risc0.Basic
import Risc0.Gadgets.IsZero.Constraints.Code
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart0
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart1
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart2
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart3
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart4

namespace Risc0.IsZero.Constraints.WP

def fixed_start_state (input : Felt) (output : BufferAtTime) : State :=
  { buffers := Map.fromList [(⟨"input"⟩, [[.some input]]), (⟨"output"⟩, [output])]
  , bufferWidths := Map.fromList [(⟨"input"⟩, 1), (⟨"output"⟩, 2)]
  , constraints := []
  , cycle := 0
  , felts := Map.empty
  , props := Map.empty
  , vars := [⟨"input"⟩, ⟨"output"⟩]
  , isFailed := false
  }

lemma fixed_closed_form {x: Felt} {y₁ y₂ : Felt} : Code.run (fixed_start_state x ([some y₁, some y₂])) ↔
    (if y₁ = 0 then True else x = 0) ∧ if 1 - y₁ = 0 then True else x * y₂ - 1 = 0 := by
  rw [part₀_wp]
  rw [part₁_updates_opaque]
  rw [part₂_updates_opaque]
  rw [part₃_updates_opaque]
  rw [part₄_updates_opaque]

  generalize eq : ((if y₁ = 0 then True else x = 0) ∧ if 1 - y₁ = 0 then True else x * y₂ - 1 = 0) = rhs

  unfold fixed_start_state

  unfold part₀_state
  MLIR_states_updates

  unfold part₁_state
  MLIR_states_updates
  
  unfold part₂_state
  MLIR_states_updates

  unfold part₃_state
  MLIR_states_updates

  unfold part₄_state
  MLIR_states_updates

  simp [Code.getReturn, State.constraintsInVar, State.constraints]
  rw [←eq]

def start_state (st: State) (input : Felt) (is0_output: Option Felt) (inv_output: Option Felt) : Prop :=
  st.WellFormed ∧
  0 ≤ st.cycle ∧
  (⟨"input"⟩ ∈ st.vars) ∧
  (⟨"output"⟩ ∈ st.vars) ∧
  -- (st.bufferWidths[({name := "input"}: BufferVar)]! = some 1) ∧
  st.bufferWidths[({ name := "input" }: BufferVar)] = some 1 ∧
  (st.bufferWidths[({name := "output"}: BufferVar)]! = some 3) ∧
  -- (List.get! st.buffers[({name := "input"}: BufferVar)].get! st.cycle = [some input]) ∧
  -- List.get!(List.get! ((State.buffers st { name := "input" }).get!) 
  Buffer.back st { name := "input" } 0 0 = some input ∧
  Buffer.back st { name := "output" } 0 0 = is0_output ∧
  Buffer.back st { name := "output" } 0 1 = inv_output

lemma State.updateFelts_isGetValid {st: State} : isGetValid (State.updateFelts st name var) = isGetValid st := by
  simp only [isGetValid, State.updateFelts_cycle, State.updateFelts_vars, State.updateFelts_bufferWidths,
  Buffer.back, State.updateFelts_buffers, ge_iff_le]

lemma State.updateProps_isGetValid {st: State} : isGetValid (State.updateProps st name var) = isGetValid st := by
  simp only [isGetValid, State.updateProps_cycle, State.updateProps_vars, State.updateProps_bufferWidths,
  Buffer.back, State.updateProps_buffers, ge_iff_le]

lemma State.updateFelts_bufferBack {st: State} :
  Buffer.back (State.updateFelts st name var) buf back offset = 
  Buffer.back st buf back offset := by
  simp only [Buffer.back, State.updateFelts_buffers, State.updateFelts_cycle, ge_iff_le]

lemma State.updateProps_bufferBack {st: State} :
  Buffer.back (State.updateProps st name var) buf back offset = 
  Buffer.back st buf back offset := by
  simp only [Buffer.back, State.updateProps_buffers, State.updateProps_cycle, ge_iff_le]

lemma wellFormed_validGet {st: State}
  (hwf: st.WellFormed) (hvar: var ∈ st.vars) (hwidth: st.bufferWidths[var] = some width)
  (htime: time ≤ st.cycle) (hdata: data < width) (helem: Buffer.get! (Option.get! st.buffers[var]) (st.cycle - Back.toNat time, data) = some elem) :
  isGetValid st var time data := by
  unfold isGetValid
  apply And.intro
  . exact htime
  . apply And.intro
    . exact hvar
    . apply And.intro
      . simp [hwidth, hdata]
      . unfold Buffer.back
        simp [helem]

-- Temporary lemma used to work out what will be needed once wellFormed_validGet is working
lemma isGetValidSkip : isGetValid st buf back offset := sorry

-- lemma closed_form {st: State} {x: Felt} {y₁ y₂ : Option Felt} : start_state st x y₁ y₂ → (
--     Code.run st ↔
--     ((if Option.get! y₁ = 0 then True else x = 0) ∧ if 1 - Option.get! y₁ = 0 then True else x * Option.get! y₂ - 1 = 0)
--   ) := by
--   unfold start_state
--   intro h_pre
--   rw [part₀_wp]
--   rw [part₁_updates_opaque]
--   rw [part₂_updates_opaque]
--   rw [part₃_updates_opaque]
--   rw [part₄_updates_opaque]

--   generalize eq : ((if Option.get! y₁ = 0 then True else x = 0) ∧ if 1 - Option.get! y₁ = 0 then True else x * Option.get! y₂ - 1 = 0) = rhs

--   unfold part₀_state
--   MLIR_states_updates

--   unfold part₁_state
--   -- have hwf: st.WellFormed := by simp [h_pre]
--   -- have hvar: { name := "input" } ∈ st.vars := by simp only [h_pre]
--   -- have hwidth: st.bufferWidths[({ name := "input" }: BufferVar)] = some 1 := by simp only [h_pre]
--   -- have htime: 0 ≤ st.cycle := by simp only [zero_le]
--   -- have hdata: (0 < 1) := by simp only
--   -- have helem: Buffer.get! (Option.get! st.buffers[({name := "input"}: BufferVar)]) (st.cycle, 0) = some x :=
--   --   by simp? [h_pre, Buffer.get!, Buffer.Idx.time, Buffer.Idx.data] -- requires (List.get! st.buffers[({name := "input"}: BufferVar)].get! st.cycle = [some input]) in the start_state
--   -- have hvalidget: isGetValid st { name := "input" } 0 0 :=
--   --   wellFormed_validGet hwf hvar hwidth htime hdata helem
--     -- REVIEW: why does this work, but adding wellFormed_validGet, hwf, hvar, hwidth, htime, hdata, helem to the simp does not?
--   simp? [
--     h_pre, getImpl, State.updateFelts_isGetValid, State.updateProps_isGetValid, isGetValidSkip,
--     State.updateFelts_bufferBack, State.updateProps_bufferBack, Map.update_get_skip', Map.update_get_next',
--     Map.update_get_skip, Map.update_get_next
--   ]
--   -- NOTE: place cursor here for maximally simple goal, the follow up simps complicate things
--   -- simp? [
--   --   getImpl, isGetValid, Buffer.back, Option.get!,
--   --   Buffer.get!, State.set!, State.setBufferElementImpl, State.set!, Buffer.set?,
--   --   Option.isEqSome, List.set, State.felts_if, State.buffers_if, State.bufferWidths_if,
--   --   State.cycle_if, State.isFailed_if, State.vars_if, State.props_if,
--   --   State.constraints_if, State.props_if
--   -- ] --states_new
--   -- simp? [
--   --   Map.update, getElem!, ite_true, Option.get!_of_some, ite_false, true_and, Option.getD_some,
--   --   Map.fromList_cons, Map.fromList_nil, State.update_val', 
--   --   le_refl, List.find?, List.mem_cons, ge_iff_le, tsub_eq_zero_of_le,
--   --   List.cons.injEq, and_imp, forall_apply_eq_imp_iff', forall_eq',
--   --   Nat.succ_ne_self, IsEmpty.forall_iff, implies_true, forall_const, Nat.succ.injEq,
--   --   getElem, instGetElemMapOptionTrue, State.updateFelts_buffers, State.updateFelts_bufferWidths,
--   --   State.updateFelts_constraints, State.updateFelts_cycle, State.updateFelts_isFailed,
--   --   State.updateFelts_props, State.updateFelts_vars, State.updateFelts_felts, State.updateProps_buffers,
--   --   State.updateProps_bufferWidths, State.updateProps_constraints, State.updateProps_cycle,
--   --   State.updateProps_isFailed, State.updateProps_felts, State.updateProps_vars, State.updateProps_props,
--   --   Buffer.Idx.time, Buffer.Idx.data, Back.toNat, h_pre, nonpos_iff_eq_zero, tsub_zero
--   -- ] --decide_updates
--   -- simp only [Map.update_def.symm]
  
--   unfold part₂_state
--   simp? [
--     h_pre, getImpl, State.updateFelts_isGetValid, State.updateProps_isGetValid, isGetValidSkip,
--     State.updateFelts_bufferBack, State.updateProps_bufferBack, Map.update_get_skip', Map.update_get_next',
--     Map.update_get_skip, Map.update_get_next
--   ]
--   -- MLIR_states_updates

--   unfold part₃_state
--   simp? [
--     h_pre, getImpl, State.updateFelts_isGetValid, State.updateProps_isGetValid, isGetValidSkip,
--     State.updateFelts_bufferBack, State.updateProps_bufferBack, Map.update_get_skip', Map.update_get_next',
--     Map.update_get_skip, Map.update_get_next
--   ]

--   -- MLIR_states_updates

--   unfold part₄_state
--   simp? [
--     h_pre, getImpl, State.updateFelts_isGetValid, State.updateProps_isGetValid, isGetValidSkip,
--     State.updateFelts_bufferBack, State.updateProps_bufferBack, Map.update_get_skip', Map.update_get_next',
--     Map.update_get_skip, Map.update_get_next
--   ]
--   -- MLIR_states_updates

--   simp [Code.getReturn, State.constraintsInVar, State.constraints]
--   rw [←eq]

def buffersPopulated (st: State) (input is0 inv: Felt) : Prop :=
  Buffer.back st ⟨"input"⟩ 0 0 = some input ∧
  Buffer.back st ⟨"output"⟩ 0 0 = some is0 ∧
  Buffer.back st ⟨"output"⟩ 0 1 = some inv

theorem constraints_of_spec : st.Valid → (Code.run st ↔ (buffersPopulated st input is0 inv ∧ (input = 0 ∧ is0 = 1 ∨ input ≠ 0 ∧ is0 = 0 ∧ inv = input⁻¹))) := by
  intro h_valid
  apply Iff.intro
  case mpr =>
    show buffersPopulated st input is0 inv ∧ (input = 0 ∧ is0 = 1 ∨ input ≠ 0 ∧ is0 = 0 ∧ inv = input⁻¹) → Code.run st
    unfold buffersPopulated
    intro h_pre
    rw [part₀_wp]
    rw [part₁_updates_opaque]
    rw [part₂_updates_opaque]
    rw [part₃_updates_opaque]
    rw [part₄_updates_opaque]

    unfold part₀_state
    MLIR_states_updates

    unfold part₁_state
    simp? [
      getImpl, State.updateFelts_isGetValid, State.updateProps_isGetValid, isGetValidSkip,
      State.updateFelts_bufferBack, State.updateProps_bufferBack, Map.update_get_skip', Map.update_get_next',
      Map.update_get_skip, Map.update_get_next
    ]
    rewrite [h_pre.left.left]
    rewrite [h_pre.left.right.left]
    simp only [Option.get!_of_some]

    unfold part₂_state
    simp? [
      getImpl, State.updateFelts_isGetValid, State.updateProps_isGetValid, isGetValidSkip,
      State.updateFelts_bufferBack, State.updateProps_bufferBack, Map.update_get_skip', Map.update_get_next',
      Map.update_get_skip, Map.update_get_next
    ]

    unfold part₃_state
    simp? [
      getImpl, State.updateFelts_isGetValid, State.updateProps_isGetValid, isGetValidSkip,
      State.updateFelts_bufferBack, State.updateProps_bufferBack, Map.update_get_skip', Map.update_get_next',
      Map.update_get_skip, Map.update_get_next
    ]
    rewrite [h_pre.left.right.right]
    simp only [Option.get!_of_some]

    unfold part₄_state
    simp? [
      getImpl, State.updateFelts_isGetValid, State.updateProps_isGetValid, isGetValidSkip,
      State.updateFelts_bufferBack, State.updateProps_bufferBack, Map.update_get_skip', Map.update_get_next',
      Map.update_get_skip, Map.update_get_next
    ]

    unfold Code.getReturn
    unfold State.Valid at h_valid
    simp [h_valid]

    unfold State.constraintsInVar

    MLIR_states_updates
    aesop
  case mp => sorry

end Risc0.IsZero.Constraints.WP


-- Option.get! (((((st.felts[⟨"1"⟩] ←ₘ 1)[⟨"0"⟩] ←ₘ 0)[⟨"x"⟩] ←ₘ Option.get! (Buffer.back st ⟨"input"⟩ 0 0))[⟨"out[0]"⟩] ←ₘ Option.get! (Buffer.back st ⟨"output"⟩ 0 0)) ⟨"x"⟩) = 0
-- ⟨⟩ 
