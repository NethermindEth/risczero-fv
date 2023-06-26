import Risc0.Gadgets.OneHot.Witness.Code
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart0
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart8

namespace Risc0.OneHot.Witness.WP

def start_state (input: Felt) : State :=
  { buffers := Map.fromList [(⟨"input"⟩, [[.some input]]), (⟨"output"⟩, [[none, none, none]])]
  , bufferWidths := Map.fromList [(⟨"input"⟩, 1), (⟨"output"⟩, 3)]
  , constraints := []
  , cycle := 0
  , felts := Map.empty
  , props := Map.empty
  , vars := [⟨"input"⟩, ⟨"output"⟩]
  , isFailed := false
  }


-- def start_state (input: Felt) (st: State) :=
--   st.WellFormed ∧
--   ⟨"input"⟩ ∈ st.vars ∧
--   ⟨"output"⟩ ∈ st.vars ∧
--   State.bufferWidths st { name := "input" } = some 1 ∧
--   st.bufferWidths[(⟨"output"⟩ : BufferVar)] = some 3 ∧
--   (State.buffers st (⟨"input"⟩ : BufferVar)).isSome = true ∧
--   (State.buffers st (⟨"input"⟩ : BufferVar)).get!.last! = [some input] ∧
--   List.get! (State.buffers st (⟨"input"⟩ : BufferVar)).get! st.cycle = [some input] ∧
--   (st.buffers[(⟨"output"⟩ : BufferVar)]).get!.last! = [none, none, none]
  -- (st.buffers[(⟨"output"⟩ : BufferVar)]).get

-- lemma temp (h: st.bufferWidths[({ name := "input" } : BufferVar)]! = some 1) : State.bufferWidths st { name := "input" } = some 1 := by
--   exact h

-- lemma temp2 {width : ℕ} (h: st.bufferWidths[({ name := "input" } : BufferVar)]! = some width) (hw: width > 0) : (0 <
--     match State.bufferWidths st { name := "input" } with
--     | some x => x
--     | none => panicWithPosWithDecl "Init.Data.Option.BasicAux" "Option.get!" 16 14 "value is none") := by
--   simp? [getElem!_impl_getElem, h, hw]
--   have h1: State.bufferWidths st { name := "input"} = some width := h

lemma get_from_pre (input : Felt) (st: State) (h_pre: start_state input st) :
  0 ≤ st.cycle ∧
    { name := "input" } ∈ st.vars ∧
      (0 <
          match State.bufferWidths st { name := "input" } with
          | some x => x
          | none =>
            panicWithPosWithDecl "Init.Data.Option.BasicAux" "Option.get!" 16 14
              "value is none") ∧
        Option.isSome
            (List.get!
              (List.get!
                (match State.buffers st { name := "input" } with
                | some x => x
                | none =>
                  panicWithPosWithDecl "Init.Data.Option.BasicAux" "Option.get!" 16 14
                    "value is none")
                (Buffer.Idx.time (st.cycle - Back.toNat 0, 0)))
              (Buffer.Idx.data (st.cycle - Back.toNat 0, 0))) =
          true := by
  unfold start_state at h_pre
  simp [zero_le, ge_iff_le, forall_true_left, true_and, h_pre, Map.getElem_def, Buffer.Idx.time, Buffer.Idx.data, Back.toNat]
  sorry
  
  -- MLIR_states_updates
  -- rewrite [h_pre.right.right.right.left]
  

lemma closed_form {st: State} {input: Felt} {output₀ output₁ output₂ : Option Felt} :
  (
    Code.run (start_state input) = [output₀, output₁, output₂] ↔ sorry
  ) := by
  rewrite [part₀_wp]
  rewrite [part₁_updates_opaque]
  rewrite [part₂_updates_opaque]
  rewrite [part₃_updates_opaque]
  rewrite [part₄_updates_opaque]
  rewrite [part₅_updates_opaque]
  rewrite [part₆_updates_opaque]
  rewrite [part₇_updates_opaque]
  rewrite [part₈_updates_opaque]
  unfold start_state

  unfold part₀_state
  MLIR_states_updates
  simp [zero_le, ge_iff_le, forall_true_left, true_and, Map.getElem_def, Buffer.Idx.time, Buffer.Idx.data, Back.toNat]
  
  unfold part₁_state
  MLIR_states_updates
  simp [zero_le, ge_iff_le, forall_true_left, true_and, Map.getElem_def, Buffer.Idx.time, Buffer.Idx.data, Back.toNat]

  -- by_cases eq: input = 0
  -- subst eq
  -- simp only [ite_true, zero_sub, ite_false]

  -- -- simp only [forall_true_left, ge_iff_le]
  -- -- simp

  unfold part₂_state
  simp only [State.updateFelts_felts, Map.update_get!, Option.get!_of_some]
  MLIR_states_updates
  -- -- 
  -- -- subst eq

  unfold part₃_state
  -- simp [zero_le, ge_iff_le, forall_true_left, true_and, Map.getElem_def, Buffer.Idx.time, Buffer.Idx.data, Back.toNat]
  MLIR_states_updates

  unfold part₄_state
  MLIR_states_updates

  -- unfold part₅_state
  -- MLIR_states_updates

  -- simp [State.lastOutput, Option.get!, List.getLast!, List.getLast, State.buffers]
  -- MLIR_states_updates
  -- simp [List.getLast]

end Risc0.OneHot.Witness.WP
