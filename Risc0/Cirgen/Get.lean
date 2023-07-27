import Risc0.State.Defs
import Risc0.State.Notation
import Risc0.State.Set
import Risc0.Cirgen.Defs
import Risc0.State.BufferBack
import Risc0.Wheels

namespace Risc0

  section isGetValid
    lemma isGetValid_def :
      isGetValid st buf back offset = 
      (back ≤ st.cycle ∧
      buf ∈ st.vars ∧
      offset < st.bufferWidths[buf].get! ∧
      (Buffer.back st buf back offset).isSome) := rfl

    lemma isGetValid_set_of_ne (h : buf ≠ buf') :
      isGetValid (State.set! st buf' index x) buf back offset = 
      isGetValid st buf back offset := by
      unfold isGetValid Buffer.back Back.toNat
      simp
      rw [State.set!_bufferWidths_get_of_ne h, State.set!_buffers_get_of_ne h]
      aesop'
  end isGetValid

  section getImpl
    lemma getImpl_def : getImpl st buf back offset = 
      if isGetValid st buf back offset
      then Option.some <| Lit.Val (Buffer.back st buf back offset).get!
      else .none := rfl

    @[simp]
    lemma getImpl_updateFelts :
      getImpl (st[felts][x] ← val) buf back offset = getImpl st buf back offset := by
        aesop'
    
    @[simp]
    lemma getImpl_updateProps :
      getImpl (st[props][x] ← val) buf back offset = getImpl st buf back offset := by
        aesop'

    @[simp]
    lemma getImpl_withEqZero :
      getImpl (withEqZero x st) buf back offset = getImpl st buf back offset := by
        aesop'

    --Review: should any of these be simps?
    lemma getImpl_none_or_val : getImpl st buf back offset = .none ∨ ∃ x, getImpl st buf back offset = some (.Val x) := by
      simp [getImpl]
      aesop'

    lemma getImpl_val_of_some : getImpl st buf back offset = some lit → ∃ x, lit = .Val x := by
      have h: getImpl st buf back offset = .none ∨ ∃ x, getImpl st buf back offset = some (.Val x) := getImpl_none_or_val
      aesop'

    @[simp]
    lemma getImpl_skip_none_update : getImpl (st[name] ←ₛ .none) buf back offset = getImpl st buf back offset := by
      simp [State.update, getImpl, isGetValid, Buffer.back]

    @[simp]
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
        aesop'

    @[simp]
    lemma getImpl_dropFelts : 
      getImpl (State.dropFelts st y) buf back offset = getImpl st buf back offset := by
      unfold State.dropFelts getImpl
      aesop'

    lemma getImpl_skip_set (h : buf ≠ buf') :
      getImpl (State.set! st buf' index x) buf back offset = getImpl st buf back offset := by
      unfold getImpl Buffer.back Buffer.get! Buffer.Idx.time Buffer.Idx.data Back.toNat
      simp [isGetValid_set_of_ne h]
      rw [State.get!_set!_of_ne h]

    lemma getImpl_skip_set_offset_of_none_aux (h : st.buffers[buf] = none) : State.set! st buf a b =
                                            {st with buffers := st.buffers[buf] ←ₘ []} := by
      unfold State.set!; simp [h]
      unfold State.setBufferElementImpl; simp [Option.get!, h]
      simp [panicWithPosWithDecl, panic, panicCore, default, instInhabitedList]
      unfold Buffer.set?
      simp

    lemma getImpl_skip_set_offset_of_none (contra : st.buffers[buf] = none) :
      getImpl (State.set! st buf offset val) buf back offset' =
      getImpl st buf back offset' := by
      rw [getImpl_skip_set_offset_of_none_aux contra]
      simp [getImpl, isGetValid, Buffer.back]
      rw [contra]
      simp [Option.get!, panicWithPosWithDecl, panic, panicCore, default]

    private lemma getImpl_skip_set_offset_of_some_aux {st : State}
      (h : List.get! (List.get! buffer (List.length buffer - (1 : ℕ))) offset = some val)
      (h₁ : st.buffers buf = some buffer) :
      getImpl (State.set! st buf offset val) buf back offset' = getImpl st buf back offset' := by
        simp [
            State.set!, State.setBufferElementImpl, Buffer.set?, Buffer.getBufferAtTime!, Buffer.Idx.time, Buffer.Idx.data,
            getElem, h₁, h, Option.isEqSome
        ]
        congr
        unfold Map.update; funext z
        have : State.buffers st z = st.buffers[z] := rfl; rw [this]
        aesop'

    lemma State.set!_of_some {v : Buffer} {st : State} {buf : BufferVar}
      (h : st.buffers[buf] = some v) :
      State.set! st buf offset val =
      let bufferSet? := Buffer.set? v (List.length v - 1, offset) val
      {
        st with buffers := match bufferSet? with
                            | some b => st.buffers[buf] ←ₘ b
                            | none => st.buffers
                isFailed := if bufferSet?.isNone then True else st.isFailed
      } := by simp [set!, setBufferElementImpl, h]; aesop'

    private lemma isGetValid_congr
      (h₁ : st.buffers = st'.buffers)
      (h₂ : st.bufferWidths = st'.bufferWidths)
      (h₃ : st.cycle = st'.cycle)
      (h₄ : st.vars = st'.vars) :
      isGetValid st buf back offset = isGetValid st' buf back offset := by
      unfold isGetValid Buffer.back
      aesop'

    private lemma Buffer.isEqSome_same_or_isNone_of_set?
      (h : Buffer.set? buffer (buffer.length - 1, offset) val = some row) :
      let inner := (buffer.getBufferAtTime! (buffer.length - 1)).get! offset
      (inner = some val) ∨ inner.isNone := by
      simp only [set?, Option.isEqSome, Buffer.Idx.data, Buffer.Idx.time] at h
      split_ifs at h <;> aesop'

    private lemma buffer_eq_row_of_isEqSome
      (h : Buffer.set? buffer (buffer.length - 1, offset) val = some row)
      (h₁ : Option.isEqSome (List.get! (List.get! buffer (buffer.length - 1)) offset) val = true) :
      buffer = row := by
      simp [Buffer.set?, Buffer.getBufferAtTime!, Buffer.Idx.time, Buffer.Idx.data, h₁] at h
      exact h

    private lemma get!_set_of_nonempty {α : Type} [Inhabited α] {l : List α} {v : α}
      (h : l ≠ []) :
      List.get! (List.set l (l.length - 1) v) (l.length - 1) = v := by
      rw [List.get!_set_of_lt_length]
      cases l <;> aesop'

    private lemma get!_set_of_nonempty_ne {α : Type} [Inhabited α] {l : List α} {v : α}
      (h : l ≠ [])
      (h₁ : (l.length - 1) ≠ i') :
      List.get! (List.set l (l.length - 1) v) i' = List.get! l i' := by
      rw [List.get!_set_of_ne]; cases l <;> aesop'

    private lemma getImpl_skip_set_offset_of_some_aux' 
      (h : List.get! (List.get! buffer (List.length buffer - 1)) offset ≠ some val)
      (h₀ : offset ≠ offset')
      (h₁ : st.buffers[buf] = some buffer) :
      getImpl (State.set! st buf offset val) buf back offset' = getImpl st buf back offset' := by
        generalize eq : List.length buffer - 1 = lastIdx at *; rw [State.set!_of_some h₁]
        simp only [getImpl]
        set st₁ : State := { st
          with buffers :=
            match Buffer.set? buffer (List.length buffer - 1, offset) val with
            | some b => st.buffers[buf] ←ₘ b
            | none => st.buffers
        } with eq₁
        apply if_congr_of_and
        rw [@isGetValid_congr (st' := st₁)] <;> simp only [eq₁]
        simp only [
          isGetValid, ge_iff_le, Buffer.back_def, eq_iff_iff, and_congr_right_iff, Option.some.injEq,
          Lit.Val.injEq, and_true
        ]
        match eq₂ : Buffer.set? buffer (buffer.length - 1, offset) val with
          | none => tauto
          | some row =>
            rcases Buffer.isEqSome_same_or_isNone_of_set? eq₂ with h₂ | h₂
            · have : (List.get! (List.get! buffer (buffer.length - 1)) offset).isEqSome val := by
                unfold Buffer.getBufferAtTime! at h₂; unfold Option.isEqSome; aesop'
              have : buffer = row := buffer_eq_row_of_isEqSome eq₂ this; subst this
              simp only [
                Buffer.get!, Map.update_get, Option.get!_of_some, Buffer.Idx.time, Buffer.Idx.data, h₁
              ]
              tauto
            · rw [←eq₂]
              have : ¬(List.get! (List.get! buffer (buffer.length - 1)) offset).isEqSome val :=
                Option.not_isEqSome_of_isNone h₂
              simp only [
                Buffer.get!, Buffer.set?, Buffer.getBufferAtTime!, Buffer.Idx.time, Buffer.Idx.data, this,
                if_pos (Buffer.getBufferAtTime!_def ▸ h₂), ite_false, Map.update_get, Option.get!_of_some, h₁
              ]
              by_cases eq : buffer = []
              · subst eq; simp
              · by_cases eq₁ : List.length buffer - 1 = st.cycle - Back.toNat back
                · rw [←eq₁, get!_set_of_nonempty eq, List.get!_set_of_ne h₀]; tauto
                · rw [get!_set_of_nonempty_ne eq eq₁]; tauto

    private lemma getImpl_skip_set_offset_of_some (h : offset ≠ offset') (h₁ : st.buffers[buf].isSome) :
      getImpl (State.set! st buf offset val) buf back offset' =
      getImpl st buf back offset' := 
        (Option.isSome_iff_exists.1 h₁).casesOn λ buffer h₁ =>
          if eq₁ : (List.get! buffer (buffer.length - 1)).get! offset = some val
          then getImpl_skip_set_offset_of_some_aux eq₁ h₁
          else getImpl_skip_set_offset_of_some_aux' eq₁ h h₁

    lemma getImpl_skip_set_offset (h: offset ≠ offset') :
      getImpl (State.set! st buf offset val) buf back offset' =
      getImpl st buf back offset' := 
        if eq : Option.isNone st.buffers[buf]
        then getImpl_skip_set_offset_of_none (Option.isNone_iff_eq_none.1 eq)
        else getImpl_skip_set_offset_of_some h (Option.not_isNone_iff_isSome.1 eq)
      end getImpl

end Risc0
