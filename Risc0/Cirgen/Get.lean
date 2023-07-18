import Risc0.State.Defs
import Risc0.State.Notation
import Risc0.State.Set
import Risc0.Cirgen.Defs

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
      aesop
  end isGetValid

  section getImpl
    lemma getImpl_def : getImpl st buf back offset = 
      if isGetValid st buf back offset
      then Option.some <| Lit.Val (Buffer.back st buf back offset).get!
      else .none := rfl

    @[simp]
    lemma getImpl_updateFelts :
      getImpl (st[felts][x] ← val) buf back offset = getImpl st buf back offset := by
        aesop
    
    @[simp]
    lemma getImpl_updateProps :
      getImpl (st[props][x] ← val) buf back offset = getImpl st buf back offset := by
        aesop

    @[simp]
    lemma getImpl_withEqZero :
      getImpl (withEqZero x st) buf back offset = getImpl st buf back offset := by
        aesop

    --Review: should any of these be simps?
    lemma getImpl_none_or_val : getImpl st buf back offset = .none ∨ ∃ x, getImpl st buf back offset = some (.Val x) := by
      simp [getImpl]
      aesop

    lemma getImpl_val_of_some : getImpl st buf back offset = some lit → ∃ x, lit = .Val x := by
      have h: getImpl st buf back offset = .none ∨ ∃ x, getImpl st buf back offset = some (.Val x) := getImpl_none_or_val
      aesop

    lemma simplify_valid_get (h: ¬(st'[name] ←ₛ getImpl st buf back offset).isFailed):
      (st'[name] ←ₛ getImpl st buf back offset) = st'[felts][⟨name⟩] ← (Buffer.back st buf back offset).get! := by
        have h: getImpl st buf back offset = .none ∨ ∃ x, getImpl st buf back offset = some (.Val x) := getImpl_none_or_val
        cases h with
          | inl h_none =>
            rewrite [h_none] at h
            unfold State.update at h
            aesop
          | inr h_some =>
            unfold getImpl at h_some
            unfold getImpl
            aesop

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
        aesop

    @[simp]
    lemma getImpl_dropFelts : 
      getImpl (State.dropFelts st y) buf back offset = getImpl st buf back offset := by
      unfold State.dropFelts getImpl
      aesop

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
            getElem
        ]
        simp [h₁, h, Option.isEqSome]
        congr
        unfold Map.update; funext z
        have : State.buffers st z = st.buffers[z] := rfl; rw [this]
        aesop

    lemma List.get!_set {α : Type} [Inhabited α] {l : List α} {i : ℕ} {v : α} (h : i < l.length) :
      List.get! (List.set l i v) i = v := by
      induction l generalizing i with
        | nil => cases h
        | cons hd tl ih =>
          cases i with
            | zero => aesop
            | succ i => simp at h
                        have : i < tl.length := Nat.lt_of_succ_lt_succ h
                        rw [←ih this]
                        aesop

    lemma List.get!_set_of_ne {α : Type} [Inhabited α] {l : List α} {i i' : ℕ} {v : α}
      (h : i < l.length) (h₁ : i ≠ i') : List.get! (List.set l i v) i' = List.get! l i' := by
      induction l generalizing i i' with
        | nil => cases h
        | cons hd tl ih =>
          cases i <;> cases i' <;> aesop
          have : n < tl.length := Nat.lt_of_succ_lt_succ h
          rw [ih this h₁]

    private lemma getImpl_skip_set_offset_of_some_aux'_aux
      (h₀ : offset ≠ offset')
      (h : lastIdx = List.length buffer - (1 : ℕ))
      (h₁ : lastRow = List.get! buffer lastIdx)
      (h₂ : st.buffers[buf] = some buffer) :
      isGetValid
        { buffers := st.buffers[buf] ←ₘ List.set buffer lastIdx (List.set lastRow offset (some val)),
          bufferWidths := st.bufferWidths, constraints := st.constraints, cycle := st.cycle, felts := st.felts,
          isFailed := st.isFailed, props := st.props, vars := st.vars } buf back offset' ↔
      isGetValid st buf back offset' := by
      subst h h₁ 
      unfold isGetValid
      simp [Buffer.back, Buffer.get!, Buffer.Idx.data, Buffer.Idx.time]
      aesop <;>
        generalize eq : List.length buffer - (1 : ℕ) = lastIdx at * <;>
        generalize eq₁ : List.get! buffer lastIdx = lastRow at * <;>
        generalize eq₂ : st.cycle - Back.toNat back = cycleIdx at *
      · rw [Option.isSome_iff_exists] at a_3 ⊢
        rcases a_3 with ⟨w₃, h₃⟩; use w₃
        by_cases eq₃ : cycleIdx = lastIdx
        · subst eq₃
          rw [List.get!_set, List.get!_set_of_ne _ h₀] at h₃; rw [eq₁]; exact h₃
          sorry; sorry
        · rw [List.get!_set_of_ne _ (Ne.symm eq₃)] at h₃; exact h₃
          sorry
      · rw [Option.isSome_iff_exists] at a_3 ⊢
        rcases a_3 with ⟨w₃, h₃⟩; use w₃
        by_cases eq₃ : cycleIdx = lastIdx
        · subst eq₃
          rw [List.get!_set, List.get!_set_of_ne _ h₀]; aesop
          sorry; sorry
        · rw [List.get!_set_of_ne _ (Ne.symm eq₃)]; exact h₃
          sorry

    private lemma getImpl_skip_set_offset_of_some_aux' {st : State}
      (h₀ : offset ≠ offset')
      (h : List.get! (List.get! buffer (List.length buffer - (1 : ℕ))) offset ≠ some val)
      (h₁ : st.buffers buf = some buffer) :
      getImpl (State.set! st buf offset val) buf back offset' = getImpl st buf back offset' := by
        generalize eq : List.length buffer - (1 : ℕ) = lastIdx at *
        have : State.buffers st buf = st.buffers[buf] := rfl; rw [this] at h₁
        simp [
          State.set!, State.setBufferElementImpl, Buffer.set?, Buffer.getBufferAtTime!, Buffer.Idx.time, Buffer.Idx.data
        ]
        simp only [h₁, Option.get!_of_some, ge_iff_le, tsub_eq_zero_iff_le, eq]
        generalize eq₁ : List.get! buffer lastIdx = lastRow
        by_cases eq₂ : (List.get! lastRow offset).isNone <;> simp [eq₂]
        · have :
            Option.isEqSome (List.get! lastRow offset) val = false := by
            simp [Option.isEqSome]
            generalize eq₃ : List.get! lastRow offset = elem at *
            aesop
          simp only [this, ite_false]
          unfold getImpl
          congr 1
          · rw [getImpl_skip_set_offset_of_some_aux'_aux h₀] <;> simp [*]
          · simp [Buffer.back, Buffer.get!, Buffer.Idx.time, Buffer.Idx.data, h₁]
            generalize eq₃ : st.cycle - Back.toNat back = cycleIdx
            by_cases eq₄ : cycleIdx = lastIdx
            · subst eq₄
              rw [List.get!_set, List.get!_set_of_ne _ h₀, ←eq₁]
              sorry; sorry
            · rw [List.get!_set_of_ne _ (Ne.symm eq₄)]
              sorry
        · have :
            Option.isEqSome (List.get! lastRow offset) val = false := by
            simp [Option.isEqSome]
            generalize eq₃ : List.get! lastRow offset = elem at *
            aesop
          simp [this]
          rfl

    lemma getImpl_skip_set_offset_of_some (h : offset ≠ offset') (h₁ : st.buffers[buf].isSome) :
      getImpl (State.set! st buf offset val) buf back offset' =
      getImpl st buf back offset' := by
        rw [Option.isSome_iff_exists] at h₁
        rcases h₁ with ⟨buffer, h₁⟩
        let lastIdx := buffer.length - 1
        by_cases eq₁ : List.get! (List.get! buffer lastIdx) offset = val
        · exact getImpl_skip_set_offset_of_some_aux eq₁ h₁
        · exact getImpl_skip_set_offset_of_some_aux' h eq₁ h₁

    lemma getImpl_skip_set_offset (h: offset ≠ offset') :
      getImpl (State.set! st buf offset val) buf back offset' =
      getImpl st buf back offset' := by
      by_cases eq : st.buffers[buf].isNone
      · rw [Option.isNone_iff_eq_none] at eq
        rw [getImpl_skip_set_offset_of_none eq]
      · have : st.buffers[buf].isSome := by
          rwa [Option.isNone_iff_eq_none, ←ne_eq, Option.ne_none_iff_isSome] at eq
        rw [getImpl_skip_set_offset_of_some h this]
  end getImpl


end Risc0
