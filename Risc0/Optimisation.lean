import Risc0.Cirgen
import Risc0.Lemmas
import Risc0.MlirTactics

namespace Risc0

section Reordering

open MLIRNotation

open State in
lemma updateFelts_neq_comm {st : State} {name name' : FeltVar} {v v' : Felt} (h : name ≠ name') :
  (updateFelts (updateFelts st name v) name' v') =
  (updateFelts (updateFelts st name' v') name v) := by
  unfold updateFelts
  simp
  rw [Map.update_neq_comm]
  exact h

-- lemma opt_swap_seq (h: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧) :
--   Γ st ⟦p₁; p₂⟧ = Γ st ⟦p₂; p₁⟧ := by
--     rw [MLIR.run_seq_def, h, ←MLIR.run_seq_def]

-- lemma opt_swap_seq_combined
--   (h1: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧)
--   (h2: Γ (Γ st ⟦p₁⟧) ⟦p₃⟧ = Γ (Γ st ⟦p₃⟧) ⟦p₁⟧) :
--   Γ (Γ st ⟦p₁⟧) ⟦p₂; p₃⟧ = Γ (Γ (Γ st ⟦p₂⟧) ⟦p₃⟧) ⟦p₁⟧

-- lemma opt_sec_combined
--   (h1: Γ st ⟦p₁; p₂; p₃; p₄⟧ = Γ ( Γ st ⟦p₂⟧) ⟦p₁; p₃; p₄⟧)
--   (h2: Γ ( Γ st ⟦p₂⟧) ⟦p₁; p₃; p₄⟧ = Γ ( Γ ( Γ st ⟦p₂⟧) ⟦p₃⟧) ⟦p₁; p₄⟧) :
--   Γ st ⟦p₁; p₂; p₃; p₄⟧ = Γ ( Γ ( Γ st ⟦p₂⟧) ⟦p₃⟧) ⟦p₁; p₄⟧ := by
--     rw [h1, h2]

lemma opt_swap (h: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧) :
  Γ st ⟦p₁; p₂; p₃⟧ = Γ ( Γ st ⟦p₂⟧) ⟦p₁; p₃⟧ := by
    simp [MLIR.run_seq_def, h]

lemma opt_swap_nondet_single (h: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧) :
  Γ st ⟦p₁; nondet p₂; p₃⟧ = Γ ( Γ st ⟦p₂⟧) ⟦p₁; p₃⟧ := by
    simp [MLIR.run_seq_def, MLIR.run_nondet, h]

lemma opt_swap_nondet_seq (h: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧) :
  Γ st ⟦p₁; nondet (p₂; p₃); p₄⟧ = Γ ( Γ st ⟦p₂⟧) ⟦p₁; nondet p₃; p₄⟧ := by
    simp [MLIR.run_seq_def, MLIR.run_nondet, h]

lemma opt_seq
  (h1: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧)
  (h2: Γ (Γ (Γ st ⟦p₂⟧) ⟦p₁⟧) ⟦p₃⟧ = Γ (Γ (Γ st ⟦p₂⟧) ⟦p₃⟧) ⟦p₁⟧) :
  Γ (Γ st ⟦p₁⟧) ⟦p₂; p₃⟧ = Γ (Γ st ⟦p₂; p₃⟧) ⟦p₁⟧ := by
    rw [MLIR.run_seq_def, MLIR.run_seq_def, h1, h2]

lemma opt_nondet (h: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧) :
  Γ (Γ st ⟦p₁⟧) ⟦nondet p₂⟧ = Γ (Γ st ⟦nondet p₂⟧) ⟦p₁⟧ := by
    rw [MLIR.run_nondet, MLIR.run_nondet, h]

section add
  lemma add_past_const (h: a ≠ b) (h': ⟨b⟩ ≠ c) (h'': ⟨b⟩ ≠ d):
    Γ (Γ st ⟦@MLIR.Assign α a (Op.Add c d)⟧) ⟦@MLIR.Assign β b (Op.Const x)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β b (Op.Const x)⟧) ⟦@MLIR.Assign α a (Op.Add c d)⟧ := by
      simp [MLIR.run_ass_def]
      rewrite [updateFelts_neq_comm] <;> aesop'

  lemma add_past_drop (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) (h₂ : ⟨name'⟩ ≠ rhs) :
    Γ (Γ st ⟦@MLIR.Assign α name (Op.Add lhs rhs)⟧) ⟦@MLIR.DropFelt β ⟨name'⟩⟧ =
    Γ (Γ st ⟦@MLIR.DropFelt β ⟨name'⟩⟧) ⟦@MLIR.Assign α name (Op.Add lhs rhs)⟧ := by
      simp [MLIR.run_ass_def, MLIR.run_dropfelt]
      aesop'
end add

section andCond
  lemma andCond_past_const (h: ⟨b⟩ ≠ c):
    Γ (Γ st ⟦@MLIR.Assign α a (Op.AndCond outer c inner)⟧) ⟦@MLIR.Assign β b (Op.Const x)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β b (Op.Const x)⟧) ⟦@MLIR.Assign α a (Op.AndCond outer c inner)⟧ := by
      simp [MLIR.run_ass_def, h]
      aesop'
  
  lemma andCond_past_drop (h: c ≠ b):
    Γ (Γ st ⟦@MLIR.Assign α a (Op.AndCond outer c inner)⟧) ⟦@MLIR.DropFelt β b⟧ =
    Γ (Γ st ⟦@MLIR.DropFelt β b⟧) ⟦@MLIR.Assign α a (Op.AndCond outer c inner)⟧ := by
      simp [MLIR.run_ass_def, MLIR.run_dropfelt, h.symm]
      aesop'
end andCond

section andeqz
  lemma andEqz_past_const (h: ⟨b⟩ ≠ d):
    Γ (Γ st ⟦@MLIR.Assign α a (Op.AndEqz c d)⟧) ⟦@MLIR.Assign β b (Op.Const x)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β b (Op.Const x)⟧) ⟦@MLIR.Assign α a (Op.AndEqz c d)⟧ := by
      simp [MLIR.run_ass_def, State.updateFelts, State.updateProps, *, Map.update]
      aesop'
  
  lemma andEqz_past_drop (h : rhs ≠ y) :
    Γ (Γ st ⟦@MLIR.Assign β x (Op.AndEqz lhs rhs)⟧) ⟦@MLIR.DropFelt α y⟧ =
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Assign β x (Op.AndEqz lhs rhs)⟧ := by
      simp [
        MLIR.run_ass_def, MLIR.run_dropfelt, State.updateFelts, State.updateProps, Map.update,
        State.dropFelts, Map.drop
      ]
      aesop'
end andeqz

section bitand
  lemma bitAnd_past_const (h: a ≠ b) (h': ⟨b⟩ ≠ c) (h'': ⟨b⟩ ≠ d):
    Γ (Γ st ⟦@MLIR.Assign α a (Op.BitAnd c d)⟧) ⟦@MLIR.Assign β b (Op.Const x)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β b (Op.Const x)⟧) ⟦@MLIR.Assign α a (Op.BitAnd c d)⟧ := by
      simp [MLIR.run_ass_def]
      rewrite [updateFelts_neq_comm] <;> aesop'

  lemma bitAnd_past_drop (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) (h₂ : ⟨name'⟩ ≠ rhs):
    Γ (Γ st ⟦@MLIR.Assign α name (Op.BitAnd lhs rhs)⟧) ⟦@MLIR.DropFelt β ⟨name'⟩⟧ =
    Γ (Γ st ⟦@MLIR.DropFelt β ⟨name'⟩⟧) ⟦@MLIR.Assign α name (Op.BitAnd lhs rhs)⟧ := by
      simp [MLIR.run_ass_def, MLIR.run_dropfelt]
      aesop'
end bitand

section const
  lemma const_past_add (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
    Γ (Γ st ⟦@MLIR.Assign α a (Op.Const x)⟧) ⟦@MLIR.Assign β b (Op.Add c d)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β b (Op.Add c d)⟧) ⟦@MLIR.Assign α a (Op.Const x)⟧ := by
      rw [add_past_const] <;> aesop'
  
  lemma const_past_andCond (h: ⟨b⟩ ≠ c):
    Γ (Γ st ⟦@MLIR.Assign β b (Op.Const x)⟧) ⟦@MLIR.Assign α a (Op.AndCond outer c inner)⟧ =
    Γ (Γ st ⟦@MLIR.Assign α a (Op.AndCond outer c inner)⟧) ⟦@MLIR.Assign β b (Op.Const x)⟧ := by
      rw [andCond_past_const]; aesop'
  
  lemma const_past_andEqz (h: ⟨b⟩ ≠ d):
    Γ (Γ st ⟦@MLIR.Assign β b (Op.Const x)⟧) ⟦@MLIR.Assign α a (Op.AndEqz c d)⟧ =
    Γ (Γ st ⟦@MLIR.Assign α a (Op.AndEqz c d)⟧) ⟦@MLIR.Assign β b (Op.Const x)⟧ := by
      rw [andEqz_past_const]
      aesop'

  lemma const_past_bitAnd (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
    Γ (Γ st ⟦@MLIR.Assign α a (Op.Const x)⟧) ⟦@MLIR.Assign β b (Op.BitAnd c d)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β b (Op.BitAnd c d)⟧) ⟦@MLIR.Assign α a (Op.Const x)⟧ := by
      rw [bitAnd_past_const] <;> aesop'

  lemma const_past_const (h: x ≠ y):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Const c₁)⟧) ⟦@MLIR.Assign β y (Op.Const c₂)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.Const c₂)⟧) ⟦@MLIR.Assign α x (Op.Const c₁)⟧ := by
      simp [MLIR.run_ass_def]
      rewrite [updateFelts_neq_comm] <;> aesop'

  lemma const_past_drop (h : name ≠ name') :
    Γ (Γ st ⟦@MLIR.Assign α name (Op.Const x)⟧) ⟦@MLIR.DropFelt β ⟨name'⟩⟧ =
    Γ (Γ st ⟦@MLIR.DropFelt β ⟨name'⟩⟧) ⟦@MLIR.Assign α name (Op.Const x)⟧ := by
      simp [MLIR.run_ass_def, MLIR.run_dropfelt]
      aesop'
  
  lemma const_past_eqz (h : ⟨name⟩ ≠ y):
    Γ (Γ st ⟦@MLIR.Assign α name (Op.Const x)⟧) ⟦@MLIR.Eqz β y⟧ =
    Γ (Γ st ⟦@MLIR.Eqz β y⟧) ⟦@MLIR.Assign α name (Op.Const x)⟧ := by
      simp [MLIR.run_ass_def, MLIR.run_eqz, withEqZero_updateFelts, *]

  lemma const_past_get (h: x ≠ y):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Const c₁)⟧) ⟦@MLIR.Assign β y (Op.Get buf back offset)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.Get buf back offset)⟧) ⟦@MLIR.Assign α x (Op.Const c₁)⟧ := by
      simp [MLIR.run_ass_def]
      aesop'
      rewrite [updateFelts_neq_comm] <;> simp [*]
  
  lemma const_past_if {branch: MLIR β}
    (h: ⟨x⟩ ≠ y)
    (h_branch: Γ (Γ st ⟦@MLIR.Assign α x (Op.Const c)⟧) ⟦branch⟧ = Γ (Γ st ⟦branch⟧) ⟦@MLIR.Assign α x (Op.Const c)⟧):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Const c)⟧) ⟦@MLIR.If β y branch⟧ =
    Γ (Γ st ⟦@MLIR.If β y branch⟧) ⟦@MLIR.Assign α x (Op.Const c)⟧ := by
      simp [MLIR.run_if, MLIR.run_ass_def, h, State.dropFelts_felts, getElem!, getElem, Map.drop_get]
      aesop'
  
  lemma const_past_inv (h: x ≠ y) (h': ⟨x⟩ ≠ z):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Const c)⟧) ⟦@MLIR.Assign .InNondet y (Op.Inv z)⟧ =
    Γ (Γ st ⟦@MLIR.Assign .InNondet y (Op.Inv z)⟧) ⟦@MLIR.Assign α x (Op.Const c)⟧ := by
      simp [MLIR.run_ass_def]
      rewrite [updateFelts_neq_comm]
      simp [State.updateFelts, Map.update_get_next, h']
      aesop'

  lemma const_past_isz (h: name ≠ name') (h': ⟨name⟩ ≠ y):
    Γ (Γ st ⟦@MLIR.Assign α name (Op.Const x)⟧) ⟦MLIR.Assign name' (Op.Isz y)⟧ =
    Γ (Γ st ⟦MLIR.Assign name' (Op.Isz y)⟧) ⟦@MLIR.Assign α name (Op.Const x)⟧ := by
      simp [MLIR.run_ass_def, State.updateFelts, Map.update_get_next', *]
      rw [Map.update_neq_comm]
      simp [h]

  lemma const_past_mul (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
    Γ (Γ st ⟦@MLIR.Assign α a (Op.Const x)⟧) ⟦@MLIR.Assign β b (Op.Mul c d)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β b (Op.Mul c d)⟧) ⟦@MLIR.Assign α a (Op.Const x)⟧ := by
      simp [MLIR.run_ass_def]
      rewrite [updateFelts_neq_comm] <;> simp [*]

  lemma const_past_set (h: ⟨a⟩ ≠ b) :
    Γ (Γ st ⟦@MLIR.Assign α a (Op.Const x)⟧) ⟦@MLIR.Set buf offset b⟧ =
    Γ (Γ st ⟦@MLIR.Set buf offset b⟧) ⟦@MLIR.Assign α a (Op.Const x)⟧ := by
      simp [MLIR.run_ass_def, MLIR.run_set_def, State.set!, State.setBufferElementImpl]
      aesop'

  lemma const_past_sub (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
    Γ (Γ st ⟦@MLIR.Assign α a (Op.Const x)⟧) ⟦@MLIR.Assign β b (Op.Sub c d)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β b (Op.Sub c d)⟧) ⟦@MLIR.Assign α a (Op.Const x)⟧ := by
      simp [MLIR.run_ass_def]
      rewrite [updateFelts_neq_comm] <;> aesop'
  
  lemma const_past_true (h: a ≠ b) :
    Γ (Γ st ⟦@MLIR.Assign α a (Op.Const x)⟧) ⟦@MLIR.Assign β b (Op.True)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β b (Op.True)⟧) ⟦@MLIR.Assign α a (Op.Const x)⟧ := by
      simp [MLIR.run_ass_def]
      aesop'

end const

section drop

  lemma drop_past_add (h : ⟨x⟩ ≠ y) (h₁ : lhs ≠ y) (h₂ : rhs ≠ y) :
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Assign β x (Op.Add lhs rhs)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β x (Op.Add lhs rhs)⟧) ⟦@MLIR.DropFelt α y⟧ := by
      rw [add_past_drop] <;> aesop'

  lemma drop_past_andCond (h: c ≠ b):
    Γ (Γ st ⟦@MLIR.DropFelt β b⟧) ⟦@MLIR.Assign α a (Op.AndCond outer c inner)⟧ =
    Γ (Γ st ⟦@MLIR.Assign α a (Op.AndCond outer c inner)⟧) ⟦@MLIR.DropFelt β b⟧ := by
      rw [andCond_past_drop h]

  lemma drop_past_andEqz (h : rhs ≠ y) :
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Assign β x (Op.AndEqz lhs rhs)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β x (Op.AndEqz lhs rhs)⟧) ⟦@MLIR.DropFelt α y⟧ := by
      rw [andEqz_past_drop]; aesop'

  lemma drop_past_bitAnd (h : ⟨x⟩ ≠ y) (h₁ : lhs ≠ y) (h₂ : rhs ≠ y):
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Assign β x (Op.BitAnd lhs rhs)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β x (Op.BitAnd lhs rhs)⟧) ⟦@MLIR.DropFelt α y⟧ := by
      rw [bitAnd_past_drop] <;> aesop'

  lemma drop_past_const (h : ⟨x⟩ ≠ y) :
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Assign β x (Op.Const c)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β x (Op.Const c)⟧) ⟦@MLIR.DropFelt α y⟧ := by
      rw [const_past_drop]; aesop'

  lemma drop_past_eqz (h : x ≠ y) :
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Eqz β x⟧ =
    Γ (Γ st ⟦@MLIR.Eqz β x⟧) ⟦@MLIR.DropFelt α y⟧ := by
      simp [MLIR.run_dropfelt, MLIR.run_eqz, withEqZero, State.dropFelts, Map.drop, getElem!, Map.getElem_def]
      aesop'

  lemma drop_past_get (h: ⟨x⟩ ≠ y) :
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Assign β x (Op.Get buf back offset)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β x (Op.Get buf back offset)⟧) ⟦@MLIR.DropFelt α y⟧ := by
      simp [MLIR.run_dropfelt, MLIR.run_ass_def]
      MLIR
      exact State.dropFelts_update_of_ne h

  lemma drop_past_if {branch: MLIR β}
    (h: y ≠ x)
    (h_branch: Γ (Γ st ⟦@MLIR.DropFelt α x⟧) ⟦branch⟧ = Γ (Γ st ⟦branch⟧) ⟦@MLIR.DropFelt α x⟧):
    Γ (Γ st ⟦@MLIR.DropFelt α x⟧) ⟦@MLIR.If β y branch⟧ =
    Γ (Γ st ⟦@MLIR.If β y branch⟧) ⟦@MLIR.DropFelt α x⟧ := by
      simp [MLIR.run_if, MLIR.run_dropfelt, h.symm, State.dropFelts_felts, getElem!, getElem, Map.drop_get]
      aesop'

  lemma drop_past_isz (h: ⟨name⟩ ≠ y) (h': x ≠ y):
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦MLIR.Assign name (Op.Isz x)⟧ =
    Γ (Γ st ⟦MLIR.Assign name (Op.Isz x)⟧) ⟦@MLIR.DropFelt α y⟧ := by
      simp [
        MLIR.run_dropfelt, MLIR.run_ass_def, State.updateFelts, Map.update_get_next', *,
        State.dropFelts_buffers, State.dropFelts_bufferWidths, State.dropFelts_constraints, State.dropFelts_cycle,
        State.dropFelts_felts, State.dropFelts_isFailed, State.dropFelts_props, State.dropFelts_vars, State.dropFelts,
        Map.update_drop_swap, Map.drop_get, Map.drop, Map.update
      ]
      funext z
      aesop'
  
  -- lemma drop_past_if (h : y ≠ x) (h₁ : Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦prog⟧ = Γ (Γ st ⟦prog⟧) ⟦@MLIR.DropFelt α y⟧) :
  --   Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.If β x prog⟧ =
  --   Γ (Γ st ⟦@MLIR.If β x prog⟧) ⟦@MLIR.DropFelt α y⟧ := by
  --     simp [MLIR.run_dropfelt, MLIR.run_if]
  --     simp [getElem!, State.get_dropFelts_of_ne h]
      
  --     -- MLIR
  --     -- aesop'; aesop'
  --     -- rw [Map.not_mem_iff_none, Map.getElem_def] at h₁
  --     -- unfold State.dropFelts Map.drop
  --     -- congr
  --     -- funext z
  --     -- aesop'

  lemma drop_past_mul (h : ⟨x⟩ ≠ y) (h₁ : lhs ≠ y) (h₂ : rhs ≠ y) :
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Assign β x (Op.Mul lhs rhs)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β x (Op.Mul lhs rhs)⟧) ⟦@MLIR.DropFelt α y⟧ := by
      simp [MLIR.run_dropfelt, MLIR.run_ass_def, State.dropFelts, State.updateFelts, Map.drop_get h₂.symm , Map.drop_get h₁.symm, Map.update_drop_swap, *]
  
  lemma drop_past_set (h : val ≠ y) :
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Set buf offset val⟧ =
    Γ (Γ st ⟦@MLIR.Set buf offset val⟧) ⟦@MLIR.DropFelt α y⟧ := by
      simp [MLIR.run_dropfelt, MLIR.run_set_def]
      MLIR; simp only [getElem!, dite_true, ne_eq]
      rw [State.get_dropFelts_of_ne h.symm]
      unfold State.dropFelts Map.drop
      simp only [
        State.set!_felts, State.set!, State.setBufferElementImpl, Buffer.set?,
        Buffer.getBufferAtTime!, Buffer.Idx.time, Buffer.Idx.data
      ]
      aesop'

  lemma drop_past_sub (h : ⟨x⟩ ≠ y) (h₁ : lhs ≠ y) (h₂ : rhs ≠ y) :
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Assign β x (Op.Sub lhs rhs)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β x (Op.Sub lhs rhs)⟧) ⟦@MLIR.DropFelt α y⟧ := by
      simp [MLIR.run_dropfelt, MLIR.run_ass_def]
      simp [State.drop_update_swap, h]
      unfold State.dropFelts Map.drop State.updateFelts
      aesop'

end drop

section get
  lemma get_past_add (h: x ≠ y) (hl: ⟨x⟩ ≠ l) (hr: ⟨x⟩ ≠ r):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Assign β y (Op.Add l r)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.Add l r)⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
      simp only [MLIR.run_ass_def, Op.eval, *]
      generalize eq: getImpl st buf back offset = get
      cases get with
        | none => aesop'
        | some lit =>
          have h_lit: ∃ k, lit = Lit.Val k := getImpl_val_of_some eq
          aesop'
          rewrite [updateFelts_neq_comm (by aesop')]
          rfl
    
  lemma get_past_andEqz (h: x ≠ y) (hl: ⟨x⟩ ≠ l) (hr: ⟨x⟩ ≠ r):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Assign β y (Op.AndEqz l r)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.AndEqz l r)⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
      simp only [MLIR.run_ass_def, Op.eval, *]
      generalize eq: getImpl st buf back offset = get
      cases get with
        | none => aesop'
        | some lit =>
          have h_lit: ∃ k, lit = Lit.Val k := getImpl_val_of_some eq
          aesop'

  lemma get_past_bitAnd (h: x ≠ y) (hl: ⟨x⟩ ≠ l) (hr: ⟨x⟩ ≠ r):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Assign β y (Op.BitAnd l r)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.BitAnd l r)⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
      simp only [MLIR.run_ass_def, Op.eval, *]
      generalize eq: getImpl st buf back offset = get
      cases get with
        | none => aesop'
        | some lit =>
          have h_lit: ∃ k, lit = Lit.Val k := getImpl_val_of_some eq
          aesop'
          rw [updateFelts_neq_comm (by aesop')]

  lemma get_past_const (h: x ≠ y) :
  Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Assign β y (Op.Const c)⟧ =
  Γ (Γ st ⟦@MLIR.Assign β y (Op.Const c)⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
    rewrite [const_past_get] <;> aesop'
    

  -- lemma get_past_drop (h: ⟨x⟩ ≠ y) :
  -- Γ st ⟦@MLIR.Assign x .Get buf back offset⟧) ⟦dropfelt y⟧ =
  -- Γ st ⟦dropfelt y⟧) ⟦@MLIR.Assign x .Get buf back offset⟧ := by
  --   MLIR
  --   generalize eq: getImpl st buf back offset = get
  --   cases get with
  --     | none => aesop'
  --     | some lit =>
  --       have h_lit: ∃ k, lit = Lit.Val k := getImpl_val_of_some eq
  --       aesop'


  lemma get_past_get_buf (h: buf ≠ buf') (h': x ≠ y) :
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Assign β y (Op.Get buf' back' offset')⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.Get buf' back' offset')⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
      simp only [MLIR.run_ass_def, Op.eval, *, getImpl_skip_get_update]
      generalize eq1: getImpl st buf back offset = get1
      generalize eq2: getImpl st buf' back' offset' = get2
      cases get1 with
        | none => simp [State.update]; aesop'
        | some lit1 =>
          have h1: ∃ k1, lit1 = Lit.Val k1 := getImpl_val_of_some eq1
          cases get2 with
            | none => aesop'
            | some lit2 =>
              have h2: ∃ k2, lit2 = Lit.Val k2 := getImpl_val_of_some eq2
              aesop'
              rw [updateFelts_neq_comm (by aesop')]

  lemma get_past_get_offset (h: offset ≠ offset') (h': x ≠ y) :
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Assign β y (Op.Get buf' back' offset')⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.Get buf' back' offset')⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
      simp only [MLIR.run_ass_def, Op.eval, getImpl_skip_get_update]
      unfold getImpl; aesop'
      unfold State.updateFelts; aesop'
      unfold Map.update; funext z; aesop'

  lemma get_past_mul (h: x ≠ y) (hl: ⟨x⟩ ≠ l) (hr: ⟨x⟩ ≠ r):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Assign β y (Op.Mul l r)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.Mul l r)⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
      simp only [MLIR.run_ass_def, Op.eval, *]
      generalize eq: getImpl st buf back offset = get
      cases get with
        | none => aesop'
        | some lit =>
          have h_lit: ∃ k, lit = Lit.Val k := getImpl_val_of_some eq
          aesop'
          rewrite [updateFelts_neq_comm (by aesop')]
          rfl

  lemma get_past_set_buf (h: ⟨x⟩ ≠ val) (h': buf' ≠ buf):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Set buf' index val⟧ =
    Γ (Γ st ⟦@MLIR.Set buf' index val⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
      simp [MLIR.run_ass_def, MLIR.run_set_def, Op.eval, getImpl_skip_get_update, getElem!]
      generalize eq : getImpl st buf back offset = get; simp only [getElem]
      rw [State.update_skip_felts (by aesop'),
         ←@Map.getElem_def _ _ (State.felts st),
         getImpl_skip_set (Ne.symm h'),
         eq]
      generalize eq₁ : Option.get! st.felts[{ name := val.name : FeltVar }] = y
      rw [←eq]
      exact State.set!_get_getImpl_comm

  lemma get_past_sub (h: x ≠ y) (hl: ⟨x⟩ ≠ l) (hr: ⟨x⟩ ≠ r):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Assign β y (Op.Sub l r)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.Sub l r)⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
      simp only [MLIR.run_ass_def, Op.eval, *]
      generalize eq: getImpl st buf back offset = get
      cases get with
        | none => aesop'
        | some lit =>
          have h_lit: ∃ k, lit = Lit.Val k := getImpl_val_of_some eq
          aesop'
          rewrite [updateFelts_neq_comm (by aesop')]
          rfl

end get

section If

end If

section inv
  -- lemma drop_assign_inv_swap (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) :
  --   Γ (Γ st ⟦@MLIR.Assign name .Inv lhs⟧) ⟦dropfelt ⟨name'⟩⟧ =
  --   Γ (Γ st ⟦dropfelt ⟨name'⟩⟧) ⟦@MLIR.Assign name .Inv lhs⟧ := by
  --     MLIR
  --     simp [State.drop_update_swap, h, State.get_dropFelts_of_ne h₁]
end inv

section isz
  -- lemma drop_assign_isz_swap (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) :
  --   Γ (Γ st ⟦@MLIR.Assign name .Isz lhs⟧) ⟦dropfelt ⟨name'⟩⟧ =
  --   Γ (Γ st ⟦dropfelt ⟨name'⟩⟧) ⟦@MLIR.Assign name .Isz lhs⟧ := by
  --     MLIR
  --     simp [State.drop_update_swap, h]
  --     unfold State.dropFelts Map.drop State.updateFelts
  --     aesop'
end isz

section mul
  -- lemma mul_past_drop (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) (h₂ : ⟨name'⟩ ≠ rhs):
  --   Γ (Γ st ⟦@MLIR.Assign name .Mul lhs rhs⟧) ⟦@MLIR.DropFelt α ⟨name'⟩⟧ =
  --   Γ (Γ st ⟦@MLIR.DropFelt α ⟨name'⟩⟧) ⟦@MLIR.Assign name .Mul lhs rhs⟧ := by
  --     MLIR
  --     simp [State.drop_update_swap, h]
  --     unfold State.dropFelts Map.drop State.updateFelts
  --     aesop'
end mul

section neg
  -- lemma neg_past_drop (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs):
  --   Γ (Γ st ⟦@MLIR.Assign name .Neg lhs⟧) ⟦@MLIR.DropFelt α ⟨name'⟩⟧ =
  --   Γ (Γ st ⟦@MLIR.DropFelt α ⟨name'⟩⟧) ⟦@MLIR.Assign name .Neg lhs⟧ := by
  --     MLIR
  --     simp [State.drop_update_swap, h]
  --     unfold State.dropFelts Map.drop
  --     aesop'
end neg

section pow
  -- lemma drop_assign_pow_swap {n : ℕ} (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) :
  --   Γ (Γ st ⟦@MLIR.Assign name .Pow lhs n⟧) ⟦@MLIR.DropFelt α ⟨name'⟩⟧ =
  --   Γ (Γ st ⟦@MLIR.DropFelt α ⟨name'⟩⟧) ⟦@MLIR.Assign name .Pow lhs n⟧ := by
  --     MLIR
  --     simp [State.drop_update_swap, h, State.get_dropFelts_of_ne' h₁]
end pow

section sub
  -- lemma sub_past_drop (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) (h₂ : ⟨name'⟩ ≠ rhs):
  --   Γ (Γ st ⟦@MLIR.Assign name .Sub lhs rhs⟧) ⟦@MLIR.DropFelt α ⟨name'⟩⟧ =
  --   Γ (Γ st ⟦@MLIR.DropFelt α ⟨name'⟩⟧) ⟦@MLIR.Assign name .Sub lhs rhs⟧ := by
  --     MLIR
  --     simp [State.drop_update_swap, h]
  --     unfold State.dropFelts Map.drop State.updateFelts
  --     aesop'
end sub

section true
  -- lemma drop_assign_true_swap {α : IsNondet} {name name' : String} {x : Felt}
  --   (h : name ≠ name') :
  --   Γ st ⟦@MLIR.Assign name ⊤⟧) ⟦@MLIR.DropFelt α ⟨name'⟩⟧ =
  --   Γ st ⟦@MLIR.DropFelt α ⟨name'⟩⟧) ⟦@MLIR.Assign name ⊤⟧ := by
  --   MLIR
  --   simp [State.drop_update_swap, h]
end true

open Risc0.MLIR

lemma combine_nondets : Γ (Γ st ⟦nondet p₁⟧) ⟦nondet p₂; p₃⟧ = Γ st ⟦nondet (p₁; p₂); p₃⟧ := by
  simp [run_nondet, run_seq_def]

lemma split_nondet_seq : Γ st ⟦nondet (s₁; s₂)⟧ = Γ st ⟦nondet s₁; nondet s₂⟧ := by
  simp [run_nondet, run_seq_def]

lemma step_det : Γ st ⟦(s₁; s₂); s₃⟧ = Γ (Γ st ⟦s₁⟧) ⟦s₂; s₃⟧ := by
  simp [run_nondet, run_seq_def]

lemma step_nondet : Γ st ⟦nondet (s₁; s₂); s₃⟧ = Γ (Γ st ⟦nondet s₁⟧) ⟦nondet s₂; s₃⟧ := by
  simp [run_nondet, run_seq_def]

section drop_sequencing
lemma drop_sequencing_dddd :
  Γ st ⟦s₁; s₂; s₃; s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ := by
  simp [run_nondet, run_seq_def]

lemma drop_sequencing_nddd :
  Γ st ⟦nondet s₁; s₂; s₃; s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ := by
  simp [run_nondet, run_seq_def]

lemma drop_sequencing_dndd :
  Γ st ⟦s₁; nondet s₂; s₃; s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ := by
  simp [run_nondet, run_seq_def]

lemma drop_sequencing_nndd :
  Γ st ⟦nondet (s₁; s₂); s₃; s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ := by
  simp [run_nondet, run_seq_def]

lemma drop_sequencing_ddnd :
  Γ st ⟦s₁; s₂; nondet s₃; s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ := by
  simp [run_nondet, run_seq_def]

lemma drop_sequencing_ndnd :
  Γ st ⟦nondet s₁; s₂; nondet s₃; s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ := by
  simp [run_nondet, run_seq_def]

lemma drop_sequencing_dnnd :
  Γ st ⟦s₁; nondet (s₂; s₃); s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ := by
  simp [run_nondet, run_seq_def]

lemma drop_sequencing_nnnd :
  Γ st ⟦nondet (s₁; s₂; s₃); s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ := by
  simp [run_nondet, run_seq_def]

lemma drop_sequencing_dddn :
  Γ st ⟦s₁; s₂; s₃; nondet s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_nddn :
  Γ st ⟦nondet s₁; s₂; s₃; nondet s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_dndn :
  Γ st ⟦s₁; nondet s₂; s₃; nondet s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_nndn :
  Γ st ⟦nondet (s₁; s₂); s₃; nondet s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_ddnn :
  Γ st ⟦s₁; s₂; nondet (s₃; s₄)⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_ndnn :
  Γ st ⟦nondet s₁; s₂; nondet (s₃; s₄)⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_dnnn :
  Γ st ⟦s₁; nondet (s₂; s₃; s₄)⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_nnnn :
  Γ st ⟦nondet (s₁; s₂; s₃; s₄)⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_ddd :
  Γ st ⟦s₁; s₂; s₃⟧ = Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_ndd :
  Γ st ⟦nondet s₁; s₂; s₃⟧ = Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_dnd :
  Γ st ⟦s₁; nondet s₂; s₃⟧ = Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_nnd :
  Γ st ⟦nondet (s₁; s₂); s₃⟧ = Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_ddn :
  Γ st ⟦s₁; s₂; nondet s₃⟧ = Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_ndn :
  Γ st ⟦nondet s₁; s₂; nondet s₃⟧ = Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_dnn :
  Γ st ⟦s₁; nondet (s₂; s₃)⟧ = Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_nnn :
  Γ st ⟦nondet (s₁; s₂; s₃)⟧ = Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_dd :
  Γ st ⟦s₁; s₂⟧ = Γ (Γ st ⟦s₁⟧) ⟦s₂⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_nd :
  Γ st ⟦nondet s₁; s₂⟧ = Γ (Γ st ⟦s₁⟧) ⟦s₂⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_dn :
  Γ st ⟦s₁; nondet s₂⟧ = Γ (Γ st ⟦s₁⟧) ⟦s₂⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_nn :
  Γ st ⟦nondet (s₁; s₂)⟧ = Γ (Γ st ⟦s₁⟧) ⟦s₂⟧ :=
  by simp [run_nondet, run_seq_def]

lemma drop_sequencing_d :
  Γ st ⟦s₁⟧ = Γ st ⟦s₁⟧ := rfl

lemma drop_sequencing_n :
  Γ st ⟦nondet (s₁)⟧ = Γ st ⟦s₁⟧ := by simp [run_nondet, run_seq_def]


-- TODO general tactic for unrolling N statements regardless of det/nondet like this would be nice
-- alternatively, process out nondet blocks up front

end drop_sequencing

end Reordering

end Risc0
