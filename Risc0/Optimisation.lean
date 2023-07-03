import Risc0.Basic
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

lemma opt_swap (h: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧) :
  Γ st ⟦p₁; p₂; p₃⟧ = Γ ( Γ st ⟦p₂⟧) ⟦p₁; p₃⟧ := by
    simp [MLIR.run_seq_def, h]

lemma opt_swap_nondet_single (h: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧) :
  Γ st ⟦p₁; nondet p₂; p₃⟧ = Γ ( Γ st ⟦p₂⟧) ⟦p₁; p₃⟧ := by
    simp [MLIR.run_seq_def, MLIR.run_nondet, h]

lemma opt_swap_nondet_seq (h: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧) :
  Γ st ⟦p₁; nondet (p₂; p₃); p₄⟧ = Γ ( Γ st ⟦p₂⟧) ⟦p₁; nondet p₃; p₄⟧ := by
    simp [MLIR.run_seq_def, MLIR.run_nondet, h]

lemma opt_swap_ddd (h: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧) :
  Γ st ⟦p₁; p₂; p₃⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁; p₃⟧ := by
    simp [MLIR.run_seq_def, h]

lemma opt_swap_ndd (h: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧) :
  Γ st ⟦nondet p₁; p₂; p₃⟧ = Γ (Γ st ⟦p₂⟧) ⟦nondet p₁; p₃⟧ := by
    simp [MLIR.run_seq_def, MLIR.run_nondet, h]

lemma opt_swap_dnd (h: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧) :
  Γ st ⟦p₁; nondet p₂; p₃⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁; p₃⟧ := by
    simp [MLIR.run_seq_def, MLIR.run_nondet, h]

lemma opt_swap_nnd (h: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧) :
  Γ st ⟦nondet (p₁; p₂); p₃⟧ = Γ (Γ st ⟦p₂⟧) ⟦nondet p₁; p₃⟧ := by
    simp [MLIR.run_seq_def, MLIR.run_nondet, h]

lemma opt_swap_ddn (h: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧) :
  Γ st ⟦p₁; p₂; nondet p₃⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁; nondet p₃⟧ := by
    simp [MLIR.run_seq_def, h]

lemma opt_swap_ndn (h: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧) :
  Γ st ⟦nondet p₁; p₂; nondet p₃⟧ = Γ (Γ st ⟦p₂⟧) ⟦nondet (p₁; p₃)⟧ := by
    simp [MLIR.run_seq_def, MLIR.run_nondet, h]

lemma opt_swap_dnn (h: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧) :
  Γ st ⟦p₁; nondet (p₂; p₃)⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁; nondet p₃⟧ := by
    simp [MLIR.run_seq_def, MLIR.run_nondet, h]

lemma opt_swap_nnn (h: Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ = Γ (Γ st ⟦p₂⟧) ⟦p₁⟧) :
  Γ st ⟦nondet (p₁; p₂; p₃)⟧ = Γ (Γ st ⟦p₂⟧) ⟦nondet (p₁; p₃)⟧ := by
    simp [MLIR.run_seq_def, MLIR.run_nondet, h]

section add
  lemma add_past_const (h: a ≠ b) (h': ⟨b⟩ ≠ c) (h'': ⟨b⟩ ≠ d):
    Γ (Γ st ⟦@MLIR.Assign α a (Op.Add c d)⟧) ⟦@MLIR.Assign β b (Op.Const x)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β b (Op.Const x)⟧) ⟦@MLIR.Assign α a (Op.Add c d)⟧ := by
      simp [MLIR.run_ass_def]
      rewrite [updateFelts_neq_comm] <;> aesop

  lemma add_past_drop (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) (h₂ : ⟨name'⟩ ≠ rhs) :
    Γ (Γ st ⟦@MLIR.Assign α name (Op.Add lhs rhs)⟧) ⟦@MLIR.DropFelt β ⟨name'⟩⟧ =
    Γ (Γ st ⟦@MLIR.DropFelt β ⟨name'⟩⟧) ⟦@MLIR.Assign α name (Op.Add lhs rhs)⟧ := by
      simp [MLIR.run_ass_def, MLIR.run_dropfelt]
      aesop
end add

section andeqz
  lemma andEqz_past_const (h: ⟨b⟩ ≠ d):
    Γ (Γ st ⟦@MLIR.Assign α a (Op.AndEqz c d)⟧) ⟦@MLIR.Assign β b (Op.Const x)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β b (Op.Const x)⟧) ⟦@MLIR.Assign α a (Op.AndEqz c d)⟧ := by
      simp [MLIR.run_ass_def, State.updateFelts, State.updateProps, *, Map.update]
      aesop
  
  lemma andEqz_past_drop (h : ⟨x⟩ ≠ y) (h₁ : rhs ≠ y) :
    Γ (Γ st ⟦@MLIR.Assign β x (Op.AndEqz lhs rhs)⟧) ⟦@MLIR.DropFelt α y⟧ =
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Assign β x (Op.AndEqz lhs rhs)⟧ := by
      simp [
        MLIR.run_ass_def, MLIR.run_dropfelt, State.updateFelts, State.updateProps, Map.update,
        State.dropFelts, Map.drop
      ]
      aesop
end andeqz

section bitand
  lemma bitAnd_past_const (h: a ≠ b) (h': ⟨b⟩ ≠ c) (h'': ⟨b⟩ ≠ d):
    Γ (Γ st ⟦@MLIR.Assign α a (Op.BitAnd c d)⟧) ⟦@MLIR.Assign β b (Op.Const x)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β b (Op.Const x)⟧) ⟦@MLIR.Assign α a (Op.BitAnd c d)⟧ := by
      simp [MLIR.run_ass_def]
      rewrite [updateFelts_neq_comm] <;> aesop

  lemma bitAnd_past_drop (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) (h₂ : ⟨name'⟩ ≠ rhs):
    Γ (Γ st ⟦@MLIR.Assign α name (Op.BitAnd lhs rhs)⟧) ⟦@MLIR.DropFelt β ⟨name'⟩⟧ =
    Γ (Γ st ⟦@MLIR.DropFelt β ⟨name'⟩⟧) ⟦@MLIR.Assign α name (Op.BitAnd lhs rhs)⟧ := by
      simp [MLIR.run_ass_def, MLIR.run_dropfelt]
      aesop
end bitand

section const
  lemma const_past_add (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
    Γ (Γ st ⟦@MLIR.Assign α a (Op.Const x)⟧) ⟦@MLIR.Assign β b (Op.Add c d)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β b (Op.Add c d)⟧) ⟦@MLIR.Assign α a (Op.Const x)⟧ := by
      rw [add_past_const] <;> aesop
  
  lemma const_past_andEqz (h: ⟨b⟩ ≠ d):
    Γ (Γ st ⟦@MLIR.Assign β b (Op.Const x)⟧) ⟦@MLIR.Assign α a (Op.AndEqz c d)⟧ =
    Γ (Γ st ⟦@MLIR.Assign α a (Op.AndEqz c d)⟧) ⟦@MLIR.Assign β b (Op.Const x)⟧ := by
      rw [andEqz_past_const]
      aesop

  lemma const_past_bitAnd (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
    Γ (Γ st ⟦@MLIR.Assign α a (Op.Const x)⟧) ⟦@MLIR.Assign β b (Op.BitAnd c d)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β b (Op.BitAnd c d)⟧) ⟦@MLIR.Assign α a (Op.Const x)⟧ := by
      rw [bitAnd_past_const] <;> aesop

  lemma const_past_const (h: x ≠ y):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Const c₁)⟧) ⟦@MLIR.Assign β y (Op.Const c₂)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.Const c₂)⟧) ⟦@MLIR.Assign α x (Op.Const c₁)⟧ := by
      simp [MLIR.run_ass_def]
      rewrite [updateFelts_neq_comm] <;> aesop

  lemma const_past_drop (h : name ≠ name') :
    Γ (Γ st ⟦@MLIR.Assign α name (Op.Const x)⟧) ⟦@MLIR.DropFelt β ⟨name'⟩⟧ =
    Γ (Γ st ⟦@MLIR.DropFelt β ⟨name'⟩⟧) ⟦@MLIR.Assign α name (Op.Const x)⟧ := by
      simp [MLIR.run_ass_def, MLIR.run_dropfelt]
      aesop

  lemma const_past_get (h: x ≠ y):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Const c₁)⟧) ⟦@MLIR.Assign β y (Op.Get buf back offset)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.Get buf back offset)⟧) ⟦@MLIR.Assign α x (Op.Const c₁)⟧ := by
      simp [MLIR.run_ass_def]
      aesop
      rewrite [updateFelts_neq_comm] <;> simp [*]

  lemma const_past_mul (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
    Γ (Γ st ⟦@MLIR.Assign α a (Op.Const x)⟧) ⟦@MLIR.Assign β b (Op.Mul c d)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β b (Op.Mul c d)⟧) ⟦@MLIR.Assign α a (Op.Const x)⟧ := by
      simp [MLIR.run_ass_def]
      rewrite [updateFelts_neq_comm] <;> simp [*]

  lemma const_past_set (h: ⟨a⟩ ≠ b) :
    Γ (Γ st ⟦@MLIR.Assign α a (Op.Const x)⟧) ⟦@MLIR.Set buf offset b⟧ =
    Γ (Γ st ⟦@MLIR.Set buf offset b⟧) ⟦@MLIR.Assign α a (Op.Const x)⟧ := by
      simp [MLIR.run_ass_def, MLIR.run_set_def, State.set!, State.setBufferElementImpl]
      aesop

  lemma const_past_sub (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
    Γ (Γ st ⟦@MLIR.Assign α a (Op.Const x)⟧) ⟦@MLIR.Assign β b (Op.Sub c d)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β b (Op.Sub c d)⟧) ⟦@MLIR.Assign α a (Op.Const x)⟧ := by
      simp [MLIR.run_ass_def]
      rewrite [updateFelts_neq_comm] <;> aesop
  
  lemma const_past_true (h: a ≠ b) :
    Γ (Γ st ⟦@MLIR.Assign α a (Op.Const x)⟧) ⟦@MLIR.Assign β b (Op.True)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β b (Op.True)⟧) ⟦@MLIR.Assign α a (Op.Const x)⟧ := by
      simp [MLIR.run_ass_def]
      aesop

end const

section drop

  lemma drop_past_add (h : ⟨x⟩ ≠ y) (h₁ : lhs ≠ y) (h₂ : rhs ≠ y) :
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Assign β x (Op.Add lhs rhs)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β x (Op.Add lhs rhs)⟧) ⟦@MLIR.DropFelt α y⟧ := by
      rw [add_past_drop] <;> aesop

  lemma drop_past_andEqz (h : ⟨x⟩ ≠ y) (h₁ : rhs ≠ y) :
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Assign β x (Op.AndEqz lhs rhs)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β x (Op.AndEqz lhs rhs)⟧) ⟦@MLIR.DropFelt α y⟧ := by
      rw [andEqz_past_drop] <;> aesop

  lemma drop_past_bitAnd (h : ⟨x⟩ ≠ y) (h₁ : lhs ≠ y) (h₂ : rhs ≠ y):
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Assign β x (Op.BitAnd lhs rhs)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β x (Op.BitAnd lhs rhs)⟧) ⟦@MLIR.DropFelt α y⟧ := by
      rw [bitAnd_past_drop] <;> aesop

  lemma drop_past_const (h : ⟨x⟩ ≠ y) :
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Assign β x (Op.Const c)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β x (Op.Const c)⟧) ⟦@MLIR.DropFelt α y⟧ := by
      rw [const_past_drop]; aesop

  lemma drop_past_eqz (h : x ≠ y) :
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Eqz β x⟧ =
    Γ (Γ st ⟦@MLIR.Eqz β x⟧) ⟦@MLIR.DropFelt α y⟧ := by
      simp [MLIR.run_dropfelt, MLIR.run_eqz, withEqZero, State.dropFelts, Map.drop]
      sorry --map[x]! issues introduced by eqz

  lemma drop_past_get (h: ⟨x⟩ ≠ y) :
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Assign β x (Op.Get buf back offset)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β x (Op.Get buf back offset)⟧) ⟦@MLIR.DropFelt α y⟧ := by
      simp [MLIR.run_dropfelt, MLIR.run_ass_def]
      sorry
  
  -- lemma drop_past_if (h : y ≠ x) (h₁ : Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦prog⟧ = Γ (Γ st ⟦prog⟧) ⟦@MLIR.DropFelt α y⟧) :
  --   Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.If β x prog⟧ =
  --   Γ (Γ st ⟦@MLIR.If β x prog⟧) ⟦@MLIR.DropFelt α y⟧ := by
  --     simp [MLIR.run_dropfelt, MLIR.run_if]
  --     simp [getElem!, State.get_dropFelts_of_ne h]
      
  --     -- MLIR
  --     -- aesop; aesop
  --     -- rw [Map.not_mem_iff_none, Map.getElem_def] at h₁
  --     -- unfold State.dropFelts Map.drop
  --     -- congr
  --     -- funext z
  --     -- aesop

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
      aesop

  lemma drop_past_sub (h : ⟨x⟩ ≠ y) (h₁ : lhs ≠ y) (h₂ : rhs ≠ y) :
    Γ (Γ st ⟦@MLIR.DropFelt α y⟧) ⟦@MLIR.Assign β x (Op.Sub lhs rhs)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β x (Op.Sub lhs rhs)⟧) ⟦@MLIR.DropFelt α y⟧ := by
      sorry

end drop

section get
  lemma get_past_add (h: x ≠ y) (hl: ⟨x⟩ ≠ l) (hr: ⟨x⟩ ≠ r):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Assign β y (Op.Add l r)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.Add l r)⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
      simp only [MLIR.run_ass_def, Op.eval, *]
      generalize eq: getImpl st buf back offset = get
      cases get with
        | none => aesop
        | some lit =>
          have h_lit: ∃ k, lit = Lit.Val k := getImpl_val_of_some eq
          sorry
    
  lemma get_past_andEqz (h: x ≠ y) (hl: ⟨x⟩ ≠ l) (hr: ⟨x⟩ ≠ r):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Assign β y (Op.AndEqz l r)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.AndEqz l r)⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
      simp only [MLIR.run_ass_def, Op.eval, *]
      generalize eq: getImpl st buf back offset = get
      cases get with
        | none => aesop
        | some lit =>
          have h_lit: ∃ k, lit = Lit.Val k := getImpl_val_of_some eq
          sorry

  lemma get_past_bitAnd (h: x ≠ y) (hl: ⟨x⟩ ≠ l) (hr: ⟨x⟩ ≠ r):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Assign β y (Op.BitAnd l r)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.BitAnd l r)⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
      sorry

  lemma get_past_const (h: x ≠ y) :
  Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Assign β y (Op.Const c)⟧ =
  Γ (Γ st ⟦@MLIR.Assign β y (Op.Const c)⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
    rewrite [const_past_get] <;> aesop
    

  -- lemma get_past_drop (h: ⟨x⟩ ≠ y) :
  -- Γ st ⟦@MLIR.Assign x .Get buf back offset⟧) ⟦dropfelt y⟧ =
  -- Γ st ⟦dropfelt y⟧) ⟦@MLIR.Assign x .Get buf back offset⟧ := by
  --   MLIR
  --   generalize eq: getImpl st buf back offset = get
  --   cases get with
  --     | none => aesop
  --     | some lit =>
  --       have h_lit: ∃ k, lit = Lit.Val k := getImpl_val_of_some eq
  --       aesop


  lemma get_past_get_buf (h: buf ≠ buf') (h': x ≠ y) :
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Assign β y (Op.Get buf' back' offset')⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.Get buf' back' offset')⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
      sorry

  lemma get_past_get_offset (h: offset ≠ offset') (h': x ≠ y) :
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Assign β y (Op.Get buf' back' offset')⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.Get buf' back' offset')⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
      simp only [MLIR.run_ass_def, Op.eval] --REVIEW: eval_getBuffer does not go to getImpl, is this expected
      generalize eq1: getImpl st buf back offset = get1
      generalize eq2: getImpl st buf' back' offset' = get2
      sorry

  lemma get_past_mul (h: x ≠ y) (hl: ⟨x⟩ ≠ l) (hr: ⟨x⟩ ≠ r):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Assign β y (Op.Mul l r)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.Mul l r)⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
      simp only [MLIR.run_ass_def, Op.eval, *]
      generalize eq: getImpl st buf back offset = get
      cases get with
        | none => aesop
        | some lit =>
          have h_lit: ∃ k, lit = Lit.Val k := getImpl_val_of_some eq
          sorry

  lemma get_past_set_buf (h: ⟨x⟩ ≠ val) (h': buf' ≠ buf):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Set buf' index val⟧ =
    Γ (Γ st ⟦@MLIR.Set buf' index val⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
      sorry

  lemma get_past_sub (h: x ≠ y) (hl: ⟨x⟩ ≠ l) (hr: ⟨x⟩ ≠ r):
    Γ (Γ st ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧) ⟦@MLIR.Assign β y (Op.Sub l r)⟧ =
    Γ (Γ st ⟦@MLIR.Assign β y (Op.Sub l r)⟧) ⟦@MLIR.Assign α x (Op.Get buf back offset)⟧ := by
      simp only [MLIR.run_ass_def, Op.eval, *]
      generalize eq: getImpl st buf back offset = get
      cases get with
        | none => aesop
        | some lit =>
          have h_lit: ∃ k, lit = Lit.Val k := getImpl_val_of_some eq
          sorry

end get

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
  --     aesop
end isz

section mul
  -- lemma mul_past_drop (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) (h₂ : ⟨name'⟩ ≠ rhs):
  --   Γ (Γ st ⟦@MLIR.Assign name .Mul lhs rhs⟧) ⟦@MLIR.DropFelt α ⟨name'⟩⟧ =
  --   Γ (Γ st ⟦@MLIR.DropFelt α ⟨name'⟩⟧) ⟦@MLIR.Assign name .Mul lhs rhs⟧ := by
  --     MLIR
  --     simp [State.drop_update_swap, h]
  --     unfold State.dropFelts Map.drop State.updateFelts
  --     aesop
end mul

section neg
  -- lemma neg_past_drop (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs):
  --   Γ (Γ st ⟦@MLIR.Assign name .Neg lhs⟧) ⟦@MLIR.DropFelt α ⟨name'⟩⟧ =
  --   Γ (Γ st ⟦@MLIR.DropFelt α ⟨name'⟩⟧) ⟦@MLIR.Assign name .Neg lhs⟧ := by
  --     MLIR
  --     simp [State.drop_update_swap, h]
  --     unfold State.dropFelts Map.drop
  --     aesop
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
  --     aesop
end sub

section true
  -- lemma drop_assign_true_swap {α : IsNondet} {name name' : String} {x : Felt}
  --   (h : name ≠ name') :
  --   Γ st ⟦@MLIR.Assign name ⊤⟧) ⟦@MLIR.DropFelt α ⟨name'⟩⟧ =
  --   Γ st ⟦@MLIR.DropFelt α ⟨name'⟩⟧) ⟦@MLIR.Assign name ⊤⟧ := by
  --   MLIR
  --   simp [State.drop_update_swap, h]
end true

lemma combine_nondets : Γ (Γ st ⟦nondet p₁⟧) ⟦nondet p₂; p₃⟧ = Γ st ⟦nondet (p₁; p₂); p₃⟧ := rfl

lemma split_nondet_seq : Γ st ⟦nondet (s₁; s₂)⟧ = Γ st ⟦nondet s₁; nondet s₂⟧ := by rfl

lemma step_det : Γ st ⟦(s₁; s₂); s₃⟧ = Γ (Γ st ⟦s₁⟧) ⟦s₂; s₃⟧ := by
  aesop

lemma step_nondet : Γ st ⟦nondet (s₁; s₂); s₃⟧ = Γ (Γ st ⟦nondet s₁⟧) ⟦nondet s₂; s₃⟧ := by
  aesop

section drop_sequencing
lemma drop_sequencing_dddd :
  Γ st ⟦s₁; s₂; s₃; s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by aesop

lemma drop_sequencing_nddd :
  Γ st ⟦nondet s₁; s₂; s₃; s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by aesop

lemma drop_sequencing_dndd :
  Γ st ⟦s₁; nondet s₂; s₃; s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by aesop

lemma drop_sequencing_nndd :
  Γ st ⟦nondet (s₁; s₂); s₃; s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by aesop

lemma drop_sequencing_ddnd :
  Γ st ⟦s₁; s₂; nondet s₃; s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by aesop

lemma drop_sequencing_ndnd :
  Γ st ⟦nondet s₁; s₂; nondet s₃; s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by aesop

lemma drop_sequencing_dnnd :
  Γ st ⟦s₁; nondet (s₂; s₃); s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by aesop

lemma drop_sequencing_nnnd :
  Γ st ⟦nondet (s₁; s₂; s₃); s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by aesop

lemma drop_sequencing_dddn :
  Γ st ⟦s₁; s₂; s₃; nondet s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by aesop

lemma drop_sequencing_nddn :
  Γ st ⟦nondet s₁; s₂; s₃; nondet s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by aesop

lemma drop_sequencing_dndn :
  Γ st ⟦s₁; nondet s₂; s₃; nondet s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by aesop

lemma drop_sequencing_nndn :
  Γ st ⟦nondet (s₁; s₂); s₃; nondet s₄⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by aesop

lemma drop_sequencing_ddnn :
  Γ st ⟦s₁; s₂; nondet (s₃; s₄)⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by aesop

lemma drop_sequencing_ndnn :
  Γ st ⟦nondet s₁; s₂; nondet (s₃; s₄)⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by aesop

lemma drop_sequencing_dnnn :
  Γ st ⟦s₁; nondet (s₂; s₃; s₄)⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by aesop

lemma drop_sequencing_nnnn :
  Γ st ⟦nondet (s₁; s₂; s₃; s₄)⟧ = Γ (Γ (Γ (Γ st ⟦s₁⟧) ⟦s₂⟧) ⟦s₃⟧) ⟦s₄⟧ :=
  by aesop

lemma drop_sequencing_ddd:
  Γ st ⟦@MLIR.DropFelt .NotInNondet x; s₁; s₂⟧ = Γ (Γ (Γ st ⟦@MLIR.DropFelt .NotInNondet x⟧) ⟦s₁⟧) ⟦s₂⟧ :=
  by aesop

lemma drop_sequencing_dnd:
  Γ st ⟦@MLIR.DropFelt .NotInNondet x; nondet s₁; s₂⟧ = Γ (Γ (Γ st ⟦@MLIR.DropFelt .NotInNondet x⟧) ⟦s₁⟧) ⟦s₂⟧ :=
  by aesop

lemma drop_sequencing_ddn:
  Γ st ⟦@MLIR.DropFelt .NotInNondet x; s₁; nondet s₂⟧ = Γ (Γ (Γ st ⟦@MLIR.DropFelt .NotInNondet x⟧) ⟦s₁⟧) ⟦s₂⟧ :=
  by aesop

lemma drop_sequencing_dnn:
  Γ st ⟦@MLIR.DropFelt .NotInNondet x; nondet (s₁; s₂)⟧ = Γ (Γ (Γ st ⟦@MLIR.DropFelt .NotInNondet x⟧) ⟦s₁⟧) ⟦s₂⟧ :=
  by aesop

lemma drop_sequencing_dd:
  Γ st ⟦@MLIR.DropFelt .NotInNondet x; s₁⟧ = Γ (Γ st ⟦@MLIR.DropFelt .NotInNondet x⟧) ⟦s₁⟧ :=
  by aesop

lemma drop_sequencing_dn:
  Γ st ⟦@MLIR.DropFelt .NotInNondet x; nondet s₁⟧ = Γ (Γ st ⟦@MLIR.DropFelt .NotInNondet x⟧) ⟦s₁⟧ :=
  by aesop

lemma drop_sequencing_d:
  Γ st ⟦@MLIR.DropFelt .NotInNondet x⟧ = Γ st ⟦@MLIR.DropFelt .NotInNondet x⟧ := rfl

-- TODO general tactic for unrolling N statements regardless of det/nondet like this would be nice
-- alternatively, process out nondet blocks up front

end drop_sequencing

end Reordering

end Risc0
