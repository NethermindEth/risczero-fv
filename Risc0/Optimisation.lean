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

section add
  lemma add_past_drop (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) (h₂ : ⟨name'⟩ ≠ rhs) :
    Γ st ⟦name ←ₐ .Add lhs rhs; @MLIR.DropFelt α ⟨name'⟩⟧ =
    Γ st ⟦@MLIR.DropFelt α ⟨name'⟩; name ←ₐ .Add lhs rhs⟧ := by
      MLIR
      simp [State.drop_update_swap, h]
      unfold State.dropFelts Map.drop State.updateFelts
      aesop
end add

section bitand
  lemma bitand_past_drop (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) (h₂ : ⟨name'⟩ ≠ rhs):
    Γ st ⟦name ←ₐ .BitAnd lhs rhs; @MLIR.DropFelt α ⟨name'⟩⟧ =
    Γ st ⟦@MLIR.DropFelt α ⟨name'⟩; name ←ₐ .BitAnd lhs rhs⟧ := by
      MLIR
      simp [State.drop_update_swap, h, feltBitAnd, State.get_dropFelts_of_ne h₁]
      aesop
end bitand

section const
  lemma const_past_add (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
    State.buffers (Γ st ⟦a ←ₐ C x; b ←ₐ Op.Add c d; rest⟧) =
    State.buffers (Γ st ⟦b ←ₐ Op.Add c d; a ←ₐ C x; rest⟧) := by
      MLIR
      rewrite [updateFelts_neq_comm] <;> simp [*]

  lemma const_past_bitAnd (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
    State.buffers (Γ st ⟦a ←ₐ C x; b ←ₐ Op.BitAnd c d; rest⟧) =
    State.buffers (Γ st ⟦b ←ₐ Op.BitAnd c d; a ←ₐ C x; rest⟧) := by
      MLIR
      rewrite [updateFelts_neq_comm] <;> simp [*]

  lemma const_past_bitAnd_nondet (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
    State.buffers (Γ st ⟦a ←ₐ C x; nondet(b ←ₐ Op.BitAnd c d; s₁); s₂⟧) =
    State.buffers (Γ st ⟦nondet (b ←ₐ Op.BitAnd c d); a ←ₐ C x; nondet s₁; s₂⟧) := by
      MLIR
      rewrite [updateFelts_neq_comm] <;> simp [*]

  lemma const_past_bitAnd_nondet_single (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
    State.buffers (Γ st ⟦a ←ₐ C x; nondet(b ←ₐ Op.BitAnd c d); s₂⟧) =
    State.buffers (Γ st ⟦nondet (b ←ₐ Op.BitAnd c d); a ←ₐ C x; s₂⟧) := by
      MLIR
      rewrite [updateFelts_neq_comm] <;> simp [*]

  lemma const_past_const (h: x ≠ y):
    State.buffers (Γ st ⟦x ←ₐ C c₁; y ←ₐ C c₂; rest⟧) =
    State.buffers (Γ st ⟦y ←ₐ C c₂; x ←ₐ C c₁; rest⟧) := by
      simp [MLIR.run_seq_def, MLIR.run_ass_def, Op.eval_const]
      rewrite [updateFelts_neq_comm] <;> simp [*]

  lemma const_past_drop (h : name ≠ name') :
    Γ st ⟦name ←ₐ C x; @MLIR.DropFelt α ⟨name'⟩⟧ =
    Γ st ⟦@MLIR.DropFelt α ⟨name'⟩; name ←ₐ C x⟧ := by
      MLIR
      simp [State.drop_update_swap, h]

  lemma const_past_get (h: x ≠ y):
    State.buffers (Γ st ⟦x ←ₐ C c₁; y ←ₐ .Get buf back offset; rest⟧) =
    State.buffers (Γ st ⟦y ←ₐ .Get buf back offset; x ←ₐ C c₁; rest⟧) := by
      simp [MLIR.run_seq_def, MLIR.run_ass_def, Op.eval_const]
      aesop
      rewrite [updateFelts_neq_comm] <;> simp [*]

  lemma const_past_nondet :
    State.buffers (Γ st ⟦x ←ₐ C c₁; nondet p; rest⟧) =
    State.buffers (Γ st ⟦nondet (x ←ₐ C c₁; p); rest⟧) := by
      simp [MLIR.run_seq_def, MLIR.run_nondet]
      rfl

  lemma const_past_mul (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
    State.buffers (Γ st ⟦a ←ₐ C x; b ←ₐ Op.Mul c d; rest⟧) =
    State.buffers (Γ st ⟦b ←ₐ Op.Mul c d; a ←ₐ C x; rest⟧) := by
      MLIR
      rewrite [updateFelts_neq_comm] <;> simp [*]

  lemma const_past_mul_nondet (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
    State.buffers (Γ st ⟦a ←ₐ C x; nondet(b ←ₐ Op.Mul c d; s₁); s₂⟧) =
    State.buffers (Γ st ⟦nondet (b ←ₐ Op.Mul c d); a ←ₐ C x; nondet s₁; s₂⟧) := by
      MLIR
      rewrite [updateFelts_neq_comm] <;> simp [*]

  lemma const_past_mul_nondet_single (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
    State.buffers (Γ st ⟦a ←ₐ C x; nondet(b ←ₐ Op.Mul c d); s₂⟧) =
    State.buffers (Γ st ⟦nondet (b ←ₐ Op.Mul c d); a ←ₐ C x; s₂⟧) := by
      MLIR
      rewrite [updateFelts_neq_comm] <;> simp [*]

  lemma const_past_set_nondet (h: ⟨a⟩ ≠ d) :
    State.buffers (Γ st ⟦a ←ₐ C x; nondet(b[c] ←ᵢ d; s₁); s₂⟧) =
    State.buffers (Γ st ⟦nondet(b[c] ←ᵢ d); a ←ₐ C x; nondet s₁; s₂⟧) := by
      MLIR
      simp [State.set!, State.setBufferElementImpl]
      aesop

  lemma const_past_set_nondet_single (h: ⟨a⟩ ≠ d) :
    State.buffers (Γ st ⟦a ←ₐ C x; nondet(b[c] ←ᵢ d); s₂⟧) =
    State.buffers (Γ st ⟦nondet(b[c] ←ᵢ d); a ←ₐ C x; s₂⟧) := by
      MLIR
      simp [State.set!, State.setBufferElementImpl]
      aesop
end const

section drop

  lemma drop_past_eqz_single (h : x ≠ y) :
    State.buffers (Γ st ⟦dropfelt y; @MLIR.Eqz IsNondet.NotInNondet x⟧) =
    State.buffers (Γ st ⟦@MLIR.Eqz IsNondet.NotInNondet x; dropfelt y⟧) := by
    MLIR
    simp [State.dropFelts, Map.drop]

  lemma drop_past_set (h : y ≠ val) :
    Γ st ⟦dropfelt y; .Set buf offset val⟧ =
    Γ st ⟦.Set buf offset val; dropfelt y⟧ := by
      MLIR; simp only [getElem!, dite_true, ne_eq]
      rw [State.get_dropFelts_of_ne h]
      unfold State.dropFelts Map.drop
      simp only [
        State.set!_felts, State.set!, State.setBufferElementImpl, Buffer.set?,
        Buffer.getBufferAtTime!, Buffer.Idx.time, Buffer.Idx.data
      ]
      aesop

  lemma drop_past_if (h : y ≠ c) (h₁ : y ∉ st.felts) :
    Γ st ⟦dropfelt y; guard c then prog⟧ =
    Γ st ⟦guard c then (dropfelt y; prog)⟧ := by
    MLIR
    simp [getElem!, State.get_dropFelts_of_ne h]
    aesop; aesop
    rw [Map.not_mem_iff_none, Map.getElem_def] at h₁
    unfold State.dropFelts Map.drop
    congr
    funext z
    aesop

  lemma drop_past_nondet :
    Γ st ⟦dropfelt y; nondet(prog)⟧ =
    Γ st ⟦nondet(dropfelt y; prog)⟧ := by
    MLIR

end drop

section get

  lemma get_past_const (h: x ≠ y) :
  State.buffers (Γ st ⟦x ←ₐ .Get buf back offset; y ←ₐ C c; rest⟧) =
  State.buffers (Γ st ⟦y ←ₐ C c; x ←ₐ .Get buf back offset; rest⟧) := by
    MLIR
    generalize eq: getImpl st buf back offset = get
    cases get with
      | none => aesop
      | some lit =>
        have h_lit: ∃ k, lit = Lit.Val k := getImpl_val_of_some eq
        aesop
        rewrite [updateFelts_neq_comm]
        rfl
        simp [h]

  lemma get_past_add (h: x ≠ y) (hl: ⟨x⟩ ≠ l) (hr: ⟨x⟩ ≠ r):
    State.buffers (Γ st ⟦x ←ₐ .Get buf back offset; y ←ₐ .Add l r; rest⟧) =
    State.buffers (Γ st ⟦y ←ₐ .Add l r; x ←ₐ .Get buf back offset; rest⟧) := by
      MLIR
      generalize eq: getImpl st buf back offset = get
      cases get with
        | none => aesop
        | some lit =>
          have h_lit: ∃ k, lit = Lit.Val k := getImpl_val_of_some eq
          aesop
          rewrite [updateFelts_neq_comm]
          rfl
          simp [h]

  lemma get_past_bitAnd_nondet (h: x ≠ y) (hl: ⟨x⟩ ≠ l) (hr: ⟨x⟩ ≠ r):
    State.buffers (Γ st ⟦x ←ₐ .Get buf back offset; nondet(y ←ₐ .BitAnd l r; s₁); s₂⟧) =
    State.buffers (Γ st ⟦nondet (y ←ₐ .BitAnd l r); x ←ₐ .Get buf back offset; nondet s₁; s₂⟧) := by
      MLIR
      generalize eq: getImpl st buf back offset = get
      cases get with
        | none => aesop
        | some lit =>
          have h_lit: ∃ k, lit = Lit.Val k := getImpl_val_of_some eq
          aesop
          rewrite [updateFelts_neq_comm]
          rfl
          simp [h]

  lemma get_past_bitAnd_nondet_single (h: x ≠ y) (hl: ⟨x⟩ ≠ l) (hr: ⟨x⟩ ≠ r):
    State.buffers (Γ st ⟦x ←ₐ .Get buf back offset; nondet(y ←ₐ .BitAnd l r); s₂⟧) =
    State.buffers (Γ st ⟦nondet (y ←ₐ .BitAnd l r); x ←ₐ .Get buf back offset; s₂⟧) := by
      MLIR
      generalize eq: getImpl st buf back offset = get
      cases get with
        | none => aesop
        | some lit =>
          have h_lit: ∃ k, lit = Lit.Val k := getImpl_val_of_some eq
          aesop
          rewrite [updateFelts_neq_comm]
          rfl
          simp [h]


  lemma get_past_mul (h: x ≠ y) (hl: ⟨x⟩ ≠ l) (hr: ⟨x⟩ ≠ r):
    State.buffers (Γ st ⟦x ←ₐ .Get buf back offset; y ←ₐ .Mul l r; rest⟧) =
    State.buffers (Γ st ⟦y ←ₐ .Mul l r; x ←ₐ .Get buf back offset; rest⟧) := by
      MLIR
      generalize eq: getImpl st buf back offset = get
      cases get with
        | none => aesop
        | some lit =>
          have h_lit: ∃ k, lit = Lit.Val k := getImpl_val_of_some eq
          aesop
          rewrite [updateFelts_neq_comm]
          rfl
          simp [h]

  lemma get_past_mul_nondet (h: x ≠ y) (hl: ⟨x⟩ ≠ l) (hr: ⟨x⟩ ≠ r):
    State.buffers (Γ st ⟦x ←ₐ .Get buf back offset; nondet(y ←ₐ .Mul l r; s₁); s₂⟧) =
    State.buffers (Γ st ⟦nondet (y ←ₐ .Mul l r); x ←ₐ .Get buf back offset; nondet s₁; s₂⟧) := by
      MLIR
      generalize eq: getImpl st buf back offset = get
      cases get with
        | none => aesop
        | some lit =>
          have h_lit: ∃ k, lit = Lit.Val k := getImpl_val_of_some eq
          aesop
          rewrite [updateFelts_neq_comm]
          rfl
          simp [h]

  lemma get_past_get_buf (h: buf ≠ buf') (h': x ≠ y) :
    State.buffers (Γ st ⟦x ←ₐ .Get buf back offset; y ←ₐ .Get buf' back' offset'; rest⟧) =
    State.buffers (Γ st ⟦y ←ₐ .Get buf' back' offset';x ←ₐ .Get buf back offset;  rest⟧) := by
      MLIR
      generalize eq1: getImpl st buf back offset = get1
      generalize eq2: getImpl st buf' back' offset' = get2
      cases get1 with
        | none => simp [State.update]; aesop
        | some lit1 =>
          have h1: ∃ k1, lit1 = Lit.Val k1 := getImpl_val_of_some eq1
          cases get2 with
            | none => aesop
            | some lit2 =>
              have h2: ∃ k2, lit2 = Lit.Val k2 := getImpl_val_of_some eq2
              aesop
              rewrite [updateFelts_neq_comm]
              rfl
              simp [h']

  lemma get_past_get_offset (h: offset ≠ offset') (h': x ≠ y) :
    State.buffers (Γ st ⟦x ←ₐ .Get buf back offset; y ←ₐ .Get buf' back' offset'; rest⟧) =
    State.buffers (Γ st ⟦y ←ₐ .Get buf' back' offset';x ←ₐ .Get buf back offset;  rest⟧) := by
      MLIR
      generalize eq1: getImpl st buf back offset = get1
      generalize eq2: getImpl st buf' back' offset' = get2
      cases get1 with
        | none => simp [State.update]; aesop
        | some lit1 =>
          have h1: ∃ k1, lit1 = Lit.Val k1 := getImpl_val_of_some eq1
          cases get2 with
            | none => aesop
            | some lit2 =>
              have h2: ∃ k2, lit2 = Lit.Val k2 := getImpl_val_of_some eq2
              aesop
              rewrite [updateFelts_neq_comm]
              rfl
              simp [h']

  lemma get_past_set_buf_nondet (h: ⟨x⟩ ≠ val) (h': buf' ≠ buf):
    State.buffers (Γ st ⟦x ←ₐ .Get buf back offset; nondet(buf'[index] ←ᵢ val; s₁); s₂⟧) =
    State.buffers (Γ st ⟦nondet (buf'[index] ←ᵢ val); x ←ₐ .Get buf back offset; nondet s₁; s₂⟧) := by
      MLIR
      generalize eq: getImpl st buf back offset = get
      cases get with
        | none => sorry
        | some lit1 => sorry

  lemma get_past_set_buf_nondet_single (h: ⟨x⟩ ≠ val) (h': buf' ≠ buf):
    State.buffers (Γ st ⟦x ←ₐ .Get buf back offset; nondet(buf'[index] ←ᵢ val); s₂⟧) =
    State.buffers (Γ st ⟦nondet (buf'[index] ←ᵢ val); x ←ₐ .Get buf back offset; s₂⟧) := by
      MLIR
      generalize eq: getImpl st buf back offset = get
      cases get with
        | none => sorry
        | some lit1 => sorry

end get

section inv
  lemma drop_assign_inv_swap (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) :
    Γ st ⟦name ←ₐ .Inv lhs; dropfelt ⟨name'⟩⟧ =
    Γ st ⟦dropfelt ⟨name'⟩; name ←ₐ .Inv lhs⟧ := by
      MLIR
      simp [State.drop_update_swap, h, State.get_dropFelts_of_ne h₁]
end inv

section isz
  lemma drop_assign_isz_swap (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) :
    Γ st ⟦name ←ₐ .Isz lhs; dropfelt ⟨name'⟩⟧ =
    Γ st ⟦dropfelt ⟨name'⟩; name ←ₐ .Isz lhs⟧ := by
      MLIR
      simp [State.drop_update_swap, h]
      unfold State.dropFelts Map.drop State.updateFelts
      aesop
end isz

section mul
  lemma mul_past_drop (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) (h₂ : ⟨name'⟩ ≠ rhs):
    Γ st ⟦name ←ₐ .Mul lhs rhs; @MLIR.DropFelt α ⟨name'⟩⟧ =
    Γ st ⟦@MLIR.DropFelt α ⟨name'⟩; name ←ₐ .Mul lhs rhs⟧ := by
      MLIR
      simp [State.drop_update_swap, h]
      unfold State.dropFelts Map.drop State.updateFelts
      aesop
end mul

section neg
  lemma neg_past_drop (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs):
    Γ st ⟦name ←ₐ .Neg lhs; @MLIR.DropFelt α ⟨name'⟩⟧ =
    Γ st ⟦@MLIR.DropFelt α ⟨name'⟩; name ←ₐ .Neg lhs⟧ := by
      MLIR
      simp [State.drop_update_swap, h]
      unfold State.dropFelts Map.drop
      aesop
end neg

section pow
  lemma drop_assign_pow_swap {n : ℕ} (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) :
    Γ st ⟦name ←ₐ .Pow lhs n; @MLIR.DropFelt α ⟨name'⟩⟧ =
    Γ st ⟦@MLIR.DropFelt α ⟨name'⟩; name ←ₐ .Pow lhs n⟧ := by
      MLIR
      simp [State.drop_update_swap, h, State.get_dropFelts_of_ne' h₁]
end pow

section sub
  lemma sub_past_drop (h : name ≠ name') (h₁ : ⟨name'⟩ ≠ lhs) (h₂ : ⟨name'⟩ ≠ rhs):
    Γ st ⟦name ←ₐ .Sub lhs rhs; @MLIR.DropFelt α ⟨name'⟩⟧ =
    Γ st ⟦@MLIR.DropFelt α ⟨name'⟩; name ←ₐ .Sub lhs rhs⟧ := by
      MLIR
      simp [State.drop_update_swap, h]
      unfold State.dropFelts Map.drop State.updateFelts
      aesop
end sub

section true
  -- lemma drop_assign_true_swap {α : IsNondet} {name name' : String} {x : Felt}
  --   (h : name ≠ name') :
  --   Γ st ⟦name ←ₐ ⊤; @MLIR.DropFelt α ⟨name'⟩⟧ =
  --   Γ st ⟦@MLIR.DropFelt α ⟨name'⟩; name ←ₐ ⊤⟧ := by
  --   MLIR
  --   simp [State.drop_update_swap, h]
end true

lemma combine_nondets : Γ (Γ st ⟦nondet p₁⟧) ⟦nondet p₂; p₃⟧ = Γ st ⟦nondet (p₁; p₂); p₃⟧ := rfl

lemma step_nondet : Γ st ⟦nondet (s₁; s₂); s₃⟧ = Γ (Γ st ⟦nondet s₁⟧) ⟦nondet s₂; s₃⟧ := by
  aesop

end Reordering

end Risc0
