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

lemma const_past_const (h: x ≠ y):
  State.buffers (Γ st ⟦x ←ₐ C c₁; y ←ₐ C c₂; rest⟧) =
  State.buffers (Γ st ⟦y ←ₐ C c₂; x ←ₐ C c₁; rest⟧) := by
  simp [MLIR.run_seq_def, MLIR.run_ass_def, Op.eval_const]
  rewrite [updateFelts_neq_comm] <;> simp [*]

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

lemma const_past_add
  (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
  State.buffers (Γ st ⟦a ←ₐ C x; b ←ₐ Op.Add c d; rest⟧) =
  State.buffers (Γ st ⟦b ←ₐ Op.Add c d; a ←ₐ C x; rest⟧) := by
  MLIR
  rewrite [updateFelts_neq_comm] <;> simp [*]

lemma const_past_bitAnd
  (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
  State.buffers (Γ st ⟦a ←ₐ C x; b ←ₐ Op.BitAnd c d; rest⟧) =
  State.buffers (Γ st ⟦b ←ₐ Op.BitAnd c d; a ←ₐ C x; rest⟧) := by
  MLIR
  rewrite [updateFelts_neq_comm] <;> simp [*]

lemma const_past_bitAnd_nondet
  (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
  State.buffers (Γ st ⟦a ←ₐ C x; nondet(b ←ₐ Op.BitAnd c d; s₁); s₂⟧) =
  State.buffers (Γ st ⟦nondet (b ←ₐ Op.BitAnd c d); a ←ₐ C x; nondet s₁; s₂⟧) := by
  MLIR
  rewrite [updateFelts_neq_comm] <;> simp [*]

lemma const_past_bitAnd_nondet_single
  (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
  State.buffers (Γ st ⟦a ←ₐ C x; nondet(b ←ₐ Op.BitAnd c d); s₂⟧) =
  State.buffers (Γ st ⟦nondet (b ←ₐ Op.BitAnd c d); a ←ₐ C x; s₂⟧) := by
  MLIR
  rewrite [updateFelts_neq_comm] <;> simp [*]

lemma const_past_mul
  (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
  State.buffers (Γ st ⟦a ←ₐ C x; b ←ₐ Op.Mul c d; rest⟧) =
  State.buffers (Γ st ⟦b ←ₐ Op.Mul c d; a ←ₐ C x; rest⟧) := by
  MLIR
  rewrite [updateFelts_neq_comm] <;> simp [*]

lemma const_past_mul_nondet
  (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
  State.buffers (Γ st ⟦a ←ₐ C x; nondet(b ←ₐ Op.Mul c d; s₁); s₂⟧) =
  State.buffers (Γ st ⟦nondet (b ←ₐ Op.Mul c d); a ←ₐ C x; nondet s₁; s₂⟧) := by
  MLIR
  rewrite [updateFelts_neq_comm] <;> simp [*]

lemma const_past_mul_nondet_single
  (h: a ≠ b) (h': ⟨a⟩ ≠ c) (h'': ⟨a⟩ ≠ d):
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

lemma combine_nondets : Γ (Γ st ⟦nondet p₁⟧) ⟦nondet p₂; p₃⟧ = Γ st ⟦nondet (p₁; p₂); p₃⟧ := rfl

lemma step_nondet : Γ st ⟦nondet (s₁; s₂); s₃⟧ = Γ (Γ st ⟦nondet s₁⟧) ⟦nondet s₂; s₃⟧ := by
  aesop

end Reordering

end Risc0
