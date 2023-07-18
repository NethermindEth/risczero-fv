import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Risc0.Cirgen
import Risc0.State

namespace Risc0

section WithMLIR 

variable {α : IsNondet} {st : State} {name : String}

open MLIRNotation IsNondet
open Risc0.VarType

namespace MLIR

lemma run_ass_def : Γ st ⟦name ←ₐ op⟧ = st[name] ←ₛ Γ st ⟦op⟧ₑ := rfl

lemma run_set_def : Γ st ⟦buf[offset] ←ᵢ val⟧ = st.set! buf offset st.felts[val]!.get! := rfl
  
lemma run_seq_def : Γ st ⟦p₁; p₂⟧ = Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ := rfl
lemma run_nondet_seq_def : Γ st ⟦nondet(p₁; p₂); p₃⟧ = Γ (Γ st ⟦p₁⟧) ⟦nondet p₂; p₃⟧ := rfl

lemma run_nondet : Γ st ⟦nondet block⟧ = Γ st ⟦block⟧ := rfl

-- lemma run_set_output (x : Felt) (h₁ : st.felts nameₓ = some x) :
--   Γ st ⟦⟨"output"⟩[i] ←ᵢ nameₓ⟧ = { st with output := st.output.set i x } := by simp [run_set_def, h₁]
-- TODO run_set_buffer

-- lemma run_if' : Γ st ⟦guard ⟨name⟩ then branch⟧
--                 = if st.felts ⟨name⟩ = some 0 ∨ ⟨name⟩ ∉ st.felts
--                   then st
--                   else Γ st ⟦branch⟧ := by
--   simp [run]
--   by_cases eq : ⟨name⟩ ∈ st.felts 
--   · have : ∃ a, State.felts st { name := name } = some a := by
--       simp [Map.mem_def, Option.isSome_iff_exists] at eq; exact eq
--     rcases this with ⟨o₁, eq₁⟩; simp [eq₁]
--     by_cases eq₁ : o₁ = 0 <;> simp [eq₁]; simp [eq]
--   · have eq' := eq
--     rw [Map.not_mem_iff_none, Map.getElem_def] at eq
--     simp [eq, eq']

lemma run_if {x : FeltVar} :
  Γ st ⟦guard x then branch⟧ = if st.felts[x]!.get! = 0 then st else Γ st ⟦branch⟧ := rfl

-- lemma run_eqz' : Γ st ⟦@MLIR.Eqz α ⟨name⟩⟧
--                  = if h : ⟨name⟩ ∈ st.felts
--                    then withEqZero ((st.felts ⟨name⟩).get h) st
--                    else st := by simp [run]
--                                  by_cases eq : ⟨name⟩ ∈ st.felts <;> simp [eq]
--                                  · rw [Map.mem_def, Option.isSome_iff_exists] at eq
--                                    aesop
--                                  · rw [Map.not_mem_iff_none] at eq
--                                    aesop

lemma run_eqz {x : FeltVar} :
  Γ st ⟦@MLIR.Eqz α x⟧ = withEqZero st.felts[x]!.get! st := rfl

lemma run_dropfelt {x : FeltVar} :
  Γ st ⟦@MLIR.DropFelt α x⟧ = .dropFelts st x := rfl

-- lemma run_valid_get {st: State} {name: String} {x y: Option Lit} {back offset : ℕ} 
--   (h_cycle: back ≤ st.cycle) (h_vars: ⟨name⟩ ∈ st.vars)
--   (h_offset: offset < st.bufferWidths.get! ⟨name⟩)
--   (h_value: ((st.buffers.get! ⟨name⟩).get! (st.cycle - Back.toNat back, offset)).isSome = true) :
--   (
--     st[name] ←ₛ if
--       back ≤ st.cycle ∧
--       ⟨name⟩ ∈ st.vars ∧
--       offset < st.bufferWidths.get! ⟨name⟩ ∧
--       Option.isSome (Buffer.get! (st.buffers.get! ⟨name⟩) (st.cycle - Back.toNat back, offset)) = true
--     then x
--     else y
--   )
--   =
--   (st[name] ←ₛ x) := by
--   aesop

lemma run_dropFelts_get_buffers :
  (Γ st ⟦@MLIR.DropFelt α x⟧).buffers = st.buffers := by
  simp [MLIR.run, State.dropFelts_buffers]

lemma seq_assoc : Γ state ⟦p₁; (p₂; p₃)⟧ = Γ state ⟦(p₁; p₂); p₃⟧ := by simp [run_seq_def]

lemma seq_step_eq (h: ∀ st : State, Γ st ⟦p₂⟧ = Γ st ⟦p₃⟧):
  Γ state ⟦p₁; p₂⟧ = Γ state ⟦p₁; p₃⟧ := by
  simp [*, MLIR.run_seq_def]

lemma nested_seq_step_eq (h: ∀ st : State, Γ st ⟦p₂; p₃⟧ = Γ st ⟦p₄⟧):
  Γ state ⟦(p₁; p₂); p₃⟧ = Γ state ⟦p₁; p₄⟧ :=
  seq_assoc.symm ▸ seq_step_eq h

lemma nondet_seq_step_eq (h: ∀ st: State, Γ st ⟦nondet s₂; s₃⟧ = Γ st ⟦nondet s₄; s₅⟧) :
  Γ state ⟦nondet (s₁; s₂); s₃⟧ = Γ state ⟦nondet (s₁; s₄); s₅⟧ := by
  aesop

lemma nondet_step_eq (h: ∀ st: State, Γ st ⟦s₂⟧ = Γ st ⟦nondet s₃; s₄⟧) :
  Γ state ⟦nondet s₁; s₂⟧ = Γ state ⟦nondet (s₁; s₃); s₄⟧ := by
  aesop

lemma nondet_end_step_eq (h: ∀ st: State, Γ st ⟦s₂; s₃⟧ = Γ st ⟦s₄⟧) :
  Γ state ⟦(nondet s₁; s₂); s₃⟧ = Γ state ⟦nondet s₁; s₄⟧ := by
  aesop

lemma nondet_blocks_split : Γ state ⟦nondet (s₁; s₂)⟧ = Γ state ⟦nondet s₁; nondet s₂⟧ := by
  simp [run_nondet, run_seq_def]

lemma part_assoc_dddd: Γ state ⟦(p₁; p₂; p₃; p₄); p₅⟧ = Γ state ⟦p₁; p₂; p₃; p₄; p₅⟧ := by aesop
lemma part_assoc_nddd: Γ state ⟦(nondet p₁; p₂; p₃; p₄); p₅⟧ = Γ state ⟦nondet p₁; p₂; p₃; p₄; p₅⟧ := by aesop
lemma part_assoc_dndd: Γ state ⟦(p₁; nondet p₂; p₃; p₄); p₅⟧ = Γ state ⟦p₁;nondet p₂; p₃; p₄; p₅⟧ := by aesop
lemma part_assoc_nndd: Γ state ⟦(nondet (p₁; p₂); p₃; p₄); p₅⟧ = Γ state ⟦nondet p₁; nondet p₂; p₃; p₄; p₅⟧ := by aesop
lemma part_assoc_ddnd: Γ state ⟦(p₁; p₂; nondet p₃; p₄); p₅⟧ = Γ state ⟦p₁; p₂; nondet p₃; p₄; p₅⟧ := by aesop
lemma part_assoc_ndnd: Γ state ⟦(nondet p₁; p₂; nondet p₃; p₄); p₅⟧ = Γ state ⟦nondet p₁; p₂; nondet p₃; p₄; p₅⟧ := by aesop
lemma part_assoc_dnnd: Γ state ⟦(p₁; nondet (p₂; p₃); p₄); p₅⟧ = Γ state ⟦p₁; nondet p₂; nondet p₃; p₄; p₅⟧ := by aesop
lemma part_assoc_nnnd: Γ state ⟦(nondet (p₁; p₂; p₃); p₄); p₅⟧ = Γ state ⟦nondet p₁; nondet p₂; nondet p₃; p₄; p₅⟧ := by aesop
lemma part_assoc_dddn: Γ state ⟦(p₁; p₂; p₃; nondet p₄); p₅⟧ = Γ state ⟦p₁; p₂; p₃; nondet p₄; p₅⟧ := by aesop
lemma part_assoc_nddn: Γ state ⟦(nondet p₁; p₂; p₃; nondet p₄); p₅⟧ = Γ state ⟦nondet p₁; p₂; p₃; nondet p₄; p₅⟧ := by aesop
lemma part_assoc_dndn: Γ state ⟦(p₁; nondet p₂; p₃; nondet p₄); p₅⟧ = Γ state ⟦p₁;nondet p₂; p₃; nondet p₄; p₅⟧ := by aesop
lemma part_assoc_nndn: Γ state ⟦(nondet (p₁; p₂); p₃; nondet p₄); p₅⟧ = Γ state ⟦nondet p₁; nondet p₂; p₃; nondet p₄; p₅⟧ := by aesop
lemma part_assoc_ddnn: Γ state ⟦(p₁; p₂; nondet (p₃; p₄)); p₅⟧ = Γ state ⟦p₁; p₂; nondet p₃; nondet p₄; p₅⟧ := by aesop
lemma part_assoc_ndnn: Γ state ⟦(nondet p₁; p₂; nondet (p₃; p₄)); p₅⟧ = Γ state ⟦nondet p₁; p₂; nondet p₃; nondet p₄; p₅⟧ := by aesop
lemma part_assoc_dnnn: Γ state ⟦(p₁; nondet (p₂; p₃; p₄)); p₅⟧ = Γ state ⟦p₁; nondet p₂; nondet p₃; nondet p₄; p₅⟧ := by aesop
lemma part_assoc_nnnn: Γ state ⟦(nondet (p₁; p₂; p₃; p₄)); p₅⟧ = Γ state ⟦nondet p₁; nondet p₂; nondet p₃; nondet p₄; p₅⟧ := by aesop

lemma isFailed_monotonic : ∀ state : State, state.isFailed → (Γ state ⟦program⟧).isFailed := by
  induction program
  all_goals intros state h_failed
  case Sequence α α₁ prog₁ prog₂ h₁ h₂ =>
    simp [run_seq_def, h₁, h₂, h_failed]
  all_goals simp [MLIR.run, State.update, h_failed]
  case Set =>
    unfold State.set! State.setBufferElementImpl
    rewrite [h_failed]
    aesop
  case SetGlobal =>
    unfold State.setGlobal! State.setBufferElementImpl
    rewrite [h_failed]
    aesop
  all_goals aesop

lemma isFailed_monotonic' : ∀ state : State, (Γ state ⟦program⟧).isFailed = false → state.isFailed = false := by
  induction program
  all_goals intros state h_noFail
  all_goals simp [MLIR.run, State.update, h_noFail] at *
  case Set =>
    unfold State.set! State.setBufferElementImpl at h_noFail
    aesop
  case SetGlobal =>
    unfold State.setGlobal! State.setBufferElementImpl at h_noFail
    aesop
  all_goals aesop

end MLIR

end WithMLIR 

end Risc0
