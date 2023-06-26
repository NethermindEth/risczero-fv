import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Risc0.Basic

namespace Risc0

section WithMLIR 

variable {α : IsNondet} {st : State} {name : String}

open MLIRNotation IsNondet
open Risc0.VarType

namespace MLIR

lemma run_ass_def : Γ st ⟦name ←ₐ op⟧ = st[name] ←ₛ Γ st ⟦op⟧ₑ := rfl

lemma run_set_def : Γ st ⟦buf[offset] ←ᵢ val⟧ = st.set! buf offset st.felts[val]!.get! := rfl
  
lemma run_seq_def : Γ st ⟦p₁; p₂⟧ = Γ (Γ st ⟦p₁⟧) ⟦p₂⟧ := rfl

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
  Γ st ⟦guard x then branch⟧ = if st.felts[x]!.get! = 0 then st else branch.run st := rfl

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

lemma seq_assoc : Γ state ⟦p₁; (p₂; p₃)⟧ = Γ state ⟦(p₁; p₂); p₃⟧ := by simp [run_seq_def]

lemma nondet_blocks_split : Γ state ⟦nondet (s₁; s₂)⟧ = Γ state ⟦nondet s₁; nondet s₂⟧ := by
  simp [run_nondet, run_seq_def]

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

-- REVIEW does this require classical logic to get from isFailed_monotonic
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

open Op in
def allGetsValid {α} (st: State) (program: MLIR α) : Prop :=
  match program with
    | Assign _ op => match op with
      | Get buf back offset  => isGetValid st buf back offset
      | _                    => True --TODO add getGlobal case
    | If x p         => st.felts[x]!.get! ≠ 0 → allGetsValid st p
    | Nondet block   => allGetsValid st block
    | Sequence p₁ p₂ => allGetsValid st p₁ ∧ allGetsValid (Γ st ⟦p₁⟧) p₂
    | _              => True

lemma allGetsValid_of_not_isFailed : ∀ st : State, ¬(Γ st ⟦program⟧).isFailed → allGetsValid st program := by
  induction program with
    | Assign name op =>
      simp [allGetsValid]
      intros st h_noFail
      cases op with
        | Get buf back offset =>
          simp [MLIR.run, Op.eval, getImpl, State.update] at *
          aesop
        | _ => aesop
    | If x p h                 => simp [h, MLIR.run, allGetsValid]; aesop
    | Nondet block h           => simp [h, MLIR.run, allGetsValid]; aesop
    | Eqz x                    => simp [allGetsValid]
    | Fail                     => simp [allGetsValid]
    | Set buf offset val       => simp [allGetsValid]
    | SetGlobal buf offset val => simp [allGetsValid]
    | Sequence p₁ p₂ h₁ h₂ =>
      intros state h_noFail
      simp [allGetsValid]
      apply And.intro
      all_goals simp only [Bool.not_eq_true] at *
      case Sequence.left =>
        have h_noFail₁: (Γ state ⟦p₁⟧).isFailed = false := isFailed_monotonic' (Γ state ⟦p₁⟧) h_noFail
        simp [h₁, h_noFail₁]
      case Sequence.right =>
        simp [MLIR.run] at h_noFail
        exact h₂ (Γ state ⟦p₁⟧) h_noFail

lemma nondet_seq_is_nondet_nondet {st : State} {p₀ p₁ : MLIR IsNondet.InNondet} :
  MLIR.run (MLIR.Nondet (MLIR.Sequence p₀ p₁)) st = MLIR.run (MLIR.Sequence (MLIR.Nondet p₀) (MLIR.Nondet p₁)) st := by rfl

end MLIR

end WithMLIR 

end Risc0
