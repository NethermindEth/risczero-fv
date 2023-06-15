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

lemma seq_assoc : Γ state ⟦p₁; (p₂; p₃)⟧ = Γ state ⟦(p₁; p₂); p₃⟧ := by simp [run_seq_def]

end MLIR

end WithMLIR 

end Risc0
