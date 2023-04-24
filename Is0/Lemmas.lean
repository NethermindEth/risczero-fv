import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Is0.Basic
import Is0.Programs

namespace Risc0

section WithCirgen 

open CirgenNotation

lemma Cirgen.run_Sequence_Assign_collapsible {state : State} {name : String} {op : Op} {program : Cirgen} :
    Γ state ⟦name ←ₐ op; program⟧ = Γ (state[name] := Γ state ⟦op⟧) ⟦program⟧ := by
  cases op <;> conv => lhs; simp [Cirgen.run, State.update, Map.update, beq_iff_eq]

lemma Cirgen.run_Sequence_Set_collapsible
    {state : State}
    {name : String}
    {nameₓ : String}
    {program : Cirgen}
    (buffer : List Felt)
    (x : Felt)
    (h : state.buffers name = some buffer)
    (h₁ : state.felts nameₓ = some x) :
    Γ state ⟦⟨name⟩[i] ←ₐ ⟨nameₓ⟩; program⟧ = 
    Γ { state with buffers := state.buffers[name] := buffer.set i x } ⟦program⟧ := by simp [run, *]

lemma Cirgen.run_if_true {c : Variable Felt}
  (h : st.felts c.name = some 0) :
  Γ st ⟦guard c then prog⟧ = (st, none) := by
  simp only [run]; generalize eq : st.felts c.name = cond
  rcases cond with _ | ⟨x⟩ <;> simp only <;> rw [eq] at h
  · cases h
  · simp; exact λ contra => absurd (by injection h) contra

lemma Cirgen.run_if_false {c : Variable Felt}
  (x : Felt)
  (h₁ : st.felts c.name = some x)
  (h₂ : x ≠ 0) :
  Γ st ⟦guard c then prog⟧ = Γ st ⟦prog⟧ := by
  simp only [run]; generalize eq : st.felts c.name = cond
  rcases cond with _ | ⟨y⟩ <;> simp only <;> rw [eq] at h₁
  · cases h₁
  · simp; intros contra
    rw [contra] at h₁
    injection h₁ with contra
    exact absurd contra.symm h₂

lemma Cirgen.run_seq :
  Γ st ⟦p₁; p₂⟧ = let (st', x) := Γ st ⟦p₁⟧
                  match x with
                    | some x => (st', some x)
                    | none => Γ st' ⟦p₂⟧ := rfl

lemma Cirgen.run_Sequence_If_collapsible
    {state : State}
    {name : String}
    {branch : Cirgen}
    {program : Cirgen}
    (x : Felt)
    (h₁ : state.felts name = some x)
    : Γ state ⟦guard ⟨name⟩ then branch; program⟧
  = if (x == 0)
      then Γ state ⟦program⟧
      else Γ state ⟦branch; program⟧ := by
    generalize eq : (x == 0) = cond
    rw [run_seq]
    rcases cond with _ | _ <;> simp only
    · rw [run_if_false x h₁ (by simp at eq; exact eq)]; rfl
    · rw [run_if_true (by simp at eq; rw [eq] at h₁; exact h₁)]; rfl

lemma Cirgen.run_If_collapsible
    {state : State}
    {name : String}
    {branch : Cirgen}
    (x : Felt)
    (h₁ : state.felts name = some x) :
    Γ state ⟦guard ⟨name⟩ then branch⟧
  = if (x == 0)
      then (state, none)
      else Cirgen.run state branch := by simp [run, h₁]

lemma Cirgen.run_Eqz_collapsible
    {state : State}
    {name : String}
    (x : Felt)
    (h₁ : state.felts name = some x) :
    Γ state ⟦?₀ ⟨name⟩⟧ 
  = ({ state with constraints := x :: state.constraints }, none) := by simp [run, *]

lemma Cirgen.run_Sequence_Eqz_collapsible
    {state : State}
    {name : String}
    {program : Cirgen}
    (x : Felt)
    (h₁ : state.felts name = some x) :
    Cirgen.run state (.Sequence (.Eqz (Variable.mk name)) program)
  = let state₁ := { state with constraints := x :: state.constraints }
    let (state₂, y) := Cirgen.run state₁ program
    (state₂, y) := by rw [run_seq, run_Eqz_collapsible _ h₁]

end WithCirgen 

end Risc0
