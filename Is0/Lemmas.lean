import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

import Is0.Basic
import Is0.Programs

namespace Risc0

lemma Cirgen.step_Sequence_Assign_collapsible :
  ∀ (state : State) (name : String) (op : Op) (program : Cirgen),
  Cirgen.step state (.Sequence (.Assign name op) program) = Cirgen.step (state.update name (Op.eval state op)) program := by
  intros state name op program
  cases op <;> {
    conv =>
      lhs
      unfold Cirgen.step
  }

lemma Cirgen.step_Sequence_Set_collapsible
    {state : State}
    {name : String}
    {nameₓ : String}
    {program : Cirgen}
    (buffer : List Felt)
    (x : Felt)
    (h : state.buffers name = some buffer)
    (h₁ : state.felts nameₓ = some x) :
    Cirgen.step state (.Sequence (.Set (Variable.mk name) i (Variable.mk nameₓ)) program)
  = let buffers' := state.buffers.update name (buffer.set i x)
    Cirgen.step ({ state with buffers := buffers' }) program := by
  conv =>
    lhs
    unfold step
  conv in step state (Set (Variable.mk name) i (Variable.mk nameₓ)) =>
    unfold step
  simp only [ne_eq, decide_not]
  rw [h]
  rw [h₁]

lemma Cirgen.step_Sequence_If_collapsible
    {state : State}
    {name : String}
    {branch : Cirgen}
    {program : Cirgen}
    (x : Felt)
    (h₁ : state.felts name = some x)
    (hab : step state program ≠ step state (Sequence branch program))
    (hhh : (state, none) ≠ step state branch) :
    Cirgen.step state (.Sequence (.If (Variable.mk name) branch) program)
  = if (x == 0)
      then Cirgen.step state program
      else Cirgen.step state (.Sequence branch program) := by
  simp only [beq_iff_eq]
  let a := step state program
  let b := step state (Sequence branch program)
  have ha : a = step state program := by simp only
  have hb : b = step state (Sequence branch program) := by simp only
  rw [← ha]
  rw [← hb]
  by_cases x = 0
  have hh := (@Ne.ite_eq_left_iff (State × Option Prop) (x = 0) _ a b hab).2 h
  rw [hh]
  conv =>
    lhs
    unfold step
    unfold step
  simp only [beq_iff_eq]
  rw [h₁]
  simp only
  have hh₁ := (@Ne.ite_eq_left_iff (State × Option Prop) (x = 0) _ (state, none) (step state branch) hhh).2 h
  rw [hh₁]
  simp only
  conv =>
    rhs
    unfold step
  simp only [beq_iff_eq]
  rw [←ite_not]
  have hba : b ≠ a := by
    rw [ha]
    rw [hb]
    rw [ne_comm]
    exact hab
  have hh := (@Ne.ite_eq_left_iff (State × Option Prop) (¬x = 0) _ b a hba).2 h
  rw [hh]
  conv =>
    lhs
    unfold step
    unfold step
  simp only [beq_iff_eq]
  rw [h₁]
  simp only
  rw [←ite_not]
  have hhhh : step state branch ≠ (state, none) := by
    rw [ne_comm]
    exact hhh
  have hh₁ := (@Ne.ite_eq_left_iff (State × Option Prop) (¬x = 0) _ (step state branch) (state, none) hhhh).2 h
  rw [hh₁]
  simp only
  conv =>
    rhs
    unfold step
  simp only [beq_iff_eq]
  conv in (step (step state branch).fst program) =>
    unfold step
  simp only [beq_iff_eq]

lemma Cirgen.step_If_collapsible
    {state : State}
    {name : String}
    {branch : Cirgen}
    (x : Felt)
    (h₁ : state.felts name = some x) :
    Cirgen.step state (.If (Variable.mk name) branch)
  = if (x == 0)
      then (state, none)
      else Cirgen.step state branch := by
  conv =>
    lhs
    unfold step
  simp only [beq_iff_eq]
  rw [h₁]
  done

lemma Cirgen.step_Eqz_collapsible
    {state : State}
    {name : String}
    (x : Felt)
    (h₁ : state.felts name = some x) :
    Cirgen.step state (.Eqz (Variable.mk name))
  = ({ state with constraints := (x = 0) :: state.constraints }, none) := by
  conv =>
    lhs
    unfold step
  simp only [beq_iff_eq]
  rw [h₁]
  done

lemma Cirgen.step_Sequence_Eqz_collapsible
    {state : State}
    {name : String}
    {program : Cirgen}
    (x : Felt)
    (h₁ : state.felts name = some x) :
    Cirgen.step state (.Sequence (.Eqz (Variable.mk name)) program)
  = let state₁ := { state with constraints := (x = 0) :: state.constraints }
    let (state₂, y) := Cirgen.step state₁ program
    (state₂, y) := by
  simp only [Prod.mk.eta]
  conv =>
    lhs
    unfold step
  simp only
  rw [Cirgen.step_Eqz_collapsible x]
  exact h₁

lemma hab {x y z : Felt} : Cirgen.step
    {
      felts := fun x_1 =>
        if x_1 = "out[0]" then some 0
        else
          if x_1 = "invVal" then some x⁻¹
          else if x_1 = "isZeroBit" then some 0 else if x_1 = "x" then some x else if x_1 = "1" then some 1 else none,
      props := fun _ => none,
      buffers := fun x_1 =>
        if x_1 = "out" then some (0 :: List.set [z] 0 x⁻¹)
        else
          if x_1 = "out" then some [0, z]
          else if x_1 = "in" then some [x] else if x_1 = "out" then some [y, z] else none,
      constraints := [] }
    (Cirgen.Sequence (Cirgen.Assign "1 - out[0]" (Op.Sub (Variable.mk "1") (Variable.mk "out[0]")))
      (Cirgen.If (Variable.mk "1 - out[0]")
        (Cirgen.Sequence (Cirgen.Assign "out[1]" (Op.Get (Variable.mk "out") 1 0))
          (Cirgen.Sequence (Cirgen.Assign "x * out[1]" (Op.Mul (Variable.mk "x") (Variable.mk "out[1]")))
            (Cirgen.Sequence (Cirgen.Assign "x * out[1] - 1" (Op.Sub (Variable.mk "x * out[1]") (Variable.mk "1")))
              (Cirgen.Eqz (Variable.mk "x * out[1] - 1"))))))) ≠
  Cirgen.step
    {
      felts := fun x_1 =>
        if x_1 = "out[0]" then some 0
        else
          if x_1 = "invVal" then some x⁻¹
          else if x_1 = "isZeroBit" then some 0 else if x_1 = "x" then some x else if x_1 = "1" then some 1 else none,
      props := fun _ => none,
      buffers := fun x_1 =>
        if x_1 = "out" then some (0 :: List.set [z] 0 x⁻¹)
        else
          if x_1 = "out" then some [0, z]
          else if x_1 = "in" then some [x] else if x_1 = "out" then some [y, z] else none,
      constraints := [] }
    (Cirgen.Sequence (Cirgen.Eqz (Variable.mk "x"))
      (Cirgen.Sequence (Cirgen.Assign "1 - out[0]" (Op.Sub (Variable.mk "1") (Variable.mk "out[0]")))
        (Cirgen.If (Variable.mk "1 - out[0]")
          (Cirgen.Sequence (Cirgen.Assign "out[1]" (Op.Get (Variable.mk "out") 1 0))
            (Cirgen.Sequence (Cirgen.Assign "x * out[1]" (Op.Mul (Variable.mk "x") (Variable.mk "out[1]")))
              (Cirgen.Sequence (Cirgen.Assign "x * out[1] - 1" (Op.Sub (Variable.mk "x * out[1]") (Variable.mk "1")))
                (Cirgen.Eqz (Variable.mk "x * out[1] - 1")))))))) := by
  unfold List.set
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.update, beq_iff_eq, ne_eq]
  unfold Op.eval ; simp only [sub_zero]
  rw [Cirgen.step_If_collapsible 1]
  simp only [ite_false]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.update, beq_iff_eq]
  unfold Op.eval
  simp only [ite_true, ite_false, List.getD_cons_succ, List.getD_cons_zero]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.update, beq_iff_eq]
  unfold Op.eval
  simp only [ite_false, ite_true, ne_eq]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.update, beq_iff_eq]
  unfold Op.eval
  simp only [ite_false, ite_true, ne_eq]
  rw [Cirgen.step_Eqz_collapsible (x * x⁻¹ - 1)]
  simp only
  rw [Cirgen.step_Sequence_Eqz_collapsible x]
  simp only [ne_eq, Prod.mk.eta]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.update, beq_iff_eq]
  unfold Op.eval
  simp only [ne_eq, ite_true, ite_false, sub_zero]
  rw [Cirgen.step_If_collapsible 1]
  simp only [ite_false]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [State.update, Map.update, beq_iff_eq]
  unfold Op.eval
  simp only [ne_eq, ite_true, ite_false, List.getD_cons_succ, List.getD_cons_zero]
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [ne_eq, State.update, Map.update, beq_iff_eq]
  unfold Op.eval ; simp only
  rw [Cirgen.step_Sequence_Assign_collapsible]
  simp only [ne_eq, State.update, Map.update, beq_iff_eq]
  unfold Op.eval ; simp only
  rw [Cirgen.step_Eqz_collapsible (x * x⁻¹ - 1)]
  simp only [ne_eq, Prod.mk.injEq, State.mk.injEq, List.cons.injEq, and_false, and_true, not_false_iff]
  simp only [ite_false, ite_true]
  simp only [ite_false, ite_true]
  simp only [ite_false, ite_true]
  simp only [ite_false, ite_true]
  simp only [ite_false, ite_true]

end Risc0
