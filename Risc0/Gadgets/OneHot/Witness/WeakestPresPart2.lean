import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart1

namespace Risc0.OneHot.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part₂ on st
def part₂_state (st: State) : State :=
  (State.set!
          ((State.set! st { name := "output" } 1
                (Option.get! st.felts[({ name := "input == 1" }: FeltVar)]!)[felts][{ name := "input - 2" }] ←
              Option.get! (State.felts st { name := "input" }) -
                Option.get! (State.felts st { name := "2" }))[felts][{ name := "input == 2" }] ←
            if Option.get! (State.felts st { name := "input" }) - Option.get! (State.felts st { name := "2" }) = 0 then
              1
            else 0)
          { name := "output" } 2
          (if Option.get! (State.felts st { name := "input" }) - Option.get! (State.felts st { name := "2" }) = 0 then 1
          else 0))

-- Run the program from part₂ onwards by using part₂_state rather than Code.part₂
def part₂_state_update (st: State): State :=
  Γ (part₂_state st) ⟦Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈⟧

-- Prove that substituting part₂_state for Code.part₂ produces the same result
lemma part₂_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram (Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₂_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈) = prog
  unfold Code.part₂
  MLIR
  rewrite [←eq]
  unfold part₂_state_update part₂_state
  rfl

-- lemma part₂_updates_opaque {st : State} : 
--   (part₁_state_update st).lastOutput = [y₁, y₂, y₃] ↔
--   (part₂_state_update (part₁_state st)).lastOutput = [y₁, y₂, y₃] := by
--   simp [part₁_state_update, part₂_wp]

def part₂₀_state (st : State) : State := (State.set! st { name := "output" } 1 (Option.get! (st.felts[({ name := "input == 1" } : FeltVar)]!)))
        
def part₂₀_state_update (st: State) : State :=
  Γ (part₂₀_state st) ⟦Code.part₂₁; Code.part₂₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈⟧

lemma part₂₀_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram (Code.part₂₀; Code.part₂₁; Code.part₂₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈) st).lastOutput = [y₁, y₂, y₃] ↔ 
  (part₂₀_state_update st).lastOutput = [y₁, y₂, y₃]  := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₂₁; Code.part₂₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈) = prog
  unfold Code.part₂₀
  MLIR
  rewrite [←eq]
  unfold part₂₀_state_update part₂₀_state
  rfl

lemma part₂₀_updates_opaque {st : State} : 
  (part₁_state_update st).lastOutput = [y₁, y₂, y₃] ↔
  (part₂₀_state_update (part₁_state st)).lastOutput = [y₁, y₂, y₃] := by
  simp [part₁_state_update, part₂₀_wp]

def part₂₁_state (st : State) : State := 
  let input := Option.get! (State.felts st { name := "input" })
  let two := Option.get! (State.felts st { name := "2" })
  ((st[felts][{ name := "input - 2" }] ←
            input - two)[felts][{ name := "input == 2" }] ←
          if input - two = 0 then 1
          else 0)
        
def part₂₁_state_update (st: State) : State :=
  Γ (part₂₁_state st) ⟦Code.part₂₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈⟧

lemma part₂₁_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram (Code.part₂₁; Code.part₂₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈) st).lastOutput = [y₁, y₂, y₃] ↔ 
  (part₂₁_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₂₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈) = prog
  unfold Code.part₂₁
  MLIR
  rewrite [←eq]
  unfold part₂₁_state_update part₂₁_state
  rfl

lemma part₂₁_updates_opaque {st : State} : 
  (part₂₀_state_update st).lastOutput = [y₁, y₂, y₃] ↔
  (part₂₁_state_update (part₂₀_state st)).lastOutput = [y₁, y₂, y₃] := by
  simp [part₂₀_state_update, part₂₁_wp]

def part₂₂_state (st : State) : State := State.set! st { name := "output" } 2 (Option.get! st.felts[({ name := "input == 2" } : FeltVar)]!)
        
def part₂₂_state_update (st: State) : State :=
  Γ (part₂₂_state st) ⟦Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈⟧

lemma part₂₂_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram (Code.part₂₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈) st).lastOutput = [y₁, y₂, y₃] ↔ 
  (part₂₂_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈) = prog
  unfold Code.part₂₂
  MLIR
  rewrite [←eq]
  unfold part₂₂_state_update part₂₂_state
  rfl

lemma part₂₂_updates_opaque {st : State} : 
  (part₂₁_state_update st).lastOutput = [y₁, y₂, y₃] ↔
  (part₂₂_state_update (part₂₁_state st)).lastOutput = [y₁, y₂, y₃] := by
  simp [part₂₁_state_update, part₂₂_wp]

end Risc0.OneHot.Witness.WP
