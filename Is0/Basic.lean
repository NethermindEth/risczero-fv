import Mathlib.Data.Nat.Prime
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch

namespace Risc0

@[inline]
def P: ℕ := 15 * 2^27 + 1

axiom P_prime: Nat.Prime P 
instance : Fact (Nat.Prime P) := ⟨P_prime⟩

-- A finite field element.
abbrev Felt := ZMod P

-- A literal, either a finite field element or a constraint.
inductive Lit where
  | Val : Felt → Lit
  | Constraint : Prop → Lit

-- A functional map, used to send variable names to literal values.
def Map (α : Type) (β : Type) := α → Option β

@[simp]
def Map.empty {α : Type} {β : Type} : Map α β := λ _ => none

@[simp]
def Map.update {α : Type} [BEq α] {β : Type} (m : Map α β) (k : α) (v : β) : Map α β :=
  λ x => if x == k then v else m x

notation:61 st "[" n:61 "]" " := " x:49 => Map.update st n x

@[simp]
def Map.fromList {α : Type} [BEq α] {β : Type} (l : List (α × β)) : Map α β :=
  match l with
  | [] => Map.empty
  | (k, v) :: xs => Map.update (Map.fromList xs) k v

-- The first three fields map variable names to values. The last is an
-- append-only stack of the expressions we assert are equal to zero via `Eqz`.
structure State where
  felts : Map String Felt
  props : Map String Prop
  buffers : Map String (List Felt)
  constraints : List Felt

@[simp]
def State.update (state : State) (name : String) (x : Lit) : State :=
  match x with
  | .Val x => { state with felts := state.felts.update name x }
  | .Constraint c => { state with props := state.props.update name c }

notation:61 st "[" n:61 "]" " := " x:49 => State.update st n x

-- A parametrized Variable. In practice, α will be one of `Felt`, `Prop`, or `List Felt`.
structure Variable (α : Type) :=
  name : String

-- Pure functional operations from the cirgen (circuit generation) MLIR dialect.
inductive Op where
  | Const : Felt → Op
  | True : Op
  | Get : Variable (List Felt) → ℕ → Felt → Op
  | Sub : Variable Felt → Variable Felt → Op
  | Mul : Variable Felt → Variable Felt → Op
  | Isz : Variable Felt → Op
  | Inv : Variable Felt → Op
  | AndEqz : Variable Prop → Variable Felt → Op
  | AndCond : Variable Prop → Variable Felt → Variable Prop → Op

namespace MLIRNotation

-- scoped notation:56 (priority := high) "[" x "]" => ⟨x⟩

end MLIRNotation

-- Notation for Ops.
namespace MLIRNotation

instance {n} : OfNat Op n := ⟨.Const n⟩
instance : Coe Felt Op := ⟨(.Const ·)⟩

scoped infixl:55 (priority := high) " - " => Op.Sub
scoped infixl:55 (priority := high) " * " => Op.Mul
scoped infix:55 " &₀ " => Op.AndEqz
scoped notation:55 c " guard " x " & " y:55 => Op.AndCond c x y
scoped notation:max "⊤" => Op.True
scoped notation:max "input[" n "]" => Op.Get ⟨"in"⟩ n 0
scoped notation:max "output[" n "]" => Op.Get ⟨"out"⟩ n 0
scoped prefix:57 "??₀" => Op.Isz
scoped prefix:max "Inv" => Op.Inv

-- scoped prefix:max "C" => Op.Const


end MLIRNotation

@[simp]
lemma Op.coe_eq_const {n : ℕ} : (↑n : Felt) = Op.Const n := rfl

instance : Inhabited Lit := ⟨(Lit.Val (-42))⟩

-- Evaluate a pure functional circuit operation to get some kind of literal.
def Op.eval (state : State) (op : Op) : Lit :=
  match op with
  | Const x => .Val x
  | True => .Constraint (_root_.True)
  | Get buffer i _ => match state.buffers buffer.name with
                        | some v => .Val <| v.getD i (-42)
                        | _      => default
  | Sub x y => let ⟨i⟩ := x
               let ⟨j⟩ := y
               .Val $ match state.felts i, state.felts j with
                 | some x, some y => x - y
                 | _      , _       => 42
  | Mul x y => let ⟨i⟩ := x
               let ⟨j⟩ := y
               .Val $ match state.felts i, state.felts j with
                 | some x, some y => x * y
                 | _      , _       => 42
  | AndEqz c x => let ⟨i⟩ := c
                  let ⟨j⟩ := x
                  match state.props i, state.felts j with
                    | some c, some x => .Constraint (c ∧ x = 0)
                    | _      , _       => .Constraint (42 = 42)
  | AndCond old cond inner =>
      let ⟨i⟩ := old
      let ⟨j⟩ := cond
      let ⟨k⟩ := inner
      match state.props i, state.felts j, state.props k with
        | .some old, .some cond, .some inner => .Constraint (if cond == 0 then old else old ∧ inner)
        | _        , _         , _           => .Constraint (42 = 42)
  | Isz x => let ⟨i⟩ := x
             match state.felts i with
             | some x => .Val $ if x == 0 then 1 else 0
             | _      => .Val 42
  | Inv x => let ⟨i⟩ := x
             match state.felts i with
             | some x => .Val $ if x == 0 then 0 else x⁻¹
             | _      => .Val 42

notation:61 "Γ " st:max " ⟦" p:49 "⟧" => Op.eval st p

-- Evaluate `op` and map `name ↦ result` in `state : State`.
def Op.assign (state : State) (op : Op) (name : String) : State :=
  match (Op.eval state op) with
  | .Val x => { state with felts := state.felts.update name x }
  | .Constraint c => { state with props := state.props.update name c }

-- An MLIR program in the `cirgen` (circuit generation) dialect. MLIR ops that
-- are not pure functions are implemented here, so they can mess with state. 
inductive MLIR where
  | If : Variable Felt → MLIR → MLIR
  | Eqz : Variable Felt → MLIR
  | Set : Variable (List Felt) → ℕ → Variable Felt → MLIR
  | ReturnPair : String → String → MLIR
  | Assign : String → Op → MLIR
  | Sequence : MLIR → MLIR → MLIR

namespace MLIRNotation

-- Notation for MLIR programs.
scoped infixr:50 "; " => MLIR.Sequence
scoped infix:51 "←ₐ " => MLIR.Assign
scoped notation:max "ret [" x "," y "]" => MLIR.ReturnPair x y
scoped notation:51 (priority := high) "[" v "]" " ←ₐ " x:51 => MLIR.Set ⟨"out"⟩ v x
scoped notation:51 (priority := high) str "[" v "]" " ←ₐ " x:51 => MLIR.Set str v x
scoped notation:51 "guard " c " then " x:51 => MLIR.If c x
scoped prefix:52 "?₀" => MLIR.Eqz

end MLIRNotation
-- Step through the entirety of a `MLIR` MLIR program from initial state
-- `state`, yielding the post-execution state and possibly a constraint
-- (`Prop`), the return value of the program.
def MLIR.run (state : State) (program : MLIR) : State × Option (Felt × Felt) :=
  match program with
  | If x program =>
    let ⟨name⟩ := x
    match state.felts name with
      | .some x => if x == 0
                   then (state, none)
                   else MLIR.run state program
      | none    => (state, some (42, 42))
  | Eqz x =>
    let ⟨name⟩ := x
    match state.felts name with
      | .some x => ({ state with constraints := x :: state.constraints }, none)
      | .none   => (state, some (42, 42))
  | Set buffer i x =>
    let ⟨name⟩ := buffer
    let ⟨nameₓ⟩ := x
      match state.buffers name, state.felts nameₓ with
        | .some buffer, .some x =>
          let buffers' := state.buffers.update name (buffer.set i x)
          ({state with buffers := buffers' }, none)
        | _, _ => (state, none)
  | Assign name op => (Op.assign state op name, none)
  | Sequence a b => let (state', x) := MLIR.run state a
                    match x with
                      | some x => (state', some x)
                      | none => MLIR.run state' b
  | ReturnPair name₁ name₂ => let retval:=
                    match state.felts name₁, state.felts name₂ with
                    | some x, some y => (x, y)
                    | _     , _      => (42, 42)
                   (state, some retval)

notation:61 "Γ " st:max " ⟦" p:49 "⟧" => MLIR.run st p

end Risc0
