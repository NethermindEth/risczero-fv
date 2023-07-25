import Risc0.Cirgen.BasicTypes
import Risc0.State.Defs

namespace Risc0

  open IsNondet

  -- Pure functional operations from the cirgen (circuit generation) MLIR dialect.
  open VarType in
  inductive Op : IsNondet → Type where
    -- Constants
    | Const : Felt → Op x
    | True  : Op x
    -- Arith
    | Add : FeltVar → FeltVar → Op x
    | Sub : FeltVar → FeltVar → Op x
    | Neg : FeltVar           → Op x
    | Mul : FeltVar → FeltVar → Op x
    | Pow : FeltVar → ℕ       → Op x
    | BitAnd : FeltVar → FeltVar → Op x
    | Inv : FeltVar           → Op InNondet
    -- Logic
    | Isz : FeltVar → Op InNondet
    -- Constraints
    | AndEqz  : PropVar → FeltVar           → Op x
    | AndCond : PropVar → FeltVar → PropVar → Op x
    -- Buffers
    | Alloc     : ℕ                    → Op x
    | Back      : BufferVar → ℕ        → Op x
    | Get       : BufferVar → Back → ℕ → Op x
    | GetGlobal : BufferVar → ℕ        → Op x
    | Slice     : BufferVar → ℕ    → ℕ → Op x

  def isGetValid (st : State) (buf : BufferVar) (back : Back) (offset : ℕ) :=
    back ≤ st.cycle ∧
    buf ∈ st.vars ∧
    offset < st.bufferWidths[buf].get! ∧
    (Buffer.back st buf back offset).isSome
  instance : Decidable (isGetValid st buf back offset) := by unfold isGetValid; exact inferInstance

  def getImpl (st : State) (buf : BufferVar) (back : Back) (offset : ℕ) :=
    if isGetValid st buf back offset
    then Option.some <| Lit.Val (Buffer.back st buf back offset).get!
    else .none

  -- Evaluate a pure functional circuit.
  def Op.eval {x} (st : State) (op : Op x) : Option Lit :=
    match op with
      -- Constants
      | Const const => .some <| .Val const
      -- Arith
      | Add lhs rhs => .some <| .Val <| st.felts[lhs].get! + st.felts[rhs].get!
      | Sub lhs rhs => .some <| .Val <| st.felts[lhs].get! - st.felts[rhs].get!
      | Neg lhs     => .some <| .Val <| 0                  - st.felts[lhs].get!
      | Mul lhs rhs => .some <| .Val <| st.felts[lhs].get! * st.felts[rhs].get!
      | Pow lhs rhs => .some <| .Val <| st.felts[lhs].get! ^ rhs
      | BitAnd lhs rhs => .some <| .Val <| feltBitAnd st.felts[lhs].get! st.felts[rhs].get!
      | Inv x => .some <| .Val <| if st.felts[x]!.get! = 0 then 0 else st.felts[x]!.get!⁻¹
      -- Logic
      | Isz x => .some <| .Val <| if st.felts[x]!.get! = 0 then 1 else 0
      -- Constraints
      | AndEqz c val           => .some <| .Constraint <| st.props[c].get! ∧ st.felts[val].get! = 0
      | AndCond old cond inner =>
          .some <| .Constraint <| st.props[old].get! ∧
                                  if st.felts[cond].get! = 0
                                  then _root_.True
                                  else st.props[inner].get!
      | True                   => .some <| .Constraint _root_.True
      -- Buffers
      | Alloc size           => .some <| .Buf <| List.replicate size .none
      | Back buf back        => .some <| .Buf <| st.buffers[buf].get![st.cycle]!.slice 0 back
      | Get buf back offset  => getImpl st buf back offset
      | GetGlobal buf offset => if buf ∈ st.vars
                                then
                                  let buffer := st.buffers[buf].get!
                                  let bufferWidth := st.bufferWidths[buf].get!
                                  let idx := Buffer.Idx.from1D offset bufferWidth -- the implementation of getGlobal steps directly into the 1D representation of whatever buffer it is passed
                                  let val := buffer.get! idx
                                  if idx.time < buffer.length ∧ val.isSome
                                  then .some <| .Val val.get!
                                  else .none
                                else .none
      | Slice buf offset size => .some <| .Buf <| (List.get! (st.buffers buf).get! (st.cycle - 1)).slice offset size

  instance : HAdd (FeltVar) (FeltVar) (Op IsNondet.InNondet)    := ⟨Op.Add⟩
  instance : HAdd (FeltVar) (FeltVar) (Op IsNondet.NotInNondet) := ⟨Op.Add⟩

  instance : HSub (FeltVar) (FeltVar) (Op IsNondet.InNondet)    := ⟨Op.Sub⟩
  instance : HSub (FeltVar) (FeltVar) (Op IsNondet.NotInNondet) := ⟨Op.Sub⟩

  instance : HMul (FeltVar) (FeltVar) (Op IsNondet.InNondet)    := ⟨Op.Mul⟩
  instance : HMul (FeltVar) (FeltVar) (Op IsNondet.NotInNondet) := ⟨Op.Mul⟩

  instance : HPow (FeltVar) ℕ (Op IsNondet.InNondet)    := ⟨Op.Pow⟩
  instance : HPow (FeltVar) ℕ (Op IsNondet.NotInNondet) := ⟨Op.Pow⟩

  inductive MLIR : IsNondet → Type where
    -- Meta
    | Assign    : String        → Op x   → MLIR x
    | DropFelt  : FeltVar                → MLIR x
    | Eqz       : FeltVar                → MLIR x
    | If        : FeltVar       → MLIR x → MLIR x
    | Nondet    : MLIR InNondet          → MLIR NotInNondet
    | Noop      :                          MLIR x
    | Sequence  : MLIR x        → MLIR x → MLIR x
    -- Ops
    | Fail      :                           MLIR x
    | Set       : BufferVar → ℕ → FeltVar → MLIR InNondet
    | SetGlobal : BufferVar → ℕ → FeltVar → MLIR InNondet
    -- Extern
        -- Extern
    | PlonkAccumRead  : BufferVar → ℕ → MLIR x
    | PlonkAccumWrite : BufferVar → List FeltVar → ℕ → MLIR x
    | PlonkRead       : BufferVar → ℕ → MLIR x
    | PlonkWrite      : BufferVar → List FeltVar → ℕ → MLIR x

  abbrev MLIRProgram := MLIR NotInNondet

  inductive ExternPlonkBuffer | PlonkRows | PlonkAccumRows
  deriving DecidableEq

  instance : ToString ExternPlonkBuffer := ⟨
    (match · with | .PlonkRows => "PlonkRows" | .PlonkAccumRows => "PlonkAccumRows")
  ⟩

  def mangle (table : ExternPlonkBuffer) (discr : BufferVar) : String :=
    toString table ++ discr.name

  namespace MLIR.ExternOp
    section

      variable (buf : BufferVar) (args : List FeltVar) (outCount : ℕ)

      def plonkExternWrite (discr : ExternPlonkBuffer) (st : State) : State := 
        if outCount = 0
        then (st.allocateBufferRow! buf args.length).setMany! ⟨mangle discr buf⟩ args
        else {st with isFailed := true}

      def plonkExternRead (discr : ExternPlonkBuffer) : MLIR x := Sequence Noop Noop

    end
  end MLIR.ExternOp  

  -- Step through the entirety of a `MLIR` MLIR program from initial state
  -- `state`, yielding the post-execution state and possibly a constraint
  -- (`Prop`), the return value of the program.
  def MLIR.run {α : IsNondet} (program : MLIR α) (st : State) : State :=
    match program with
      -- Meta
      -- | Assign name op => st[name] ←ₛ Γ st ⟦op⟧ₑ
      | Assign name op => st.update name (op.eval st)
      | DropFelt k     => .dropFelts st k
      | Eqz x          => withEqZero st.felts[x]!.get! st
      | If x program   => if st.felts[x]!.get! = 0 then st else program.run st
      | Nondet block   => block.run st
      | Noop           => st
      | Sequence a b   => b.run (a.run st)
      -- Ops
      | Fail                     => {st with isFailed := true}
      | Set buf offset val       => st.set! buf offset st.felts[val]!.get!
      | SetGlobal buf offset val => st.setGlobal! buf offset st.felts[val]!.get! -- Behind the scenes setGlobal actually flattens a 2d buffer into a 1d buffer
                                                                                -- and indexes into it. This is a side effect of global buffers only being 1d anyway
      | PlonkAccumRead buf outCount => (ExternOp.plonkExternRead .PlonkAccumRows).run (α := IsNondet.InNondet) st
      | PlonkAccumWrite buf args outCount => ExternOp.plonkExternWrite buf args outCount .PlonkAccumRows st
      | PlonkRead buf outCount => (ExternOp.plonkExternRead .PlonkRows).run (α := IsNondet.InNondet) st
      | PlonkWrite buf args outCount => ExternOp.plonkExternWrite buf args outCount .PlonkRows st 

  @[simp]
  abbrev MLIR.runProgram (program : MLIRProgram) := program.run

end Risc0
