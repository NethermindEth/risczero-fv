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

  @[default_instance] noncomputable
  instance : SizeOf (Op x) where
    sizeOf _ := 1

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
    | Barrier   :                           MLIR x
    | Fail      :                           MLIR x
    | Set       : BufferVar → ℕ → FeltVar → MLIR InNondet
    | SetGlobal : BufferVar → ℕ → FeltVar → MLIR InNondet
    -- Extern
        -- Extern
    | PlonkAccumRead  : BufferVar → ℕ                → MLIR InNondet
    | PlonkAccumWrite : BufferVar → List FeltVar → ℕ → MLIR InNondet
    | PlonkRead       : BufferVar → ℕ                → MLIR InNondet
    | PlonkWrite      : BufferVar → List FeltVar → ℕ → MLIR InNondet

  abbrev MLIRProgram := MLIR NotInNondet

  inductive ExternPlonkBuffer | PlonkRows | PlonkAccumRows
  deriving DecidableEq

  @[simp]
  lemma sizeOf_ExternPlonkBuffer {x : ExternPlonkBuffer} : sizeOf x = 1 := by
    cases x <;> simp

  instance : ToString ExternPlonkBuffer := ⟨
    (match · with | .PlonkRows => "PlonkRows" | .PlonkAccumRows => "PlonkAccumRows")
  ⟩

  def mangle (table : ExternPlonkBuffer) (discr : BufferVar) : String :=
    toString table ++ discr.name

  namespace MLIR.ExternOp
    section

      variable (buf : BufferVar) (args : List FeltVar) (outCount : ℕ)

      def memoryName (mangledName : String) := "mem" ++ mangledName

      def plonkExternWrite (discr : ExternPlonkBuffer) (st : State) : State := 
        let mangledName := mangle discr buf
        if outCount = 0
        then st.allocateBufferRow! ⟨mangledName⟩ args.length |>.setMany! ⟨mangledName⟩ args
             |>.allocateBufferRow! ⟨memoryName mangledName⟩ 1 |>.set! ⟨memoryName mangledName⟩ 0 0
        else {st with isFailed := true}

      def getSequence_aux (discr : ExternPlonkBuffer) (offset : ℕ) : ℕ → MLIR .InNondet
        | 0 => Noop
        | k + 1 => Sequence
                     (Assign s!"{mangle discr buf}#{k}" (Op.Get ⟨mangle discr buf⟩ offset k))
                     (getSequence_aux discr offset k)

      def getSequence (discr : ExternPlonkBuffer) (offset : ℕ) :=
        getSequence_aux buf discr offset outCount

      def getOffset (discr : ExternPlonkBuffer) : MLIR x :=
        Assign s!"mem{mangle discr buf}" (Op.Get ⟨s!"mem{mangle discr buf}"⟩ 0 0)

      @[simp]
      lemma getSequence_aux_succ :
        getSequence_aux buf discr offset k.succ =
        Sequence (Assign s!"{mangle discr buf}#{k}" (Op.Get ⟨mangle discr buf⟩ offset k)) (getSequence_aux buf discr offset k) := rfl

      abbrev plonkExternRead (discr : ExternPlonkBuffer) (offset : ℕ) : MLIR .InNondet :=
        getSequence buf outCount discr offset

      def memoryFor (mangledName : String) (st : State) :=
        (st.buffers[(⟨memoryName mangledName⟩ : BufferVar)].get![0]!)[0]!.get!.val

      def plonkRead (discr : ExternPlonkBuffer) (st : State) :=
        let offset := memoryFor (mangle discr buf) st
        if st.buffers[(⟨mangle discr buf⟩ : BufferVar)].get![offset]!.length = outCount ∧
           ⟨mangle discr buf⟩ ∈ st.buffers
        then ExternOp.plonkExternRead buf outCount discr offset
        else Fail

      def plonkReadBump (discr : ExternPlonkBuffer) (st : State) : State :=
        let buffer := mangle discr buf
        st.set! ⟨memoryName buffer⟩ 0 (memoryFor buffer st)

      -- Note: In theory, this can tag a non-special table if they happen to be called like this.
      -- We'll need a more robust system should we want to extend this further.
      def isSpecial (buf : BufferVar) :=
        buf.name.startsWith (toString ExternPlonkBuffer.PlonkRows) ||
        buf.name.startsWith (toString ExternPlonkBuffer.PlonkAccumRows)

      def sortPlonkBuffers (st : State) : State :=
        let specialNames := st.vars.filter isSpecial
        specialNames.foldr (init := st)
          λ name acc ↦
            {acc with buffers := acc.buffers[name] ←ₘ acc.buffers[name].get!.sort}

    end
  end MLIR.ExternOp  

  @[simp]
  lemma sizeOf_Variable {x : Variable α} : SizeOf.sizeOf x = 1 + SizeOf.sizeOf x.name := by cases x; simp

  @[simp]
  lemma sizeOf_IsNondet {x : IsNondet} : SizeOf.sizeOf x = 1 := by cases x <;> simp

  @[default_instance] noncomputable
  instance : SizeOf (MLIR x) where
    sizeOf command := let rec go {x} : MLIR x → ℕ
      | .Assign _ _ => 1
      | .Barrier => 1
      | .DropFelt _ => 1
      | .Eqz _ => 1
      | .If _ prog => 1 + go prog
      | .Nondet block => 1 + go block
      | .Noop => 0
      | .Sequence a b => 1 + go a + go b
      -- Ops
      | .Fail => 0
      | .Set _ _ _ => 1
      | .SetGlobal _ _ _ => 1
      -- Extern
      | .PlonkAccumRead _ n => 1 + n + n
      | .PlonkAccumWrite _ _ _ => 1
      | .PlonkRead _ n => 1 + n + n
      | .PlonkWrite _ _ _ => 1
    go command

  @[simp]
  lemma sizeOf_ExternOp_zero :
    sizeOf (MLIR.ExternOp.plonkExternRead buf 0 discr offset) = 0 := by
    simp [sizeOf, instSizeOfMLIR.go]

  @[simp]
  lemma sizeOf_ExternOp_succ :
    sizeOf (MLIR.ExternOp.plonkExternRead buf (Nat.succ k) discr offset) = 
    sizeOf (MLIR.ExternOp.plonkExternRead buf k discr offset) + 2 := by
    simp_arith [sizeOf, instSizeOfMLIR.go]
    rfl
      
  @[simp]
  lemma sizeOf_PlonkAccumRead_zero :
    sizeOf (MLIR.PlonkAccumRead buf 0) = 1 := by
    simp [sizeOf, instSizeOfMLIR.go]

  @[simp]
  lemma sizeOf_PlonkAccumRead_succ :
    sizeOf (MLIR.PlonkAccumRead buf (Nat.succ k)) = 
    sizeOf (MLIR.PlonkAccumRead buf k) + 2 := by
    simp_arith [sizeOf, instSizeOfMLIR.go]

  @[simp]
  lemma sizeOf_PlonkRead_zero :
    sizeOf (MLIR.PlonkRead buf 0) = 1 := by
    simp [sizeOf, instSizeOfMLIR.go]

  @[simp]
  lemma sizeOf_PlonkRead_succ :
    sizeOf (MLIR.PlonkRead buf (Nat.succ k)) = 
    sizeOf (MLIR.PlonkRead buf k) + 2 := by
    simp_arith [sizeOf, instSizeOfMLIR.go]

  lemma sizeOf_plonkExternRead_lt_sizeOf_plonkAccumRead :
    sizeOf (MLIR.ExternOp.plonkExternRead buf outCount discr offset) <
    sizeOf (MLIR.PlonkAccumRead buf outCount) := by
    induction outCount <;> simp [*]

  lemma sizeOf_plonkExternRead_lt_sizeOf_plonkRead :
    sizeOf (MLIR.ExternOp.plonkExternRead buf outCount discr offset) <
    sizeOf (MLIR.PlonkRead buf outCount) := by
    induction outCount <;> simp [*]

  lemma sizeOf_plonkRead_lt_sizeOf_plonkAccumRead :
    sizeOf (MLIR.ExternOp.plonkRead buf outCount discr st) <
    sizeOf (MLIR.PlonkAccumRead buf outCount) := by
    simp [MLIR.ExternOp.plonkRead]; split_ifs
    · exact sizeOf_plonkExternRead_lt_sizeOf_plonkAccumRead
    · simp [sizeOf, instSizeOfMLIR.go]

  lemma sizeOf_plonkRead_lt_sizeOf_plonkRead :
    sizeOf (MLIR.ExternOp.plonkRead buf outCount discr st) <
    sizeOf (MLIR.PlonkRead buf outCount) := by
    simp [MLIR.ExternOp.plonkRead]; split_ifs
    · exact sizeOf_plonkExternRead_lt_sizeOf_plonkRead
    · simp [sizeOf, instSizeOfMLIR.go]

  -- Step through the entirety of a `MLIR` MLIR program from initial state
  -- `state`, yielding the post-execution state and possibly a constraint
  -- (`Prop`), the return value of the program.
  def MLIR.run {α : IsNondet} (program : MLIR α) (st : State) : State :=
    match program with
      -- Meta
      | Assign name op => st.update name (op.eval st)
      | DropFelt k     => .dropFelts st k
      | Eqz x          => withEqZero st.felts[x]!.get! st
      | If x prog   =>
          -- have : sizeOf prog < sizeOf (If x prog) := by
          --   simp [sizeOf, instSizeOfMLIR.go]
          if st.felts[x]!.get! = 0 then st else prog.run st
      | Nondet block   =>
          -- have : sizeOf block < sizeOf (Nondet block) := by
          --   simp [sizeOf, instSizeOfMLIR.go]
          block.run st
      | Noop           => st
      | Sequence a b   =>
          have : sizeOf a < sizeOf (Sequence a b) := by
            cases a <;> simp [sizeOf, instSizeOfMLIR.go] <;> linarith
          have : sizeOf b < sizeOf (Sequence a b) := by
            cases b <;> simp [sizeOf, instSizeOfMLIR.go]
          b.run (a.run st)
      -- Ops
      | Barrier                  => ExternOp.sortPlonkBuffers st
      | Fail                     => {st with isFailed := true}
      | Set buf offset val       => st.set! buf offset st.felts[val]!.get!
      | SetGlobal buf offset val => st.setGlobal! buf offset st.felts[val]!.get! -- Behind the scenes setGlobal actually flattens a 2d buffer into a 1d buffer
                                                                                 -- and indexes into it. This is a side effect of global buffers only being 1d anyway
      -- Extern
      | PlonkAccumRead buf outCount =>
        -- have : sizeOf (ExternOp.plonkRead buf outCount ExternPlonkBuffer.PlonkAccumRows st) <
        --        sizeOf (PlonkAccumRead buf outCount) :=
        --   sizeOf_plonkRead_lt_sizeOf_plonkAccumRead
        ExternOp.plonkReadBump buf .PlonkAccumRows <|
          ExternOp.plonkRead buf outCount .PlonkAccumRows st |>.run st
      | PlonkAccumWrite buf args outCount => ExternOp.plonkExternWrite buf args outCount .PlonkAccumRows st
      | PlonkRead buf outCount =>
        -- have : sizeOf (ExternOp.plonkRead buf outCount ExternPlonkBuffer.PlonkRows st) <
        --        sizeOf (PlonkRead buf outCount) :=
        --   sizeOf_plonkRead_lt_sizeOf_plonkRead
        ExternOp.plonkReadBump buf .PlonkRows <|
          ExternOp.plonkRead buf outCount .PlonkRows st |>.run st
      | PlonkWrite buf args outCount => ExternOp.plonkExternWrite buf args outCount .PlonkRows st
  termination_by run _ program st => sizeOf program
  decreasing_by simp_wf
                all_goals try (simp [sizeOf, instSizeOfMLIR.go]; done)
                all_goals try (cases a <;> simp [sizeOf, instSizeOfMLIR.go] <;> try linarith)
                all_goals try apply sizeOf_plonkRead_lt_sizeOf_plonkAccumRead
                -- have : sizeOf (ExternOp.plonkRead buf outCount ExternPlonkBuffer.PlonkAccumRows st) <
                --   sizeOf (PlonkAccumRead buf outCount) :=
                --   sizeOf_plonkRead_lt_sizeOf_plonkAccumRead 
                -- exact this
                -- exact sizeOf_plonkRead_lt_sizeOf_plonkAccumRead
                -- all_goals try exact [sizeOf_plonkRead_lt_sizeOf_plonkAccumRead]
                -- all_goals try exact [sizeOf_plonkRead_lt_sizeOf_plonkRead]


  @[simp]
  abbrev MLIR.runProgram (program : MLIRProgram) := program.run

end Risc0
