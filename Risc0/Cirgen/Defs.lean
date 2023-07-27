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
      -- match op with
      --   | .Const _ => 1
      --   | .True => 1
      --   | .Add _ _ => 1
      --   | .Sub _ _ => 1
      --   | .Neg _ => 1
      --   | .Mul _ _ => 1
      --   | .Pow _ _ => 1
      --   | .BitAnd _ _ => 1
      --   | .Inv _ => 1
      --   | .Isz _ => 1        
      --   | .AndEqz _ _ => 1
      --   | .AndCond _ _ _ => 1
      --   | .Alloc _ => 1
      --   | .Back _ _ => 1
      --   | .Get _ _ _ => 1
      --   | .GetGlobal _ _ => 1
      --   | .Slice _ _ _ => 1

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

      def plonkExternWrite (discr : ExternPlonkBuffer) (st : State) : State := 
        if outCount = 0
        then (st.allocateBufferRow! buf args.length).setMany! ⟨mangle discr buf⟩ args
        else {st with isFailed := true}

      -- def plonkExternRead (discr : ExternPlonkBuffer) : MLIR x := Sequence Noop Noop

      def getSequence (discr : ExternPlonkBuffer) : MLIR x :=
        (List.range outCount).foldr (init := Noop)
          λ i acc ↦ Sequence (Assign s!"{mangle discr buf}#{i.toNat}" (Op.Get buf i 0)) acc

      def getSequence'_aux (discr : ExternPlonkBuffer) : ℕ → MLIR x
        | 0 => Noop
        | k + 1 => Sequence (Assign s!"{mangle discr buf}#{k}" (Op.Get buf k 0)) (getSequence'_aux discr k)

      def getSequence' {x : IsNondet} (discr : ExternPlonkBuffer) := @getSequence'_aux (x := x) buf discr outCount

      @[simp]
      lemma getSequence'_aux_succ {x} :
        @getSequence'_aux (x := x) buf discr k.succ =
        Sequence (Assign s!"{mangle discr buf}#{k.toNat}" (Op.Get buf k 0)) (getSequence'_aux buf discr k) := rfl

      def plonkExternRead {x : IsNondet} (discr : ExternPlonkBuffer) : MLIR x :=
        getSequence' buf outCount discr

    end
  end MLIR.ExternOp  

  @[simp]
  lemma sizeOf_Variable {x : Variable α} : SizeOf.sizeOf x = 1 + SizeOf.sizeOf x.name := by cases x; simp

  @[simp]
  lemma sizeOf_IsNondet {x : IsNondet} : SizeOf.sizeOf x = 1 := by cases x <;> simp

  -- #check MLIR.PlonkRead.sizeOf_spec

  -- lemma wagh {x} : sizeOf (@MLIR.ExternOp.getSequence' (x := x) buf outCount ExternPlonkBuffer.PlonkAccumRows) =
  --                  2 + outCount := by
  --   simp [MLIR.ExternOp.getSequence', MLIR.ExternOp.getSequence'_aux]
  --   induction outCount with
  --     | zero => simp [MLIR.ExternOp.getSequence'_aux]
  --     | succ k ih => simp
  --                    rw [ih]
  --                    simp (config := {arith := true})

  -- lemma aux :
  --   sizeOf (MLIR.ExternOp.getSequence'_aux buf ExternPlonkBuffer.PlonkAccumRows outCount) <
  --   3 + sizeOf buf.name + outCount := by
  --      induction outCount with
  --        | zero => simp [MLIR.ExternOp.getSequence'_aux]; linarith
  --        | succ k ih => simp
  --                       simp (config := {arith := true})
                        

-- #exit
  -- example {α : IsNondet} :
  --   sizeOf (@MLIR.ExternOp.plonkExternRead buf outCount α ExternPlonkBuffer.PlonkAccumRows st) <
  --   3 + sizeOf buf.name + outCount := by
  --   simp [MLIR.ExternOp.plonkExternRead]
  --   by_cases eq : { name := mangle ExternPlonkBuffer.PlonkRows buf : BufferVar } ∈ st.buffers <;> simp [eq]
  --   · by_cases eq' :
  --       List.length (Option.get! st.buffers[{ name := mangle ExternPlonkBuffer.PlonkAccumRows buf : BufferVar }])[(0 : ℕ)]! =
  --       outCount <;> simp [eq']
  --     · simp [MLIR.ExternOp.getSequence']
  --       unfold MLIR.ExternOp.getSequence'_aux
  --       rcases outCount with _ | k 
  --       · simp; linarith
  --       · simp (config := {arith := true})
          
        

        
  --     · linarith
  --   · linarith
                          
  -- example {α : IsNondet} :
  --   sizeOf (@MLIR.ExternOp.plonkExternRead buf outCount α ExternPlonkBuffer.PlonkAccumRows st) =
  --   2 + outCount := by
  --   simp [MLIR.ExternOp.plonkExternRead]
  --   by_cases eq : { name := mangle ExternPlonkBuffer.PlonkRows buf : BufferVar } ∈ st.buffers <;> simp [eq]
  --   · by_cases eq' :
  --       List.length (Option.get! st.buffers[{ name := mangle ExternPlonkBuffer.PlonkAccumRows buf : BufferVar }])[(0 : ℕ)]! =
  --       outCount <;> simp [eq']
  --     · simp [MLIR.ExternOp.getSequence']
  --       unfold MLIR.ExternOp.getSequence'_aux
  --       rcases outCount with _ | k 
  --       · simp
  --       · simp (config := {arith := true})
  --         sorry
          
        

        
  --     · cases outCount
  --       · rfl
  --       · simp at eq'
  --   · linarith

  -- @[simp]
  -- lemma sizeOf_append {a b : String} : sizeOf (a ++ b) = sizeOf a + sizeOf b := by
    
    


  -- @[simp]
  -- lemma sizeOf_mangle : sizeOf (mangle discr buf) = _ := by
  --   unfold mangle sizeOf String._sizeOf_inst
  --   simp


  -- example {α : IsNondet} {k : ℕ} :
  --   sizeOf (@MLIR.ExternOp.plonkExternRead buf outCount α ExternPlonkBuffer.PlonkAccumRows) =
  --   sizeOf s!"{mangle discr buf}#{k}" + sizeOf outCount := by
  --   simp [MLIR.ExternOp.plonkExternRead, MLIR.ExternOp.getSequence']
  --   unfold MLIR.ExternOp.getSequence'_aux
  --   rcases outCount with _ | ⟨k⟩
  --   · simp [toString]
  --     unfold sizeOf
  --   · simp (config := {arith := true})
      
  -- #exit

  -- lemma xa {α} {prog : MLIR α} :
  --   sizeOf (MLIR.If x prog) = 1 + sizeOf prog := by
  
  -- @[default_instance] noncomputable
  -- instance : SizeOf (MLIR .NotInNondet) where
  --   sizeOf command := let rec mario
  --     | .Assign _ _ => 1
  --     | .DropFelt _ => 1
  --     | .Eqz _ => 1
  --     | .If _ prog => 1 + sizeOf prog
  --     | .Nondet block => 1 + SizeOf.sizeOf block
  --     | .Noop => 0
  --     | .Sequence a b => 1 + mario a + mario b
  --     -- Ops
  --     | .Fail => 1
  --     -- Extern
  --     | .PlonkAccumRead _ n => 1 + SizeOf.sizeOf n
  --     | .PlonkAccumWrite _ _ _ => 1
  --     | .PlonkRead _ n => SizeOf.sizeOf n
  --     | .PlonkWrite _ _ _ => 1
  --   mario command
  
  -- @[default_instance] noncomputable
  -- instance : SizeOf (MLIR .InNondet) where
  --   sizeOf command := let rec mario
  --     | .Assign _ _ => 1
  --     | .DropFelt _ => 1
  --     | .Eqz _ => 1
  --     | .If _ prog => 1 + sizeOf prog
  --     | .Noop => 0
  --     | .Sequence a b => 1 + mario a + mario b
  --     -- Ops
  --     | .Fail => 1
  --     | .Set _ _ _ => 1
  --     | .SetGlobal _ _ _ => 1
  --     -- Extern
  --     | .PlonkAccumRead _ n => 1 + SizeOf.sizeOf n
  --     | .PlonkAccumWrite _ _ _ => 1
  --     | .PlonkRead _ n => SizeOf.sizeOf n
  --     | .PlonkWrite _ _ _ => 1
  --   mario command

  @[default_instance] noncomputable
  instance : SizeOf (MLIR x) where
    sizeOf command := let rec mario {x} : (y : MLIR x) → ℕ
      | .Assign _ _ => 1
      | .DropFelt _ => 1
      | .Eqz _ => 1
      | @MLIR.If x _ prog => 1 + @mario x prog
      | .Nondet block => 1 + mario block
      | .Noop => 0
      | @MLIR.Sequence x a b => 1 + @mario x a + @mario x b
      -- Ops
      | .Fail => 0
      | .Set _ _ _ => 1
      | .SetGlobal _ _ _ => 1
      -- Extern
      | .PlonkAccumRead _ n => 1 + n + SizeOf.sizeOf n
      | .PlonkAccumWrite _ _ _ => 1
      | .PlonkRead _ n => 1 + n + SizeOf.sizeOf n
      | .PlonkWrite _ _ _ => 1
    mario command

  @[simp]
  lemma xa {x : IsNondet}
    : sizeOf (@MLIR.ExternOp.plonkExternRead buf (Nat.succ k) x discr) = 
      sizeOf (@MLIR.ExternOp.plonkExternRead buf k x discr) + 2 := by
      generalize eq : sizeOf (MLIR.ExternOp.plonkExternRead buf k _) = rhs
      unfold MLIR.ExternOp.plonkExternRead MLIR.ExternOp.getSequence' MLIR.ExternOp.getSequence'_aux
      simp [sizeOf, instSizeOfMLIR.mario]
      generalize eq₁ : 1 + 1 + _ = lhs
      subst eq
      subst eq₁
      
      simp (config := {arith := true})
      -- unfold instSizeOfMLIR.mario
      
      
      rfl
      -- subst eq
      
  @[simp]
  lemma xb {x : IsNondet}
  : sizeOf (@MLIR.PlonkAccumRead x buf (Nat.succ k)) = 
    sizeOf (@MLIR.PlonkAccumRead x buf k) + 2 := by
    generalize eq : sizeOf (MLIR.PlonkAccumRead buf k) + _ = rhs
    simp [sizeOf, instSizeOfMLIR.mario]
    subst eq
    simp (config := {arith := true}) [sizeOf, instSizeOfMLIR.mario]
    



      
    
  --   sorry

  -- Step through the entirety of a `MLIR` MLIR program from initial state
  -- `state`, yielding the post-execution state and possibly a constraint
  -- (`Prop`), the return value of the program.
  def MLIR.run {β : IsNondet} (program : MLIR β) (st : State) : State :=
    match program with
      -- Meta
      | Assign name op => st.update name (op.eval st)
      | DropFelt k     => .dropFelts st k
      | Eqz x          => withEqZero st.felts[x]!.get! st
      | If x prog   =>
          have : sizeOf prog < sizeOf (If x prog) := by
            cases β <;> simp [sizeOf, instSizeOfMLIR.mario] <;>
            cases prog <;> simp [_sizeOf_1, sizeOf] <;> try linarith
          if st.felts[x]!.get! = 0 then st else prog.run st
      | Nondet block   =>
          have : sizeOf block < sizeOf (Nondet block) := by
            cases β <;> simp [sizeOf, instSizeOfMLIR.mario] <;>
            cases block <;> simp [_sizeOf_1, sizeOf] <;> try linarith
          block.run st
      | Noop           => st
      | Sequence a b   =>
          have : sizeOf a < sizeOf (Sequence a b) := by
            cases β
            · simp [sizeOf]
              cases a <;> simp [_sizeOf_1, sizeOf, instSizeOfMLIR.mario] <;> try linarith
            · simp [sizeOf]
              cases a <;> simp [_sizeOf_1, sizeOf, instSizeOfMLIR.mario] <;> try linarith
          have : sizeOf b < sizeOf (Sequence a b) := by
            cases β
            · simp [sizeOf]
              cases b <;> simp [_sizeOf_1, sizeOf, instSizeOfMLIR.mario] <;> try linarith
            · simp [sizeOf]
              cases b <;> simp [_sizeOf_1, sizeOf, instSizeOfMLIR.mario] <;> try linarith
          b.run (a.run st)
      -- Ops
      | Fail                     => {st with isFailed := true}
      | Set buf offset val       => st.set! buf offset st.felts[val]!.get!
      | SetGlobal buf offset val => st.setGlobal! buf offset st.felts[val]!.get! -- Behind the scenes setGlobal actually flattens a 2d buffer into a 1d buffer
                                                                                -- and indexes into it. This is a side effect of global buffers only being 1d anyway
      | PlonkAccumRead buf outCount =>
          if st.buffers[(⟨mangle .PlonkAccumRows buf⟩ : BufferVar)].get![0]!.length = outCount ∧ ⟨mangle .PlonkAccumRows buf⟩ ∈ st.buffers
          then 
            have : sizeOf (@ExternOp.plonkExternRead buf outCount IsNondet.InNondet ExternPlonkBuffer.PlonkAccumRows) < sizeOf (@PlonkAccumRead IsNondet.InNondet buf outCount) := by
                     induction outCount with
                       | zero => simp [ExternOp.plonkExternRead, ExternOp.getSequence', ExternOp.getSequence'_aux, sizeOf, instSizeOfMLIR.mario]
                       | succ k ih => rw [xa, xb]; linarith
              (ExternOp.plonkExternRead buf outCount .PlonkAccumRows).run (β := IsNondet.InNondet) st
          else
            -- have : sizeOf (@Fail β) < sizeOf (@PlonkAccumRead β buf outCount) := by
            --   simp [sizeOf, instSizeOfMLIR.mario]
            -- have : sizeOf (@Fail β) < sizeOf (@PlonkRead β buf outCount) := by
            --   simp [sizeOf, instSizeOfMLIR.mario]
            Fail.run (β := IsNondet.InNondet) st
      | PlonkAccumWrite buf args outCount => ExternOp.plonkExternWrite buf args outCount .PlonkAccumRows st
      | PlonkRead buf outCount =>
          if st.buffers[(⟨mangle .PlonkRows buf⟩ : BufferVar)].get![0]!.length = outCount ∧ ⟨mangle .PlonkRows buf⟩ ∈ st.buffers
          then have : sizeOf (@ExternOp.plonkExternRead buf outCount IsNondet.InNondet ExternPlonkBuffer.PlonkRows) < sizeOf (@PlonkAccumRead IsNondet.InNondet buf outCount) := by
                     induction outCount with
                       | zero => simp [ExternOp.plonkExternRead, ExternOp.getSequence', ExternOp.getSequence'_aux, sizeOf, instSizeOfMLIR.mario]
                       | succ k ih => rw [xa, xb]; linarith
          
          (ExternOp.plonkExternRead buf outCount .PlonkRows).run (β := IsNondet.InNondet) st
          else Fail.run (β := IsNondet.InNondet) st
      | PlonkWrite buf args outCount => ExternOp.plonkExternWrite buf args outCount .PlonkRows st
  termination_by run _ program st => sizeOf program

  @[simp]
  abbrev MLIR.runProgram (program : MLIRProgram) := program.run

end Risc0
