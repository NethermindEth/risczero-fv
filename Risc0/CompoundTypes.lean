import Risc0.Basic

namespace Risc0

-- Each field has a storage kind in the C++
-- Seems to just be a label, but I'm keeping it here so we don't forget
-- inductive StorageKind :=
--   | Normal
--   | Reserve
--   | Use

mutual

inductive ContainerType where
  | StructType : List (String × MemberType) → ContainerType
  | UnionType  : List (String × MemberType) → ContainerType

inductive MemberType where
  | StructType : ContainerType → MemberType
  | UnionType  : ContainerType → MemberType
  | ArrayType  : MemberType → ℕ → MemberType
  | Ref        : MemberType

end

mutual

def ContainerType.size : ContainerType → ℕ
  | .StructType fields =>
      match fields with
        | List.nil => 0
        | List.cons  (_, fieldType) fs => fieldType.size + (ContainerType.StructType fs).size
  | .UnionType fields =>
      match fields with
        | List.nil => 0
        | List.cons (_, fieldType) fs => max fieldType.size (ContainerType.UnionType fs).size

def MemberType.size (memberType: MemberType) : ℕ :=
  match memberType with
    | .StructType c | .UnionType c => c.size
    | .ArrayType c n               => c.size * n
    | .Ref                         => 1

end

def ContainerType.offsetSize (c : ContainerType) (name : String) : Option (ℕ × ℕ) :=
  match c with
    | StructType fields =>
        match fields with
          | List.nil => .none
          | List.cons (fieldName, fieldType) fs =>
              if name = fieldName
              then .some (0, fieldType.size)
              else
                let x := (StructType fs).offsetSize name
                if x.isNone
                then .none
                else .some (fieldType.size + x.get!.fst, x.get!.snd)
    | UnionType fields =>
        match fields with
          | List.nil => .none
          | List.cons (fieldName, fieldType) fs =>
              if name = fieldName
              then .some (0, fieldType.size)
              else (UnionType fs).offsetSize name

namespace CompoundOp

-- def Lookup

-- def Subscript

def Load {isNondet: IsNondet} (ref: BufferVar): Op isNondet := Op.Get ref 0 0

def Store (ref: BufferVar) (val: FeltVar) := MLIR.Set ref 0 val

def Lookup {isNondet: IsNondet} (container: BufferVar) (containerType: ContainerType) (fieldName: String): Op isNondet :=
  let (offset, size) := (containerType.offsetSize fieldName).get!
  Op.Slice container offset size

def Subscript {isNondet : IsNondet} (container: BufferVar) (containerType: MemberType) (idx: ℕ) : Option (Op isNondet) :=
  match containerType with
    | MemberType.ArrayType elemType _ =>
      .some (Op.Slice container (idx * elemType.size) elemType.size)
    | _ => .none

end CompoundOp

end Risc0
