import Risc0.Basic

namespace Risc0

-- Each field has a storage kind in the C++
-- Seems to just be a label, but I'm keeping it here so we don't forget
-- inductive StorageKind :=
--   | Normal
--   | Reserve
--   | Use

inductive MemberType where
  | StructType: List (String × MemberType) → MemberType
  | UnionType: List (String × MemberType) → MemberType
  | ArrayType: MemberType → ℕ → MemberType
  | Ref      : MemberType

def MemberType.GetSize (memberType: MemberType) : ℕ :=
  match memberType with
    | StructType fields =>
      match fields with
        | List.nil => 0
        | List.cons (_, fieldType) fs => (GetSize fieldType) + (GetSize (StructType fs))
    | UnionType fields       =>
      match fields with
        | List.nil                       => 0
        | List.cons (_, fieldType) fs => max (GetSize fieldType) (GetSize (UnionType fs))
    | ArrayType elemType len => (GetSize elemType) * len
    | Ref                    => 1

def MemberType.GetFieldOffsetSize (memberType: MemberType) (name: String) : Option (ℕ × ℕ) :=
  match memberType with
    | StructType fields      =>
      match fields with
        | List.nil => .none
        | List.cons (fieldName, fieldType) fs =>
          if name = fieldName
          then .some (0, GetSize fieldType)
          else
            let x := GetFieldOffsetSize (StructType fs) name
            if x.isNone
            then .none
            else .some ((GetSize fieldType) + x.get!.fst,x.get!.snd)
    | UnionType fields       =>
      match fields with
        | List.nil => .none
        | List.cons (fieldName, fieldType) fs =>
          if name = fieldName
          then .some (0, GetSize fieldType)
          else GetFieldOffsetSize (UnionType fs) name
    | ArrayType _ _ => .none
    | Ref           => .none

namespace CompoundOp

-- def Lookup

-- def Subscript

def Load {isNondet: IsNondet} (ref: BufferVar): Op isNondet := Op.Get ref 0 0

def Store (ref: BufferVar) (val: FeltVar) := MLIR.Set ref 0 val

def Lookup {isNondet: IsNondet} (container: BufferVar) (containerType: MemberType) (fieldName: String): Op isNondet :=
  let (offset, size) := (containerType.GetFieldOffsetSize fieldName).get!
  Op.Slice container offset size

def Subscript {isNondet : IsNondet} (container: BufferVar) (containerType: MemberType) (idx: ℕ): Option (Op isNondet) :=
  match containerType with
    | MemberType.ArrayType elemType _ =>
      .some (Op.Slice container (idx * elemType.GetSize) elemType.GetSize)
    | _ => .none

end CompoundOp

end Risc0