namespace Risc0

-- Each field has a storage kind in the C++
-- Seems to just be a label, but I'm keeping it here so we don't forget
inductive StorageKind :=
  | Normal
  | Reserve
  | Use

inductive ContainerTag :=
  | Struct
  | Union

structure ContainerType (containerTag: ContainerTag) :=
  name: String
  fields: List FieldInfo

structure FieldInfo :=
  name: String
  type: sorry

structure ArrayType :=
  type: sorry
  length: Nat

inductive CompoundType :=
  | ContainerType
  | ArrayType

def ToBuffer (x: CompoundType) :=
  match x with
    | ContainerType tag => match tag with
      | ContainerTag.Struct => sorry
      | ContainerTag.Union => sorry
    | ArrayType => sorry

-- The conversion from compound types to buffers is the issue
-- Our code currently evaluates operations on buffers by taking
-- the name of the buffer and finding it in state.buffers
-- however if an op returns a buffer, not a BufferVar, how can another one take it?

end Risc0