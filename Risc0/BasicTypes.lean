import Mathlib.Data.Nat.Prime
import Mathlib.Data.Finmap
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.Vector
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Bitvec.Defs

import Risc0.Map
import Risc0.Wheels

import Lean

namespace Risc0

  @[inline]
  def P: ℕ := 15 * 2^27 + 1

  axiom P_prime: Nat.Prime P 
  instance : Fact (Nat.Prime P) := ⟨P_prime⟩

  inductive VarType := | FeltTag | PropTag | BufferTag deriving DecidableEq

  structure Variable (tag : VarType) :=
    name : String
  deriving DecidableEq

  abbrev BufferVar := Variable VarType.BufferTag
  abbrev FeltVar := Variable VarType.FeltTag
  abbrev PropVar := Variable VarType.PropTag

  abbrev Felt := ZMod P
  instance : Inhabited Felt := ⟨-42⟩
  def feltBitAnd (x y: Felt) : Felt :=
    ↑(Bitvec.and (Bitvec.ofNat 256 x.val) (Bitvec.ofNat 256 y.val)).toNat

  open Lean Meta PrettyPrinter Delaborator SubExpr in
  @[delab app.OfNat.ofNat] def delabOfNat : Delab := do
    let a ← withAppFn $ withAppArg delab
    let b ← withType delab
    `(($a : $b))

  -- TODO: Inspect the term properly to un-resolve namespaces; Lean is being difficult
  set_option hygiene false in
  open Lean Meta Elab Term PrettyPrinter Delaborator SubExpr in
  @[delab app.Risc0.Variable.mk] def delabOfVariable : Delab := do
    let ident ← withAppArg delab
    let T ← withType delab
    let translate (t : Term) : String := 
      if s!"{t}" = "(Term.app `Variable [`VarType.BufferTag])" then "BufferVar"
      else if s!"{t}" = "(Term.app `Variable [`VarType.FeltTag])" then "FeltVar"
      else "PropVar"
    let finalT := mkIdent <| translate T
    `({ name := $ident : $finalT})

end Risc0
