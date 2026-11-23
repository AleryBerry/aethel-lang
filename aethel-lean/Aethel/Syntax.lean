import Aethel.Permissions

namespace Aethel.Core

abbrev OwnerId := Nat
abbrev HandleId := Nat
abbrev ViewId := Nat

inductive AccessMode where
  | shared
  | exclusive
  deriving Repr, DecidableEq

/-- Raw instructions for the first sequential resource kernel. IDs and offsets
are unchecked syntax, so invalid ownership and access programs are representable.
The full ADT/function language will extend this kernel, not be inferred from it. -/
inductive Instruction where
  | alloc (owner : OwnerId) (bytes : List UInt8)
  | alias (handle : HandleId) (owner : OwnerId) (offset : Nat) (mode : AccessMode)
  | read (handle : HandleId)
  | write (handle : HandleId) (value : UInt8)
  | reserve (view : ViewId) (handle : HandleId) (mode : AccessMode)
  | readView (view : ViewId)
  | writeView (view : ViewId) (value : UInt8)
  | release (view : ViewId)
  | forget (handle : HandleId)
  | destroy (owner : OwnerId)
  deriving Repr, DecidableEq

abbrev Program := List Instruction

end Aethel.Core
