import Aethel.Machine

namespace Aethel.Core

/-- Executable interpretation of a raw instruction. Failure is rejection, not
a successful checked failure in the eventual source-language semantics. -/
def execute (s : State) : Instruction → Option State
  | .alloc owner bytes =>
    if owner ∉ s.issued then some (s.addAllocation owner bytes) else none
  | .alias id owner offset mode => do
    if (s.handle id).isSome then none else do
      let _ ← s.byte ⟨owner, offset⟩
      some (s.addHandle id ⟨⟨owner, offset⟩, mode⟩)
  | .read id => do
    let h ← s.handle id
    let value ← s.byte h.location
    if s.Available h.location .shared none then some (s.observe value) else none
  | .write id value => do
    let h ← s.handle id
    let _ ← s.byte h.location
    if h.mode.Allows .exclusive ∧ s.Available h.location .exclusive none
      then some (s.store h.location value) else none
  | .reserve id handle mode => do
    if (s.view id).isSome then none else do
      let h ← s.handle handle
      let _ ← s.byte h.location
      if h.mode.Allows mode ∧ s.Available h.location mode none
        then some (s.addView ⟨id, h.location, mode⟩) else none
  | .readView id => do
    let v ← s.view id
    let value ← s.byte v.location
    if s.Available v.location .shared (some id) then some (s.observe value) else none
  | .writeView id value => do
    let v ← s.view id
    let _ ← s.byte v.location
    if v.mode.Allows .exclusive ∧ s.Available v.location .exclusive (some id)
      then some (s.store v.location value) else none
  | .release id => do
    let _ ← s.view id
    some (s.removeView id)
  | .forget id => do
    let _ ← s.handle id
    some (s.removeHandle id)
  | .destroy owner => do
    let _ ← s.allocation owner
    if s.Unreserved owner then some (s.removeOwner owner) else none

def run (s : State) : Program → Option State
  | [] => some s
  | instruction :: rest => (execute s instruction).bind fun middle => run middle rest

/-- A top-level resource program must release all view reservations. Owning
allocations can remain as its result; function-return origins are not modeled. -/
def checkClosed (program : Program) : Option State := do
  let final ← run {} program
  if final.views.isEmpty then some final else none

end Aethel.Core
