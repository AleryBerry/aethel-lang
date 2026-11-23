import Aethel.Syntax

namespace Aethel.Core

structure Allocation where
  owner : OwnerId
  bytes : List UInt8
  deriving Repr, DecidableEq

structure Handle where
  location : ByteLocation
  mode : AccessMode
  deriving Repr, DecidableEq

structure View where
  id : ViewId
  location : ByteLocation
  mode : AccessMode
  deriving Repr, DecidableEq

structure State where
  allocations : List Allocation := []
  handles : List (HandleId × Handle) := []
  views : List View := []
  /-- Allocation identities are never reused, even after destruction. -/
  issued : List OwnerId := []
  /-- Observations are accumulated in reverse order. -/
  observations : List UInt8 := []
  deriving Repr, DecidableEq

def State.allocation (s : State) (owner : OwnerId) : Option Allocation :=
  s.allocations.find? fun a => a.owner == owner

def State.handle (s : State) (id : HandleId) : Option Handle :=
  (s.handles.find? fun entry => entry.1 == id).map Prod.snd

def State.view (s : State) (id : ViewId) : Option View :=
  s.views.find? fun view => view.id == id

def State.byte (s : State) (p : ByteLocation) : Option UInt8 := do
  let allocation ← s.allocation p.allocation
  allocation.bytes[p.offset]?

def State.store (s : State) (p : ByteLocation) (value : UInt8) : State :=
  { s with allocations := s.allocations.map fun allocation =>
      { allocation with bytes := if allocation.owner == p.allocation
          then allocation.bytes.set p.offset value else allocation.bytes } }

def State.addAllocation (s : State) (owner : OwnerId) (bytes : List UInt8) : State :=
  { s with allocations := ⟨owner, bytes⟩ :: s.allocations, issued := owner :: s.issued }

def State.addHandle (s : State) (id : HandleId) (h : Handle) : State :=
  { s with handles := (id, h) :: s.handles }

def State.addView (s : State) (v : View) : State :=
  { s with views := v :: s.views }

def State.removeView (s : State) (id : ViewId) : State :=
  { s with views := s.views.filter fun v => v.id != id }

def State.removeHandle (s : State) (id : HandleId) : State :=
  { s with handles := s.handles.filter fun h => h.1 != id }

/-- Destruction invalidates all descendant handles. Active views are checked
separately before this operation; issued allocation identities remain retired. -/
def State.removeOwner (s : State) (owner : OwnerId) : State :=
  { s with
    allocations := s.allocations.filter fun a => a.owner != owner
    handles := s.handles.filter fun h => h.2.location.allocation != owner }

def State.observe (s : State) (value : UInt8) : State :=
  { s with observations := value :: s.observations }

def AccessMode.Allows (authority request : AccessMode) : Prop :=
  request = .shared ∨ authority = .exclusive

def AccessMode.Compatible (a b : AccessMode) : Prop := a = .shared ∧ b = .shared

instance (a b : AccessMode) : Decidable (a.Allows b) :=
  inferInstanceAs (Decidable (b = .shared ∨ a = .exclusive))

/-- Eligibility is expressed independently as a proposition. In this byte kernel
each view covers one byte; wider paths and packed proxies require later rules. -/
def State.Available (s : State) (p : ByteLocation) (mode : AccessMode)
    (through : Option ViewId) : Prop :=
  ∀ v ∈ s.views,
    through = some v.id ∨ p ≠ v.location ∨ mode.Compatible v.mode

instance (s : State) (p : ByteLocation) (mode : AccessMode) (through : Option ViewId) :
    Decidable (s.Available p mode through) :=
  inferInstanceAs (Decidable (∀ v ∈ s.views,
    through = some v.id ∨ p ≠ v.location ∨ (mode = .shared ∧ v.mode = .shared)))

def State.Unreserved (s : State) (owner : OwnerId) : Prop :=
  ∀ v ∈ s.views, v.location.allocation ≠ owner

instance (s : State) (owner : OwnerId) : Decidable (s.Unreserved owner) :=
  inferInstanceAs (Decidable (∀ v ∈ s.views, v.location.allocation ≠ owner))

/-- Independent relational semantics. Missing allocations/handles, invalid
authority, reservation conflicts, and reuse of allocation IDs have no step. -/
inductive Step : State → Instruction → State → Prop where
  | alloc (fresh : owner ∉ s.issued) :
      Step s (.alloc owner bytes) (s.addAllocation owner bytes)
  | alias {id : HandleId} (fresh : s.handle id = none) (live : s.byte ⟨owner, offset⟩ = some byte) :
      Step s (.alias id owner offset mode) (s.addHandle id ⟨⟨owner, offset⟩, mode⟩)
  | read {id : HandleId} (found : s.handle id = some h) (live : s.byte h.location = some value)
      (available : s.Available h.location .shared none) :
      Step s (.read id) (s.observe value)
  | write {id : HandleId} (found : s.handle id = some h) (live : s.byte h.location = some old)
      (authority : h.mode.Allows .exclusive)
      (available : s.Available h.location .exclusive none) :
      Step s (.write id value) (s.store h.location value)
  | reserve {id : ViewId} (fresh : s.view id = none) (found : s.handle handle = some h)
      (live : s.byte h.location = some byte) (authority : h.mode.Allows mode)
      (available : s.Available h.location mode none) :
      Step s (.reserve id handle mode) (s.addView ⟨id, h.location, mode⟩)
  | readView {id : ViewId} (found : s.view id = some v) (live : s.byte v.location = some value)
      (available : s.Available v.location .shared (some id)) :
      Step s (.readView id) (s.observe value)
  | writeView {id : ViewId} (found : s.view id = some v) (live : s.byte v.location = some old)
      (authority : v.mode.Allows .exclusive)
      (available : s.Available v.location .exclusive (some id)) :
      Step s (.writeView id value) (s.store v.location value)
  | release {id : ViewId} (found : s.view id = some v) : Step s (.release id) (s.removeView id)
  | forget {id : HandleId} (found : s.handle id = some h) : Step s (.forget id) (s.removeHandle id)
  | destroy (found : s.allocation owner = some a) (unreserved : s.Unreserved owner) :
      Step s (.destroy owner) (s.removeOwner owner)

/-- A complete finite trace in the relational semantics. This is not the full
language's typing judgment: it specifies the resource kernel's legal execution. -/
inductive Runs : State → Program → State → Prop where
  | nil : Runs s [] s
  | cons : Step s instruction middle → Runs middle rest final →
      Runs s (instruction :: rest) final

end Aethel.Core
