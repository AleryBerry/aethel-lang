import Aethel.CoreOwnership

namespace Aethel.Core

/-- The checker retains allocation lengths and access metadata. It never
interprets stored values or collects read observations. -/
structure ResourceState where
  allocations : List (OwnerId × Nat) := []
  handles : List (HandleId × Handle) := []
  views : List View := []
  issued : List OwnerId := []
  deriving Repr, DecidableEq

def State.resources (s : State) : ResourceState :=
  ⟨s.allocations.map (fun a => (a.owner, a.bytes.length)), s.handles, s.views, s.issued⟩

/-- Reuse handle and view queries with only access metadata available. -/
def ResourceState.authorityState (r : ResourceState) : State :=
  { handles := r.handles, views := r.views, issued := r.issued }

def ResourceState.extent (r : ResourceState) (owner : OwnerId) : Option Nat :=
  (r.allocations.find? fun a => a.1 == owner).map Prod.snd

def ResourceState.live (r : ResourceState) (p : ByteLocation) : Bool :=
  (r.extent p.allocation).any fun n => p.offset < n

def checkInstruction (r : ResourceState) : Instruction → Option ResourceState
  | .alloc owner bytes =>
    if owner ∉ r.issued then
      some { r with allocations := (owner, bytes.length) :: r.allocations
                    issued := owner :: r.issued }
    else none
  | .alias id owner offset mode =>
    if (r.authorityState.handle id).isNone && r.live ⟨owner, offset⟩ then
      some { r with handles := (id, ⟨⟨owner, offset⟩, mode⟩) :: r.handles }
    else none
  | .read id => do
    let h ← r.authorityState.handle id
    if r.live h.location ∧ r.authorityState.Available h.location .shared none
      then some r else none
  | .write id _ => do
    let h ← r.authorityState.handle id
    if r.live h.location ∧ h.mode.Allows .exclusive ∧
        r.authorityState.Available h.location .exclusive none
      then some r else none
  | .reserve id handle mode => do
    if (r.authorityState.view id).isSome then none else do
      let h ← r.authorityState.handle handle
      if r.live h.location ∧ h.mode.Allows mode ∧
          r.authorityState.Available h.location mode none
        then some { r with views := ⟨id, h.location, mode⟩ :: r.views }
        else none
  | .readView id => do
    let v ← r.authorityState.view id
    if r.live v.location ∧ r.authorityState.Available v.location .shared (some id)
      then some r else none
  | .writeView id _ => do
    let v ← r.authorityState.view id
    if r.live v.location ∧ v.mode.Allows .exclusive ∧
        r.authorityState.Available v.location .exclusive (some id)
      then some r else none
  | .release id => do
    let _ ← r.authorityState.view id
    some { r with views := r.views.filter fun v => v.id != id }
  | .forget id => do
    let _ ← r.authorityState.handle id
    some { r with handles := r.handles.filter fun entry => entry.1 != id }
  | .destroy owner =>
    if (r.extent owner).isSome ∧ r.authorityState.Unreserved owner then
      some { r with
        allocations := r.allocations.filter fun a => a.1 != owner
        handles := r.handles.filter fun h => h.2.location.allocation != owner }
    else none

def checkResources (r : ResourceState) : Program → Option ResourceState
  | [] => some r
  | instruction :: rest =>
    (checkInstruction r instruction).bind fun middle => checkResources middle rest

def verifyResources (program : Program) : Bool :=
  (checkResources {} program).any fun final => final.views.isEmpty

theorem State.resources_extent (s : State) (owner : OwnerId) :
    s.resources.extent owner = (s.allocation owner).map (fun a => a.bytes.length) := by
  simp [ResourceState.extent, State.resources, State.allocation, List.find?_map, Function.comp_def]

theorem State.resources_live (s : State) (p : ByteLocation) :
    s.resources.live p = (s.byte p).isSome := by
  cases h : s.allocation p.allocation <;>
    simp [ResourceState.live, State.resources_extent, State.byte, h, getElem?_def] <;> split <;> simp_all

@[simp] theorem State.resources_store (s : State) (p : ByteLocation) (value : UInt8) :
    (s.store p value).resources = s.resources := by
  simp [State.store, State.resources, List.map_map, Function.comp_def, apply_ite]

@[simp] private theorem authority_handle (s : State) (id : HandleId) :
    s.resources.authorityState.handle id = s.handle id := rfl

@[simp] private theorem authority_view (s : State) (id : ViewId) :
    s.resources.authorityState.view id = s.view id := rfl

@[simp] private theorem authority_available (s : State) (p : ByteLocation)
    (mode : AccessMode) (through : Option ViewId) :
    s.resources.authorityState.Available p mode through = s.Available p mode through := rfl

@[simp] private theorem authority_unreserved (s : State) (owner : OwnerId) :
    s.resources.authorityState.Unreserved owner = s.Unreserved owner := rfl

@[simp] private theorem resources_observe (s : State) (value : UInt8) :
    (s.observe value).resources = s.resources := rfl

theorem checkInstruction_correct (s : State) (instruction : Instruction) :
    checkInstruction s.resources instruction = (execute s instruction).map State.resources := by
  cases instruction <;>
    simp only [checkInstruction, execute, State.resources_live, State.resources_extent,
      authority_handle, authority_view, authority_available, authority_unreserved,
      Option.map_bind, Function.comp_def, Option.isSome_map, bind]
  case alloc owner bytes =>
    by_cases fresh : owner ∈ s.issued <;> simp [fresh, State.resources, State.addAllocation]
  case alias id owner offset mode =>
    cases (s.handle id) <;> cases (s.byte ⟨owner, offset⟩) <;> simp [State.addHandle, State.resources]
  case reserve id handle mode =>
    cases (s.view id) <;> simp only [Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ite_false, ite_true, Option.map_none, Option.map_bind, Function.comp_def]
    congr 1 <;> funext access
    cases (s.byte access.location) <;> simp [apply_ite, State.resources, State.addView, Option.bind]
  case destroy owner =>
    cases (s.allocation owner) <;> simp [State.resources, State.removeOwner, List.filter_map, Function.comp_def, apply_ite, Option.bind]
  all_goals first | rfl | (congr 1 <;> funext access)
  all_goals cases (s.byte access.location) <;> simp [apply_ite, Option.bind]

theorem checkResources_correct (s : State) (program : Program) :
    checkResources s.resources program = (run s program).map State.resources := by
  induction program generalizing s with
  | nil => rfl
  | cons instruction rest ih =>
    simp [checkResources, run, checkInstruction_correct, Option.bind_map, Option.map_bind,
      Function.comp_def, ih]

theorem verifyResources_correct (program : Program) :
    verifyResources program = true ↔ ∃ final, Runs {} program final ∧ final.views = [] := by
  change (checkResources ({} : State).resources program).any _ = true ↔ _
  rw [checkResources_correct]
  simp only [Option.any_eq_true, Option.map_eq_some_iff, List.isEmpty_iff, run_correct]
  exact ⟨fun ⟨_, ⟨final, traced, rfl⟩, closed⟩ => ⟨final, traced, closed⟩,
    fun ⟨final, traced, closed⟩ => ⟨final.resources, ⟨final, traced, rfl⟩, closed⟩⟩

end Aethel.Core
