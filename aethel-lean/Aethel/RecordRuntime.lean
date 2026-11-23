import Aethel.RecordInitialization
import Aethel.Structured

namespace Aethel.AutomaticLayout

open Core Structured

/-- The runtime pairs a checked representation with the allocation identity
issued when its initialized bytes were installed. -/
structure RecordRef (abi : TargetIntegerABI) (schema : Schema) where
  private mk ::
  owner : OwnerId
  layout : Layout
  conforms : Conforms abi schema layout

def allocateRecord (abi : TargetIntegerABI) (schema : Schema) (state : State) (owner : OwnerId)
    (values : List Nat → Option IntegerBits) : Option (RecordRef abi schema × State) := do
  let layout ← planVerified abi schema
  let image ← initializeRecord layout.property values
  let next ← execute state (.alloc owner image.toBytes)
  return (⟨owner, layout.val, layout.property⟩, next)

theorem allocateRecord_initialized {abi : TargetIntegerABI} {schema : Schema} {state next : State}
    {owner : OwnerId} {values : List Nat → Option IntegerBits} {record : RecordRef abi schema}
    (allocated : allocateRecord abi schema state owner values = some (record, next)) :
    record.owner = owner ∧ ∃ image, initializeRecord record.conforms values = some image ∧
      Step state (.alloc owner image.toBytes) next ∧
      next.allocation record.owner = some ⟨owner, image.toBytes⟩ := by
  simp only [allocateRecord, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at allocated
  obtain ⟨layout, planned, image, initialized, stateAfter, executed, rfl, rfl⟩ := allocated
  have step := execute_sound executed
  refine ⟨rfl, image, initialized, step, ?_⟩
  cases step
  simp [State.addAllocation, State.allocation]

def IntegerField.byteOffsets (field : IntegerField size) : List Nat :=
  (List.range ((field.offset % 8 + field.kind.bits + 7) / 8)).map
    (fun i => field.offset / 8 + i)

theorem IntegerField.byteOffsets_cover (field : IntegerField size) (bit : Nat)
    (inside : field.offset ≤ bit ∧ bit < field.offset + field.kind.bits) :
    bit / 8 ∈ field.byteOffsets := by
  apply List.mem_map.mpr
  refine ⟨bit / 8 - field.offset / 8, List.mem_range.mpr ?_, ?_⟩
  · omega
  · omega

private def probe (mode : AccessMode) (target : AccessTarget) : Instruction :=
  match mode with
  | .shared => target.readInstruction
  | .exclusive => target.writeInstruction 0

/-- Each byte a field can touch requires its own existing handle or view.
Packed updates consequently need authority over the shared byte. -/
def AccessAllowed (state : State) (owner : OwnerId) (mode : AccessMode)
    (offsets : List Nat) (targets : List AccessTarget) : Prop :=
  offsets.length = targets.length ∧
    ∀ pair ∈ offsets.zip targets, pair.2.location state = some ⟨owner, pair.1⟩ ∧
      ∃ next, Step state (probe mode pair.2) next

def checkAccessTargets (state : State) (owner : OwnerId) (mode : AccessMode)
    (offsets : List Nat) (targets : List AccessTarget) : Bool :=
  offsets.length == targets.length &&
    (offsets.zip targets).all fun (offset, target) =>
      target.location state == some ⟨owner, offset⟩ &&
      (checkInstruction state.resources (probe mode target)).isSome

theorem checkAccessTargets_correct (state : State) (owner : OwnerId) (mode : AccessMode)
    (offsets : List Nat) (targets : List AccessTarget) :
    checkAccessTargets state owner mode offsets targets = true ↔
      AccessAllowed state owner mode offsets targets := by
  simp only [checkAccessTargets, AccessAllowed, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true, checkInstruction_correct, Option.isSome_map, Option.isSome_iff_exists, execute_correct]

theorem AccessAllowed.permits_bit {state : State} {owner : OwnerId} {mode : AccessMode}
    {field : IntegerField size} {targets : List AccessTarget} {bit : Nat}
    (allowed : AccessAllowed state owner mode field.byteOffsets targets)
    (inside : field.offset ≤ bit ∧ bit < field.offset + field.kind.bits) :
    ∃ target next, target ∈ targets ∧ target.location state = some ⟨owner, bit / 8⟩ ∧
      Step state (probe mode target) next := by
  obtain ⟨i, index, eq⟩ := List.mem_iff_getElem.mp (field.byteOffsets_cover bit inside)
  have targetIndex : i < targets.length := allowed.1 ▸ index
  have zipped : i < (field.byteOffsets.zip targets).length := by
    simp only [List.length_zip, Nat.lt_min]
    exact ⟨index, targetIndex⟩
  have member : (bit / 8, targets[i]) ∈ field.byteOffsets.zip targets :=
    List.mem_of_getElem (h := zipped) (by rw [List.getElem_zip, eq])
  obtain ⟨matchesLocation, next, permitted⟩ := allowed.2 _ member
  exact ⟨targets[i], next, List.getElem_mem _, matchesLocation, permitted⟩

private def RecordRef.openImage (record : RecordRef abi schema) (state : State) :
    Option (Image record.layout.size) := do
  let allocation ← state.allocation record.owner
  if same : allocation.bytes.length = record.layout.size then
    return same ▸ Image.ofBytes allocation.bytes
  else none

def RecordRef.read (record : RecordRef abi schema) (state : State) (path : List Nat)
    (targets : List AccessTarget) : Option IntegerBits := do
  let field ← resolveInteger record.conforms path
  if checkAccessTargets state record.owner .shared field.byteOffsets targets then
    let image ← record.openImage state
    return ⟨field.kind, field.get image⟩
  else none

private def replaceBytes (state : State) (owner : OwnerId) (bytes : List UInt8) : State :=
  { state with allocations := state.allocations.map fun allocation =>
      if allocation.owner == owner then { allocation with bytes := bytes } else allocation }

def RecordRef.write (record : RecordRef abi schema) (state : State) (path : List Nat)
    (targets : List AccessTarget) (value : IntegerBits) : Option State := do
  let field ← resolveInteger record.conforms path
  if checkAccessTargets state record.owner .exclusive field.byteOffsets targets then
    let image ← record.openImage state
    let updated ← writeInteger record.conforms path image value
    return replaceBytes state record.owner updated.toBytes
  else none

theorem RecordRef.write_preserves_scopes {record : RecordRef abi schema} {state next : State}
    {path : List Nat} {targets : List AccessTarget} {value : IntegerBits}
    (written : record.write state path targets value = some next) :
    next.handles = state.handles ∧ next.views = state.views := by
  simp only [RecordRef.write, bind, pure, Option.bind_eq_some_iff,
    Option.ite_none_right_eq_some, Option.some.injEq] at written
  obtain ⟨_, _, _, _, _, _, _, rfl⟩ := written
  exact ⟨rfl, rfl⟩

theorem RecordRef.write_authorized {record : RecordRef abi schema} {state next : State}
    {path : List Nat} {targets : List AccessTarget} {value : IntegerBits}
    (written : record.write state path targets value = some next) :
    ∃ field, resolveInteger record.conforms path = some field ∧
      AccessAllowed state record.owner .exclusive field.byteOffsets targets := by
  simp only [RecordRef.write, bind, pure, Option.bind_eq_some_iff,
    Option.ite_none_right_eq_some, Option.some.injEq] at written
  obtain ⟨field, resolved, allowed, _⟩ := written
  exact ⟨field, resolved, (checkAccessTargets_correct ..).mp allowed⟩

theorem RecordRef.read_authorized {record : RecordRef abi schema} {state : State}
    {path : List Nat} {targets : List AccessTarget} {value : IntegerBits}
    (read : record.read state path targets = some value) :
    ∃ field, resolveInteger record.conforms path = some field ∧
      AccessAllowed state record.owner .shared field.byteOffsets targets := by
  simp only [RecordRef.read, bind, pure, Option.bind_eq_some_iff,
    Option.ite_none_right_eq_some, Option.some.injEq] at read
  obtain ⟨field, resolved, allowed, _⟩ := read
  exact ⟨field, resolved, (checkAccessTargets_correct ..).mp allowed⟩

private theorem replaceBytes_allocation (state : State) (owner : OwnerId) (bytes : List UInt8)
    {old : Allocation} (found : state.allocation owner = some old) :
    (replaceBytes state owner bytes).allocation owner = some { old with bytes } := by
  have owns : old.owner = owner := by simpa [State.allocation] using List.find?_some found
  simp only [replaceBytes, State.allocation, List.find?_map, Function.comp_def]
  have key (allocation : Allocation) :
      (if allocation.owner == owner then { allocation with bytes } else allocation).owner =
        allocation.owner := by split <;> rfl
  simp only [key]
  change (state.allocation owner).map _ = _
  simp [found, owns]

private theorem replaceBytes_other_allocation (state : State) (owner other : OwnerId)
    (bytes : List UInt8) (different : owner ≠ other) :
    (replaceBytes state owner bytes).allocation other = state.allocation other := by
  simp only [replaceBytes, State.allocation, List.find?_map, Function.comp_def]
  have key (allocation : Allocation) :
      (if allocation.owner == owner then { allocation with bytes } else allocation).owner =
        allocation.owner := by split <;> rfl
  simp only [key]
  change (state.allocation other).map _ = state.allocation other
  cases h : state.allocation other with
  | none => rfl
  | some old =>
    have owns : old.owner = other := by simpa [State.allocation] using List.find?_some h
    simp [owns, Ne.symm different]

theorem RecordRef.write_preserves_other_allocation {record : RecordRef abi schema} {state next : State}
    {path : List Nat} {targets : List AccessTarget} {value : IntegerBits} {other : OwnerId}
    (different : record.owner ≠ other) (written : record.write state path targets value = some next) :
    next.allocation other = state.allocation other := by
  simp only [RecordRef.write, bind, pure, Option.bind_eq_some_iff,
    Option.ite_none_right_eq_some, Option.some.injEq] at written
  obtain ⟨field, resolved, allowed, image, opened, updated, changed, rfl⟩ := written
  exact replaceBytes_other_allocation state record.owner other updated.toBytes different

private theorem replaceBytes_resources (state : State) (owner : OwnerId) (bytes : List UInt8)
    (extent : ∀ old ∈ state.allocations, old.owner = owner → old.bytes.length = bytes.length) :
    (replaceBytes state owner bytes).resources = state.resources := by
  simp only [replaceBytes, State.resources, List.map_map]
  congr 1
  apply List.map_congr_left
  intro allocation member
  by_cases same : allocation.owner = owner
  · simp [same, extent allocation member same]
  · simp [same]

theorem RecordRef.write_preserves_resources {record : RecordRef abi schema} {state next : State}
    {path : List Nat} {targets : List AccessTarget} {value : IntegerBits}
    (owners : state.OwnersValid) (written : record.write state path targets value = some next) :
    next.resources = state.resources := by
  simp only [RecordRef.write, bind, pure, Option.bind_eq_some_iff,
    Option.ite_none_right_eq_some, Option.some.injEq, RecordRef.openImage] at written
  obtain ⟨field, resolved, allowed, image, opened, updated, changed, rfl⟩ := written
  obtain ⟨allocation, found, imageMatches⟩ := opened
  split at imageMatches
  next sizeMatches =>
    apply replaceBytes_resources
    intro old member same
    have unique : old = allocation := by
      have allocationMember := List.mem_of_find?_eq_some found
      have allocationOwner : allocation.owner = record.owner := by
        simpa [State.allocation] using List.find?_some found
      obtain ⟨i, hi, atOld⟩ := List.mem_iff_getElem.mp member
      obtain ⟨j, hj, atAllocation⟩ := List.mem_iff_getElem.mp allocationMember
      have pairwise : state.allocations.Pairwise (fun a b => a.owner ≠ b.owner) :=
        List.pairwise_map.mp owners.1
      have pair := List.pairwise_iff_getElem.mp pairwise
      rcases Nat.lt_trichotomy i j with less | rfl | greater
      · have apart := pair i j hi hj less
        rw [atOld, atAllocation, same, allocationOwner] at apart
        exact (apart rfl).elim
      · exact atOld.symm.trans atAllocation
      · have apart := pair j i hj hi greater
        rw [atOld, atAllocation, same, allocationOwner] at apart
        exact (apart rfl).elim
    simp [Image.toBytes, unique, sizeMatches]
  next => cases imageMatches

/-- A successful runtime write installs the accessor's exact byte image,
including its preservation of all other integer leaves. -/
theorem RecordRef.write_effect {record : RecordRef abi schema} {state next : State}
    {path : List Nat} {targets : List AccessTarget} {value : IntegerBits}
    (written : record.write state path targets value = some next) :
    ∃ before after : Image record.layout.size,
      record.openImage state = some before ∧
      (next.allocation record.owner).map Allocation.bytes = some after.toBytes ∧
      readInteger record.conforms path after = some value ∧
      ∀ other, path ≠ other →
        readInteger record.conforms other after = readInteger record.conforms other before := by
  simp only [RecordRef.write, bind, pure, Option.bind_eq_some_iff,
    Option.ite_none_right_eq_some, Option.some.injEq] at written
  obtain ⟨field, resolved, allowed, before, opened, after, updated, rfl⟩ := written
  have live : ∃ old, state.allocation record.owner = some old := by
    simp only [RecordRef.openImage, bind, Option.bind_eq_some_iff] at opened
    exact match opened with | ⟨old, found, _⟩ => ⟨old, found⟩
  obtain ⟨old, found⟩ := live
  exact ⟨before, after, opened, by simp [replaceBytes_allocation _ _ _ found],
    readInteger_after_write record.conforms path before after value updated,
    fun _ separate => readInteger_preserved_other_path record.conforms separate updated⟩

end Aethel.AutomaticLayout
