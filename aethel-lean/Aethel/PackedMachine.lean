import Aethel.PackedType
import Aethel.RecordRuntime
import Aethel.ScopedForkJoin

namespace Aethel.AutomaticLayout

open Core Structured ScopedForkJoin

def PackedValueField.byteOffsets (field : PackedValueField size width) : List Nat :=
  bitIntervalBytes field.start width

theorem PackedValueField.mem_byteOffsets (field : PackedValueField size width) (byte : Nat) :
    byte ∈ field.byteOffsets ↔ 0 < width ∧ field.start / 8 ≤ byte ∧
      byte < (field.start + width + 7) / 8 := by
  unfold byteOffsets bitIntervalBytes
  split
  · rename_i empty
    simp [empty]
  · simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, within, rfl⟩
      omega
    · intro within
      exact ⟨byte - field.start / 8, by omega, by omega⟩

theorem PackedValueField.byteOffset_inBounds (field : PackedValueField size width)
    {byte : Nat} (member : byte ∈ field.byteOffsets) : byte < size := by
  have fits := field.fits
  have inside := (field.mem_byteOffsets byte).mp member
  omega

theorem PackedValueField.store_byte_outside (field : PackedValueField size width)
    (codec : PackedCodec α width) (image : Image size) (value : α)
    (byte : Fin size) (outside : byte.val ∉ field.byteOffsets) :
    field.store codec image value byte = image byte := by
  rw [field.mem_byteOffsets] at outside
  unfold PackedValueField.store Image.writeBytes
  exact ite_eq_left (by omega)

theorem PackedValueField.store_agrees_at_byte (field : PackedValueField size width)
    (codec : PackedCodec α width) (before after : Image size) (value : α)
    (byte : Fin size) (same : before byte = after byte) :
    field.store codec before value byte = field.store codec after value byte := by
  unfold PackedValueField.store Image.writeBytes
  rw [same]

theorem PackedValueField.store_commutes {a : PackedValueField size w} {b : PackedValueField size v}
    (first : PackedCodec α w) (second : PackedCodec β v) (image : Image size)
    (x : α) (y : β) (separate : ∀ byte ∈ a.byteOffsets, byte ∉ b.byteOffsets) :
    b.store second (a.store first image x) y = a.store first (b.store second image y) x := by
  funext byte
  by_cases inA : byte.val ∈ a.byteOffsets
  · have outB := separate byte.val inA
    rw [b.store_byte_outside second _ y byte outB]
    exact (a.store_agrees_at_byte first _ image x byte
      (b.store_byte_outside second image y byte outB)).symm
  · rw [a.store_byte_outside first _ x byte inA]
    exact b.store_agrees_at_byte second _ image y byte (a.store_byte_outside first image x byte inA)

private def PackedValueField.needsMerge (field : PackedValueField size width) (byte : Nat) : Bool :=
  !(decide (field.start ≤ byte * 8 ∧ byte * 8 + 8 ≤ field.start + width))

def PackedValueField.mergeOffsets (field : PackedValueField size width) : List Nat :=
  field.byteOffsets.filter field.needsMerge

theorem PackedValueField.mergeOffset_boundary (field : PackedValueField size width)
    {byte : Nat} (member : byte ∈ field.mergeOffsets) :
    byte = field.start / 8 ∨ byte = (field.start + width - 1) / 8 := by
  obtain ⟨touched, masked⟩ := List.mem_filter.mp member
  have inside := (field.mem_byteOffsets byte).mp touched
  simp only [needsMerge, Bool.not_eq_true', decide_eq_false_iff_not] at masked
  omega

/-- A touched byte uses a sub-byte shift for the mask and a valid payload
bit index when extracting from the unshifted value. -/
theorem PackedValueField.storeShifts_inBounds (field : PackedValueField size width)
    {byte : Nat} (member : byte ∈ field.byteOffsets) :
    field.start - byte * 8 < 8 ∧ 8 - (field.start + width - byte * 8) < 8 ∧
      byte * 8 - field.start < width := by
  have inside := (field.mem_byteOffsets byte).mp member
  omega

def PackedValueField.footprint (field : PackedValueField size width)
    (owner : OwnerId) (mode : AccessMode) : TaskFootprint :=
  let locations := field.byteOffsets.map fun byte => ⟨owner, byte⟩
  match mode with
  | .shared => ⟨locations, []⟩
  | .exclusive => ⟨field.mergeOffsets.map (fun byte => ⟨owner, byte⟩), locations⟩

/-- Compute only the byte stores in the checked interval. The stored byte
values include the preserved bits on either boundary of the interval. -/
def PackedValueField.patch (field : PackedValueField size width) (owner : OwnerId)
    (codec : PackedCodec α width) (before : Image size) (value : α) : TaskWrites :=
  let updated := field.store codec before value
  field.byteOffsets.attach.map fun byte =>
    (⟨owner, byte.val⟩, UInt8.ofBitVec (updated ⟨byte.val, field.byteOffset_inBounds byte.property⟩))

private theorem PackedValueField.patch_locations (field : PackedValueField size width)
    (owner : OwnerId) (codec : PackedCodec α width) (before : Image size) (value : α) :
    (field.patch owner codec before value).map Prod.fst =
      field.byteOffsets.map (fun byte => ⟨owner, byte⟩) := by
  simp [patch, List.map_map, Function.comp_def]

theorem PackedValueField.patch_within (field : PackedValueField size width) (owner : OwnerId)
    (codec : PackedCodec α width) (before : Image size) (value : α) :
    WritesWithin (field.patch owner codec before value) (field.footprint owner .exclusive) := by
  intro write member
  obtain ⟨byte, _, rfl⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨byte.val, byte.property, rfl⟩

/-- Recomputing a store can only depend on the previous values of the
partial boundary bytes. Full bytes come directly from the incoming value. -/
theorem PackedValueField.patch_eq_of_mergeBytes (field : PackedValueField size width)
    (owner : OwnerId) (codec : PackedCodec α width) (before after : Image size) (value : α)
    (equal : ∀ byte : Fin size, byte.val ∈ field.mergeOffsets → before byte = after byte) :
    field.patch owner codec before value = field.patch owner codec after value := by
  unfold patch
  apply List.map_congr_left
  intro offset _
  congr 2
  have inside := (field.mem_byteOffsets _).mp offset.property
  let byte : Fin size := ⟨offset.val, field.byteOffset_inBounds offset.property⟩
  change field.store codec before value byte = field.store codec after value byte
  have touches : ¬ (width = 0 ∨ byte.val * 8 + 8 ≤ field.start ∨
      field.start + width ≤ byte.val * 8) := by
    dsimp [byte]
    omega
  unfold PackedValueField.store Image.writeBytes
  rw [ite_eq_right touches, ite_eq_right touches]
  split
  · rfl
  · rename_i partialByte
    have merge : byte.val ∈ field.mergeOffsets := by
      exact List.mem_filter.mpr ⟨offset.property, by simp [needsMerge, partialByte]⟩
    rw [equal byte merge]

theorem PackedValueField.patches_commute
    (a : PackedValueField sizeA widthA) (b : PackedValueField sizeB widthB)
    (ownerA ownerB : OwnerId) (codecA : PackedCodec α widthA) (codecB : PackedCodec β widthB)
    (beforeA : Image sizeA) (beforeB : Image sizeB) (valueA : α) (valueB : β)
    (safe : checkForkDisjoint (a.footprint ownerA .exclusive) (b.footprint ownerB .exclusive) = true)
    (state : State) (location : ByteLocation) :
    let patchA := a.patch ownerA codecA beforeA valueA
    let patchB := b.patch ownerB codecB beforeB valueB
    (applyTaskWrites (applyTaskWrites state patchA) patchB).byte location =
      (applyTaskWrites (applyTaskWrites state patchB) patchA).byte location :=
  forkDisjoint_writes_commute safe (a.patch_within ownerA codecA beforeA valueA)
    (b.patch_within ownerB codecB beforeB valueB) state location

theorem PackedValueField.load_eq_of_byteOffsets (field : PackedValueField size width)
    (codec : PackedCodec α width) (before after : Image size)
    (equal : ∀ byte : Fin size, byte.val ∈ field.byteOffsets → before byte = after byte) :
    field.load codec before = field.load codec after := by
  unfold load
  simp only [Image.readBytes_refines]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro bit within
  rw [Image.readBits_getLsbD _ _ _ within, Image.readBits_getLsbD _ _ _ within]
  have addr : (field.start + bit) / 8 ∈ field.byteOffsets :=
    (field.mem_byteOffsets _).mpr (by omega)
  have bound := field.byteOffset_inBounds addr
  simp only [Image.bit, dite_eq_left bound, equal ⟨_, bound⟩ addr]

theorem PackedValueField.load_stable {reader : PackedValueField size w}
    {writer : PackedValueField size v} (decode : PackedCodec α w) (encode : PackedCodec β v)
    (image : Image size) (value : β)
    (separate : ∀ byte ∈ reader.byteOffsets, byte ∉ writer.byteOffsets) :
    reader.load decode (writer.store encode image value) = reader.load decode image :=
  reader.load_eq_of_byteOffsets decode _ image (fun byte within =>
    writer.store_byte_outside encode image value byte (separate byte.val within))

private theorem applyTaskWrites_byte_value (writes : TaskWrites) (state : State)
    (location : ByteLocation) (old value : UInt8) (present : state.byte location = some old)
    (values : ∀ p ∈ writes, p.1 = location → p.2 = value) :
    (applyTaskWrites state writes).byte location =
      some (if writes.any (fun p => p.1 == location) then value else old) := by
  induction writes generalizing state old with
  | nil => exact present
  | cons first rest ih =>
    have tailValues := fun p member => values p (List.mem_cons_of_mem _ member)
    change (applyTaskWrites (state.store first.1 first.2) rest).byte location = _
    by_cases same : first.1 = location
    · have equalValue := values first List.mem_cons_self same
      have newPresent : (state.store first.1 first.2).byte location = some value := by
        rw [same, equalValue]
        exact State.store_byte_written state location old value present
      rw [ih _ _ newPresent tailValues]
      simp [same]
    · have oldPresent : (state.store first.1 first.2).byte location = some old :=
        (State.store_byte_other state first.1 location first.2 same).trans present
      rw [ih _ _ oldPresent tailValues]
      have different : (first.1 == location) = false := Bool.eq_false_iff.mpr
        (fun equal => same (eq_of_beq equal))
      simp only [List.any_cons, different, Bool.false_or]

theorem PackedValueField.patch_refines (field : PackedValueField size width)
    (codec : PackedCodec α width) (before : Image size) (value : α)
    (owner : OwnerId) (byte : Fin size) (state : State)
    (present : state.byte ⟨owner, byte.val⟩ = some (UInt8.ofBitVec (before byte))) :
    (applyTaskWrites state (field.patch owner codec before value)).byte ⟨owner, byte.val⟩ =
      some (UInt8.ofBitVec (field.store codec before value byte)) := by
  rw [applyTaskWrites_byte_value _ _ _ _ (UInt8.ofBitVec (field.store codec before value byte))
    present]
  · by_cases member : byte.val ∈ field.byteOffsets
    · have any : (field.patch owner codec before value).any
          (fun p => p.1 == (⟨owner, byte.val⟩ : ByteLocation)) = true := by
        apply List.any_eq_true.mpr
        refine ⟨_, List.mem_map.mpr ⟨⟨byte.val, member⟩, List.mem_attach _ _, rfl⟩, ?_⟩
        exact beq_self_eq_true _
      simp [any]
    · simp [field.store_byte_outside codec before value byte member]
  · intro write member same
    obtain ⟨offset, _, rfl⟩ := List.mem_map.mp member
    have eq : (⟨offset.val, field.byteOffset_inBounds offset.property⟩ : Fin size) = byte :=
      Fin.ext (congrArg ByteLocation.offset same)
    rw [eq]

/-- Interpret the stores using ordinary machine write instructions. Each
capability must still identify the byte named by that store. -/
def runPackedStores : State → TaskWrites → List AccessTarget → Option State
  | state, [], [] => some state
  | state, (location, value) :: rest, target :: remaining => do
    if target.location state = some location then
      let next ← execute state (target.writeInstruction value)
      runPackedStores next rest remaining
    else none
  | _, _, _ => none

private theorem packedStore_step {state next : State} {target : AccessTarget}
    {location : ByteLocation} {value : UInt8}
    (atLocation : target.location state = some location)
    (step : Step state (target.writeInstruction value) next) :
    next = state.store location value := by
  cases target <;> cases step <;> simp_all [AccessTarget.location]

theorem runPackedStores_sound {state next : State} {stores : TaskWrites}
    {targets : List AccessTarget} (ran : runPackedStores state stores targets = some next) :
    Runs state ((stores.zip targets).map fun (entry, target) => target.writeInstruction entry.2) next ∧
      next = applyTaskWrites state stores := by
  induction stores generalizing state next targets with
  | nil =>
    cases targets <;> simp [runPackedStores] at ran
    subst next
    exact ⟨.nil, rfl⟩
  | cons first rest ih =>
    cases targets with
    | nil => simp [runPackedStores] at ran
    | cons target remaining =>
      obtain ⟨location, value⟩ := first
      simp only [runPackedStores, Option.ite_none_right_eq_some, bind,
        Option.bind_eq_some_iff] at ran
      obtain ⟨atLocation, mid, wrote, continues⟩ := ran
      obtain ⟨suffix, effect⟩ := ih continues
      have step := execute_sound wrote
      exact ⟨.cons step suffix, effect.trans (congrArg
        (fun s => applyTaskWrites s rest) (packedStore_step atLocation step))⟩

private def recordImage (state : State) (owner : OwnerId) (size : Nat) : Option (Image size) := do
  let allocation ← state.allocation owner
  if same : allocation.bytes.length = size then
    some (same ▸ Image.ofBytes allocation.bytes)
  else none

private theorem recordImage_byte {state : State} {owner : OwnerId} {size : Nat}
    {before : Image size} (opened : recordImage state owner size = some before)
    (byte : Fin size) :
    state.byte ⟨owner, byte.val⟩ = some (UInt8.ofBitVec (before byte)) := by
  simp only [recordImage, bind, Option.bind_eq_some_iff] at opened
  obtain ⟨allocation, located, image⟩ := opened
  split at image
  · rename_i length
    subst size
    cases image
    simp [State.byte, located, bind, Image.ofBytes]
  · contradiction

private theorem readTrace_observations {state next : State} {owner : OwnerId} {offsets : List Nat}
    {targets : List AccessTarget} {readAt : Nat → UInt8}
    (length : offsets.length = targets.length)
    (locations : ∀ pair ∈ offsets.zip targets, pair.2.location state = some ⟨owner, pair.1⟩)
    (contents : ∀ byte ∈ offsets, state.byte ⟨owner, byte⟩ = some (readAt byte))
    (ran : Runs state (targets.map AccessTarget.readInstruction) next) :
    next.observations = (offsets.map readAt).reverse ++ state.observations := by
  induction offsets generalizing state targets with
  | nil =>
    cases targets with
    | nil => cases ran; rfl
    | cons _ _ => simp at length
  | cons byte rest ih =>
    cases targets with
    | nil => simp at length
    | cons target remaining =>
      cases ran with
      | cons head tail =>
        obtain ⟨value, rfl⟩ := target.read_observes head
        have current := AccessTarget.read_current_byte ((target.read_correct state value _).mpr ⟨head, rfl⟩)
        rw [locations _ List.mem_cons_self] at current
        have valueAt : value = readAt byte := by
          exact Option.some.inj (current.symm.trans (contents byte List.mem_cons_self))
        have suffix := ih (state := state.observe value) (by simpa using length)
          (fun pair member => locations pair (List.mem_cons_of_mem _ member))
          (fun byte member => contents byte (List.mem_cons_of_mem _ member)) tail
        simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append,
          State.observe, valueAt] using suffix

private def observedBytes (next : State) (count : Nat) : List (BitVec 8) :=
  ((next.observations.take count).reverse).map UInt8.toBitVec

private theorem observedBytes_eq_image {state next : State} {owner : OwnerId} {size : Nat}
    {offsets : List Nat} {targets : List AccessTarget} {image : Image size}
    (length : offsets.length = targets.length)
    (locations : ∀ pair ∈ offsets.zip targets, pair.2.location state = some ⟨owner, pair.1⟩)
    (fits : ∀ byte ∈ offsets, byte < size)
    (opened : recordImage state owner size = some image)
    (ran : Runs state (targets.map AccessTarget.readInstruction) next) :
    observedBytes next targets.length = image.bytesAt offsets := by
  let readAt := fun byte => UInt8.ofBitVec (if h : byte < size then image ⟨byte, h⟩ else 0)
  have contents : ∀ byte ∈ offsets, state.byte ⟨owner, byte⟩ = some (readAt byte) := by
    intro byte member
    simpa [readAt, dite_eq_left (fits byte member)] using recordImage_byte opened ⟨byte, fits byte member⟩
  have observations := readTrace_observations length locations contents ran
  simp [observedBytes, observations, ← length, List.map_map, Function.comp_def, readAt, Image.bytesAt]

def PackedValueField.readMachine (field : PackedValueField size width)
    (codec : PackedCodec α width) (state : State) (owner : OwnerId)
    (targets : List AccessTarget) : Option α := do
  if checkAccessTargets state owner .shared field.byteOffsets targets then
    let next ← Core.run state (targets.map AccessTarget.readInstruction)
    let _ ← recordImage state owner size
    codec.decode (decodeLittleEndianBytes (observedBytes next targets.length) (field.start % 8) width)
  else none

private def PackedValueField.mergeTargets (field : PackedValueField size width)
    (targets : List AccessTarget) : List AccessTarget :=
  (field.byteOffsets.zip targets).filterMap fun (byte, target) =>
    if field.needsMerge byte then some target else none

def PackedValueField.mergeTrace (field : PackedValueField size width)
    (targets : List AccessTarget) : Program :=
  (field.mergeTargets targets).map AccessTarget.readInstruction

private theorem mergeTargets_corresponds (offsets : List Nat) (targets : List AccessTarget)
    (pick : Nat → Bool) (length : offsets.length = targets.length) :
    let merge := (offsets.zip targets).filterMap fun (byte, target) => if pick byte then some target else none
    (offsets.filter pick).length = merge.length ∧
      (offsets.filter pick).zip merge = (offsets.zip targets).filter (fun pair => pick pair.1) := by
  induction offsets generalizing targets with
  | nil => simp
  | cons byte rest ih =>
    cases targets with
    | nil => simp at length
    | cons target remaining =>
      have suffix := ih remaining (by simpa using length)
      cases selected : pick byte <;> simpa [selected] using suffix

private theorem runReadTrace_only_observes {state next : State} {targets : List AccessTarget}
    (ran : Runs state (targets.map AccessTarget.readInstruction) next) :
    next = { state with observations := next.observations } := by
  induction targets generalizing state with
  | nil => cases ran; rfl
  | cons target _ ih =>
    cases ran with
    | cons step suffix =>
      obtain ⟨value, rfl⟩ := target.read_observes step
      exact ih (state := state.observe value) suffix

private def sampleImage (field : PackedValueField size width) (samples : List (BitVec 8)) : Image size :=
  let byOffset := field.mergeOffsets.zip samples
  fun byte => (byOffset.lookup byte.val).getD 0

private def mergeImage (field : PackedValueField size width) (observed : State)
    (targets : List AccessTarget) : Image size :=
  sampleImage field (observedBytes observed (field.mergeTargets targets).length)

private theorem lookup_zip_samples {offsets : List Nat} {byte : Nat} (samples : Nat → BitVec 8)
    (member : byte ∈ offsets) : (offsets.zip (offsets.map samples)).lookup byte = some (samples byte) := by
  induction offsets with
  | nil => simp at member
  | cons head tail ih =>
    by_cases atHead : byte = head
    · subst head
      simp
    · have later : byte ∈ tail := (List.mem_cons.mp member).resolve_left atHead
      have misses : (byte == head) = false := Bool.eq_false_iff.mpr (fun h => atHead (eq_of_beq h))
      simpa [List.lookup, misses] using ih later

private theorem sampleImage_agrees {field : PackedValueField size width} {image : Image size}
    (byte : Fin size) (member : byte.val ∈ field.mergeOffsets) :
    sampleImage field (image.bytesAt field.mergeOffsets) byte = image byte := by
  simp only [sampleImage, Image.bytesAt, lookup_zip_samples _ member,
    Option.getD_some, dite_eq_left byte.isLt]

private theorem mergeSamples_eq_image {field : PackedValueField size width} {state observed : State}
    {owner : OwnerId} {targets : List AccessTarget} {image : Image size}
    (allowed : AccessAllowed state owner .exclusive field.byteOffsets targets)
    (opened : recordImage state owner size = some image)
    (reads : Runs state (field.mergeTrace targets) observed) :
    observedBytes observed (field.mergeTargets targets).length = image.bytesAt field.mergeOffsets := by
  have extent := mergeTargets_corresponds field.byteOffsets targets field.needsMerge allowed.1
  change field.mergeOffsets.length = (field.mergeTargets targets).length ∧
    field.mergeOffsets.zip (field.mergeTargets targets) =
      (field.byteOffsets.zip targets).filter (fun pair => field.needsMerge pair.1) at extent
  have pairMatches pair (paired : pair ∈ field.mergeOffsets.zip (field.mergeTargets targets)) :=
    (allowed.2 pair (List.mem_filter.mp (extent.2 ▸ paired)).1).1
  have fits address (included : address ∈ field.mergeOffsets) :=
    field.byteOffset_inBounds (List.mem_filter.mp included).1
  exact observedBytes_eq_image extent.1 pairMatches fits opened reads

private theorem mergeImage_agrees {field : PackedValueField size width} {state observed : State}
    {owner : OwnerId} {targets : List AccessTarget} {image : Image size}
    (allowed : AccessAllowed state owner .exclusive field.byteOffsets targets)
    (opened : recordImage state owner size = some image)
    (reads : Runs state (field.mergeTrace targets) observed)
    (byte : Fin size) (member : byte.val ∈ field.mergeOffsets) :
    mergeImage field observed targets byte = image byte := by
  rw [mergeImage, mergeSamples_eq_image allowed opened reads]
  exact sampleImage_agrees byte member

private theorem applyTaskWrites_resources (state : State) (writes : TaskWrites) :
    (applyTaskWrites state writes).resources = state.resources := by
  induction writes generalizing state with
  | nil => rfl
  | cons entry rest ih =>
    change (applyTaskWrites (state.store entry.1 entry.2) rest).resources = state.resources
    rw [ih, State.resources_store]

private theorem run_of_resources {state next final : State} {trace : Program}
    (same : next.resources = state.resources) (ran : Core.run state trace = some final) :
    ∃ result, Core.run next trace = some result := by
  have result := (checkResources_correct next trace).symm
  rw [same, checkResources_correct, ran, Option.map_some] at result
  obtain ⟨result, ran, _⟩ := Option.map_eq_some_iff.mp result
  exact ⟨result, ran⟩

private theorem runPackedStores_of_resources {state next final : State} {stores replacement : TaskWrites}
    {targets : List AccessTarget} (same : next.resources = state.resources)
    (locations : replacement.map Prod.fst = stores.map Prod.fst)
    (ran : runPackedStores state stores targets = some final) :
    ∃ result, runPackedStores next replacement targets = some result := by
  induction stores generalizing state next targets replacement with
  | nil =>
    have empty : replacement = [] := List.map_eq_nil_iff.mp locations
    subst replacement
    cases targets <;> simp [runPackedStores] at ran ⊢
  | cons write rest ih =>
    cases targets with
    | nil => simp [runPackedStores] at ran
    | cons target remaining =>
      obtain ⟨location, value⟩ := write
      cases replacement with
      | nil => simp at locations
      | cons entry newRest =>
        obtain ⟨newLocation, newValue⟩ := entry
        simp only [List.map_cons, List.cons.injEq] at locations
        obtain ⟨rfl, sameTail⟩ := locations
        simp only [runPackedStores, Option.ite_none_right_eq_some, bind,
          Option.bind_eq_some_iff] at ran ⊢
        obtain ⟨located, middle, wrote, suffix⟩ := ran
        have nextLocation : target.location next = some newLocation := by
          rw [← target.location_resources next, same, target.location_resources state, located]
        have allowed := (checkInstruction_correct next (target.writeInstruction newValue)).symm
        rw [same, target.check_value state.resources newValue value, checkInstruction_correct, wrote,
          Option.map_some] at allowed
        obtain ⟨updated, ranWrite, _⟩ := Option.map_eq_some_iff.mp allowed
        have resourcesAfter : updated.resources = middle.resources := by
          rw [packedStore_step nextLocation (execute_sound ranWrite),
            packedStore_step located (execute_sound wrote), State.resources_store, State.resources_store, same]
        obtain ⟨result, continues⟩ := ih resourcesAfter sameTail suffix
        exact ⟨result, nextLocation, updated, ranWrite, continues⟩

def PackedValueField.writeMachine (field : PackedValueField size width)
    (codec : PackedCodec α width) (state : State) (owner : OwnerId)
    (targets : List AccessTarget) (value : α) : Option State := do
  if checkAccessTargets state owner .exclusive field.byteOffsets targets then
    let _ ← recordImage state owner size
    let observed ← Core.run state (field.mergeTrace targets)
    runPackedStores observed (field.patch owner codec (mergeImage field observed targets) value) targets
  else none

private def PackedValueField.writeInstructions (field : PackedValueField size width)
    (codec : PackedCodec α width) (owner : OwnerId) (image : Image size)
    (targets : List AccessTarget) (value : α) : Program :=
  ((field.patch owner codec image value).zip targets).map
    (fun (entry, target) => target.writeInstruction entry.2)

private def PackedValueField.storeInstructions (field : PackedValueField size width)
    (codec : PackedCodec α width) (owner : OwnerId) (image : Image size)
    (targets : List AccessTarget) (value : α) : Program :=
  field.mergeTrace targets ++ field.writeInstructions codec owner image targets value

/-- Form the write instructions after collecting the task's own boundary-byte
samples in program order. The payload supplies every fully covered byte. -/
def PackedValueField.writeInstructionsFromSamples (field : PackedValueField size width)
    (codec : PackedCodec α width) (owner : OwnerId) (targets : List AccessTarget) (value : α)
    (samples : List (BitVec 8)) : Option Program :=
  if samples.length = field.mergeOffsets.length then
    some (field.writeInstructions codec owner (sampleImage field samples) targets value)
  else none

def PackedValueField.writeProgram (field : PackedValueField size width)
    (codec : PackedCodec α width) (state : State) (owner : OwnerId)
    (targets : List AccessTarget) (value : α) : Option Program :=
  (recordImage state owner size).map fun image => field.storeInstructions codec owner image targets value

private theorem readInstruction_byteAccess (target : AccessTarget) (state : State) :
    target.readInstruction.byteAccess state.resources = (target.location state).map ByteAccess.read := by
  rw [← target.location_resources state]
  cases target <;> simp [AccessTarget.readInstruction, AccessTarget.location,
    Instruction.byteAccess, Option.map_map, Function.comp_def]

private theorem writeInstruction_byteAccess (target : AccessTarget) (state : State) (byte : UInt8) :
    (target.writeInstruction byte).byteAccess state.resources =
      (target.location state).map (fun place => .write place byte) := by
  rw [← target.location_resources state]
  cases target <;> simp [AccessTarget.writeInstruction, AccessTarget.location,
    Instruction.byteAccess, Option.map_map, Function.comp_def]

private theorem byteAccesses_of_zip {α : Type} {entries : List α} {targets : List AccessTarget}
    (state : State) (emit : α × AccessTarget → Instruction) (expected : α → ByteAccess)
    (length : entries.length = targets.length)
    (exactAccess : ∀ pair ∈ entries.zip targets,
      (emit pair).byteAccess state.resources = some (expected pair.1)) :
    ((entries.zip targets).map emit).mapM (Instruction.byteAccess state.resources) =
      some (entries.map expected) := by
  induction entries generalizing targets with
  | nil => rfl
  | cons entry rest ih =>
    cases targets with
    | nil => simp at length
    | cons target tail =>
      have remaining := ih (by simpa using length)
        (fun pair member => exactAccess pair (List.mem_cons_of_mem _ member))
      simp [List.mapM_cons, exactAccess _ List.mem_cons_self, remaining, bind, pure]

private theorem resolvedReadInstructions {state : State} {owner : OwnerId}
    {offsets : List Nat} {targets : List AccessTarget}
    (length : offsets.length = targets.length)
    (located : ∀ pair ∈ offsets.zip targets, pair.2.location state = some ⟨owner, pair.1⟩) :
    (targets.map AccessTarget.readInstruction).mapM (Instruction.byteAccess state.resources) =
      some (offsets.map (fun byte => .read ⟨owner, byte⟩)) := by
  have exactReads := byteAccesses_of_zip state (fun pair : Nat × AccessTarget => pair.2.readInstruction)
    (fun byte => .read ⟨owner, byte⟩) length (fun pair member => by
      rw [readInstruction_byteAccess, located pair member]; rfl)
  have same : ((offsets.zip targets).map (fun pair => pair.2.readInstruction)) =
      targets.map AccessTarget.readInstruction := by
    change (offsets.zip targets).map (AccessTarget.readInstruction ∘ Prod.snd) = _
    rw [← List.map_map, List.map_snd_zip (Nat.le_of_eq length.symm)]
  rwa [same] at exactReads

theorem PackedValueField.readProgram_byteAccesses (field : PackedValueField size width)
    {state : State} {owner : OwnerId} {targets : List AccessTarget}
    (allowed : AccessAllowed state owner .shared field.byteOffsets targets) :
    (targets.map AccessTarget.readInstruction).mapM (Instruction.byteAccess state.resources) =
      some (field.byteOffsets.map (fun byte => .read ⟨owner, byte⟩)) :=
  resolvedReadInstructions allowed.1 (fun pair member => (allowed.2 pair member).1)

private theorem PackedValueField.mergeTrace_byteAccesses (field : PackedValueField size width)
    {state : State} {owner : OwnerId} {targets : List AccessTarget}
    (allowed : AccessAllowed state owner .exclusive field.byteOffsets targets) :
    (field.mergeTrace targets).mapM (Instruction.byteAccess state.resources) =
      some (field.mergeOffsets.map (fun byte => .read ⟨owner, byte⟩)) := by
  obtain ⟨length, paired⟩ := mergeTargets_corresponds field.byteOffsets targets field.needsMerge allowed.1
  apply resolvedReadInstructions length
  intro pair member
  rw [paired] at member
  exact (allowed.2 pair (List.mem_filter.mp member).1).1

private theorem PackedValueField.writeInstructions_byteAccesses (field : PackedValueField size width)
    (codec : PackedCodec α width) {state : State} {owner : OwnerId}
    {targets : List AccessTarget} (image : Image size) (value : α)
    (allowed : AccessAllowed state owner .exclusive field.byteOffsets targets) :
    (field.writeInstructions codec owner image targets value).mapM (Instruction.byteAccess state.resources) =
      some ((field.patch owner codec image value).map (fun entry => .write entry.1 entry.2)) := by
  have locations := field.patch_locations owner codec image value
  have length := congrArg List.length locations
  simp only [List.length_map] at length
  exact byteAccesses_of_zip state (fun pair : (ByteLocation × UInt8) × AccessTarget =>
    pair.2.writeInstruction pair.1.2) (fun entry => .write entry.1 entry.2)
    (length.trans allowed.1) (fun pair member => by
      have located : (pair.1.1, pair.2) ∈ ((field.patch owner codec image value).map Prod.fst).zip targets := by
        rw [List.zip_map_left]
        exact List.mem_map_of_mem member
      rw [locations, List.zip_map_left] at located
      obtain ⟨original, originalMember, same⟩ := List.mem_map.mp located
      have target := congrArg Prod.snd same
      have address := congrArg Prod.fst same
      change original.2 = pair.2 at target
      change (⟨owner, original.1⟩ : ByteLocation) = pair.1.1 at address
      rw [writeInstruction_byteAccess, ← target, (allowed.2 original originalMember).1, address]
      rfl)

private theorem PackedValueField.storeInstructions_byteAccesses (field : PackedValueField size width)
    (codec : PackedCodec α width) {state : State} {owner : OwnerId}
    {targets : List AccessTarget} (image : Image size) (value : α)
    (allowed : AccessAllowed state owner .exclusive field.byteOffsets targets) :
    (field.storeInstructions codec owner image targets value).mapM (Instruction.byteAccess state.resources) =
      some (field.mergeOffsets.map (fun byte => .read ⟨owner, byte⟩) ++
        (field.patch owner codec image value).map (fun entry => .write entry.1 entry.2)) := by
  simp [storeInstructions, List.mapM_append, field.mergeTrace_byteAccesses allowed,
    field.writeInstructions_byteAccesses codec image value allowed, bind, pure]

theorem PackedValueField.readProgram_footprint (field : PackedValueField size width)
    {state : State} {owner : OwnerId} {targets : List AccessTarget}
    (allowed : AccessAllowed state owner .shared field.byteOffsets targets) :
    TaskFootprint.ofProgram state.resources (targets.map AccessTarget.readInstruction) =
      some (field.footprint owner .shared) := by
  simp [TaskFootprint.ofProgram, field.readProgram_byteAccesses allowed, TaskFootprint.ofByteAccesses,
    footprint, List.filterMap_map, Function.comp_def, List.filterMap_eq_map']

theorem PackedValueField.writeProgram_footprint (field : PackedValueField size width)
    (codec : PackedCodec α width) {state : State} {owner : OwnerId} {targets : List AccessTarget}
    {value : α} {program : Program}
    (allowed : AccessAllowed state owner .exclusive field.byteOffsets targets)
    (compiled : field.writeProgram codec state owner targets value = some program) :
    TaskFootprint.ofProgram state.resources program = some (field.footprint owner .exclusive) := by
  obtain ⟨image, _, rfl⟩ := Option.map_eq_some_iff.mp compiled
  simp [TaskFootprint.ofProgram, field.storeInstructions_byteAccesses codec image value allowed,
    TaskFootprint.ofByteAccesses, footprint, List.filterMap_append, List.filterMap_map,
    Function.comp_def, List.filterMap_eq_map', field.patch_locations]

theorem readInstructions_are_byteAccesses (targets : List AccessTarget) :
    (targets.map AccessTarget.readInstruction).all Instruction.isByteAccess = true := by
  apply List.all_eq_true.mpr
  intro _ member
  obtain ⟨target, _, rfl⟩ := List.mem_map.mp member
  cases target <;> rfl

theorem PackedValueField.writeProgram_accesses (field : PackedValueField size width)
    (codec : PackedCodec α width) {state : State} {owner : OwnerId} {targets : List AccessTarget}
    {value : α} {program : Program}
    (compiled : field.writeProgram codec state owner targets value = some program) :
    program.all Instruction.isByteAccess = true := by
  obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp compiled
  rw [storeInstructions, writeInstructions, List.all_append, mergeTrace, readInstructions_are_byteAccesses, Bool.true_and]
  apply List.all_eq_true.mpr
  intro _ member
  obtain ⟨⟨_, target⟩, _, rfl⟩ := List.mem_map.mp member
  cases target <;> rfl

theorem PackedValueField.writeMachine_refines (field : PackedValueField size width)
    (codec : PackedCodec α width) {state next : State} {owner : OwnerId}
    {targets : List AccessTarget} {value : α}
    (ran : field.writeMachine codec state owner targets value = some next) :
    AccessAllowed state owner .exclusive field.byteOffsets targets ∧
    ∃ image, recordImage state owner size = some image ∧
      Runs state (field.storeInstructions codec owner image targets value) next ∧
      next.resources = state.resources ∧
      ∀ byte : Fin size, next.byte ⟨owner, byte.val⟩ =
        some (UInt8.ofBitVec (field.store codec image value byte)) := by
  simp only [writeMachine, Option.ite_none_right_eq_some, checkAccessTargets_correct, bind,
    Option.bind_eq_some_iff] at ran
  obtain ⟨allowed, image, opened, observed, reading, ran⟩ := ran
  have reads := Core.run_sound reading
  have patch := field.patch_eq_of_mergeBytes owner codec (mergeImage field observed targets) image value
    (mergeImage_agrees allowed opened reads)
  rw [patch] at ran
  obtain ⟨steps, effect⟩ := runPackedStores_sound ran
  have readOnly := runReadTrace_only_observes reads
  refine ⟨allowed, image, opened, reads.append steps, ?_, fun byte => ?_⟩
  · rw [effect, applyTaskWrites_resources]
    rw [readOnly]
    rfl
  · rw [effect]
    apply field.patch_refines
    have alive := recordImage_byte opened byte
    have unchanged := congrArg State.allocations readOnly
    simpa only [State.byte, State.allocation, unchanged] using alive

theorem PackedValueField.writeProgram_correct (field : PackedValueField size width)
    (codec : PackedCodec α width) {state next : State} {owner : OwnerId}
    {targets : List AccessTarget} {value : α}
    (ran : field.writeMachine codec state owner targets value = some next) :
    ∃ program, field.writeProgram codec state owner targets value = some program ∧ Runs state program next := by
  obtain ⟨_, _, opened, traced, _⟩ := field.writeMachine_refines codec ran
  exact ⟨_, by simp [writeProgram, opened], traced⟩

theorem PackedValueField.readMachine_authorized (field : PackedValueField size width)
    (codec : PackedCodec α width) {state : State} {owner : OwnerId}
    {targets : List AccessTarget} {value : α}
    (result : field.readMachine codec state owner targets = some value) :
    AccessAllowed state owner .shared field.byteOffsets targets := by
  simp only [readMachine, Option.ite_none_right_eq_some, checkAccessTargets_correct] at result
  exact result.1

theorem PackedValueField.readMachine_refines (field : PackedValueField size width)
    (codec : PackedCodec α width) {state : State} {owner : OwnerId}
    {targets : List AccessTarget} {value : α}
    (result : field.readMachine codec state owner targets = some value) :
    ∃ next image, Runs state (targets.map AccessTarget.readInstruction) next ∧
      recordImage state owner size = some image ∧ field.load codec image = some value := by
  simp only [readMachine, Option.ite_none_right_eq_some, checkAccessTargets_correct, bind,
    Option.bind_eq_some_iff] at result
  obtain ⟨allowed, next, ran, image, opened, loaded⟩ := result
  have bytes := observedBytes_eq_image allowed.1 (fun pair member => (allowed.2 pair member).1)
    (fun _ member => field.byteOffset_inBounds member) opened (run_sound ran)
  rw [bytes] at loaded
  exact ⟨next, image, run_sound ran, opened, loaded⟩

theorem PackedValueField.readMachine_on_storage (field : PackedValueField size width)
    (codec : PackedCodec α width) {state : State} {owner : OwnerId}
    {targets : List AccessTarget} {value : α}
    (result : field.readMachine codec state owner targets = some value) :
    RunsOnStorage state (targets.map AccessTarget.readInstruction) state := by
  obtain ⟨next, _, reads, _, _⟩ := field.readMachine_refines codec result
  exact ⟨next, reads, by rw [runReadTrace_only_observes reads]; rfl⟩

/-- An allocation has the exact record extent and represents the image's
bytes. The extent also witnesses a live owner when the image has zero bytes. -/
def Image.InAllocation (image : Image size) (owner : OwnerId) (state : State) : Prop :=
  state.resources.extent owner = some size ∧
    ∀ byte : Fin size, state.byte ⟨owner, byte.val⟩ = some (UInt8.ofBitVec (image byte))

theorem Image.InAllocation.of_allocations {image : Image size} {owner : OwnerId} {state next : State}
    (represented : image.InAllocation owner state) (unchanged : next.allocations = state.allocations) :
    image.InAllocation owner next := by
  refine ⟨?_, fun byte => ?_⟩
  · simpa [State.resources_extent, State.allocation, unchanged] using represented.1
  · simpa [State.byte, State.allocation, unchanged] using represented.2 byte

theorem Image.inAllocation_of_alloc {image : Image size} {owner : OwnerId} {state next : State}
    (allocated : Step state (.alloc owner image.toBytes) next) : image.InAllocation owner next := by
  cases allocated
  refine ⟨?_, fun byte => ?_⟩
  · simp [State.resources_extent, State.allocation, State.addAllocation, Image.toBytes]
  · simp [State.byte, State.allocation, State.addAllocation, Image.toBytes, bind, byte.isLt]

private theorem Image.inAllocation_unique {a b : Image size} {owner : OwnerId} {state : State}
    (first : a.InAllocation owner state)
    (second : ∀ byte : Fin size, state.byte ⟨owner, byte.val⟩ = some (UInt8.ofBitVec (b byte))) :
    a = b := by
  funext byte
  have same := Option.some.inj ((first.2 byte).symm.trans (second byte))
  exact congrArg UInt8.toBitVec same

private theorem recordImage_of_inAllocation {image : Image size} {owner : OwnerId} {state : State}
    (represented : image.InAllocation owner state) : recordImage state owner size = some image := by
  have extent := represented.1
  rw [State.resources_extent] at extent
  obtain ⟨allocation, found, length⟩ := Option.map_eq_some_iff.mp extent
  have opened : recordImage state owner size = some (length ▸ Image.ofBytes allocation.bytes) := by
    simp [recordImage, found, bind, length]
  rw [opened, Image.inAllocation_unique represented (recordImage_byte opened)]

theorem PackedValueField.mergeTrace_samples (field : PackedValueField size width)
    {state : State} {owner : OwnerId} {targets : List AccessTarget} {image : Image size}
    (allowed : AccessAllowed state owner .exclusive field.byteOffsets targets)
    (represented : image.InAllocation owner state) :
    (∀ op ∈ field.mergeTrace targets, ∃ location, op.byteAccess state.resources = some (.read location)) ∧
    (field.mergeTrace targets).mapM (Instruction.readSample state) = some (image.bytesAt field.mergeOffsets) := by
  have decoded := field.mergeTrace_byteAccesses allowed
  constructor
  · intro op member
    obtain ⟨access, inAccesses, resolved⟩ := mapM_member decoded member
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp inAccesses
    exact ⟨_, resolved⟩
  · rw [Program.readSamples_of_byteAccesses state decoded, List.mapM_map]
    let sample : Nat → BitVec 8 := fun offset => if fits : offset < size then image ⟨offset, fits⟩ else 0
    rw [show image.bytesAt field.mergeOffsets = field.mergeOffsets.map sample from rfl,
      ← show field.mergeOffsets.mapM (pure <| sample ·) = some (field.mergeOffsets.map sample) from
        List.mapM_pure (m := Option)]
    apply mapM_eq_of_mem
    intro offset member
    have fits := field.byteOffset_inBounds (List.mem_filter.mp member).1
    simpa [sample, fits, ByteAccess.readSample, Function.comp_def] using
      congrArg (Option.map UInt8.toBitVec) (represented.2 ⟨offset, fits⟩)

theorem PackedValueField.writeProgram_eq_fromSamples (field : PackedValueField size width)
    (codec : PackedCodec α width) {state : State} {owner : OwnerId}
    {targets : List AccessTarget} {image : Image size} {value : α} {samples : List (BitVec 8)}
    (represented : image.InAllocation owner state) (observed : samples = image.bytesAt field.mergeOffsets) :
    field.writeProgram codec state owner targets value =
      (field.writeInstructionsFromSamples codec owner targets value samples).map (field.mergeTrace targets ++ ·) := by
  have patch := field.patch_eq_of_mergeBytes owner codec (sampleImage field (image.bytesAt field.mergeOffsets))
    image value sampleImage_agrees
  have count : (image.bytesAt field.mergeOffsets).length = field.mergeOffsets.length := by simp [Image.bytesAt]
  simp [writeProgram, recordImage_of_inAllocation represented, storeInstructions, writeInstructionsFromSamples,
    writeInstructions, observed, count, patch]

private theorem recordImage_inAllocation {image : Image size} {owner : OwnerId} {state : State}
    (opened : recordImage state owner size = some image) : image.InAllocation owner state := by
  refine ⟨?_, recordImage_byte opened⟩
  obtain ⟨allocation, located, _⟩ := Option.bind_eq_some_iff.mp opened
  by_cases same : allocation.bytes.length = size
  · simp [State.resources_extent, located, same]
  · simp [recordImage, located, same] at opened

theorem PackedValueField.writeProgram_sampling (field : PackedValueField size width)
    (codec : PackedCodec α width) {state next : State} {owner : OwnerId}
    {targets : List AccessTarget} {value : α} {program : Program}
    (ran : field.writeMachine codec state owner targets value = some next)
    (compiled : field.writeProgram codec state owner targets value = some program) :
    ∃ samples writes, program = field.mergeTrace targets ++ writes ∧
      (∀ op ∈ field.mergeTrace targets, ∃ location, op.byteAccess state.resources = some (.read location)) ∧
      (∀ op ∈ writes, ∃ location byte, op.byteAccess state.resources = some (.write location byte)) ∧
      (field.mergeTrace targets).mapM (Instruction.readSample state) = some samples ∧
      field.writeInstructionsFromSamples codec owner targets value samples = some writes := by
  obtain ⟨allowed, image, opened, _⟩ := field.writeMachine_refines codec ran
  have represented := recordImage_inAllocation opened
  obtain ⟨readable, snapshot⟩ := field.mergeTrace_samples allowed represented
  have rebuilt := field.writeProgram_eq_fromSamples codec (targets := targets) (value := value) represented rfl
  obtain ⟨writes, ready, same⟩ := Option.map_eq_some_iff.mp (rebuilt.symm.trans compiled)
  refine ⟨_, writes, same.symm, readable, ?_, snapshot, ready⟩
  intro op member
  have count : (image.bytesAt field.mergeOffsets).length = field.mergeOffsets.length := by simp [Image.bytesAt]
  rw [writeInstructionsFromSamples, ite_eq_left count] at ready
  have isWrites := (Option.some.inj ready).symm
  rw [isWrites] at member
  obtain ⟨access, inAccesses, resolved⟩ := mapM_member
    (field.writeInstructions_byteAccesses codec _ value allowed) member
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp inAccesses
  exact ⟨_, _, resolved⟩

theorem PackedValueField.readMachine_on_image (field : PackedValueField size width)
    (codec : PackedCodec α width) {state : State} {owner : OwnerId}
    {targets : List AccessTarget} {image : Image size} {value : α}
    (represented : image.InAllocation owner state)
    (ran : field.readMachine codec state owner targets = some value) :
    field.load codec image = some value := by
  obtain ⟨_, _, _, opened, loaded⟩ := field.readMachine_refines codec ran
  rw [Image.inAllocation_unique represented (recordImage_byte opened)]
  exact loaded

theorem PackedValueField.writeMachine_on_image (field : PackedValueField size width)
    (codec : PackedCodec α width) {state next : State} {owner : OwnerId}
    {targets : List AccessTarget} {image : Image size} {value : α}
    (represented : image.InAllocation owner state)
    (ran : field.writeMachine codec state owner targets value = some next) :
    (field.store codec image value).InAllocation owner next := by
  obtain ⟨_, _, opened, _, sameResources, result⟩ := field.writeMachine_refines codec ran
  rw [Image.inAllocation_unique represented (recordImage_byte opened)]
  exact ⟨sameResources ▸ represented.1, result⟩

theorem PackedValueField.writeMachine_preserves_resources (field : PackedValueField size width)
    (codec : PackedCodec α width) {state next : State} {owner : OwnerId}
    {targets : List AccessTarget} {value : α}
    (ran : field.writeMachine codec state owner targets value = some next) :
    next.resources = state.resources := by
  obtain ⟨_, _, _, _, preserved, _⟩ := field.writeMachine_refines codec ran
  exact preserved

theorem PackedValueField.readMachine_transfer (field : PackedValueField size width)
    (codec : PackedCodec α width) {state next : State} {owner : OwnerId}
    {targets : List AccessTarget} {image : Image size} {oldValue value : α}
    (ran : field.readMachine codec state owner targets = some oldValue)
    (same : next.resources = state.resources) (represented : image.InAllocation owner next)
    (loaded : field.load codec image = some value) :
    field.readMachine codec next owner targets = some value := by
  have allowed := (field.readMachine_authorized codec ran).of_resources same
  obtain ⟨_, _, reads, _, _⟩ := field.readMachine_refines codec ran
  obtain ⟨_, ranReads⟩ := run_of_resources same (run_complete reads)
  have opened := recordImage_of_inAllocation represented
  have bytes := observedBytes_eq_image allowed.1 (fun pair member => (allowed.2 pair member).1)
    (fun _ member => field.byteOffset_inBounds member) opened (run_sound ranReads)
  simp [readMachine, (checkAccessTargets_correct _ _ _ _ _).mpr allowed, bind, ranReads, opened, bytes]
  exact loaded

theorem PackedValueField.writeMachine_transfer (field : PackedValueField size width)
    (codec : PackedCodec α width) {state next final : State} {owner : OwnerId}
    {targets : List AccessTarget} {after : Image size} {value : α}
    (ran : field.writeMachine codec state owner targets value = some final)
    (same : next.resources = state.resources) (newImage : after.InAllocation owner next) :
    ∃ result, field.writeMachine codec next owner targets value = some result := by
  simp only [writeMachine, Option.ite_none_right_eq_some, checkAccessTargets_correct, bind,
    Option.bind_eq_some_iff] at ran
  obtain ⟨allowed, _, _, observed, reading, storing⟩ := ran
  have compare := allowed.of_resources same
  obtain ⟨other, reads⟩ := run_of_resources same reading
  have oldReads := runReadTrace_only_observes (run_sound reading)
  have newReads := runReadTrace_only_observes (run_sound reads)
  have readResources : other.resources = observed.resources := by
    rw [newReads, oldReads]
    exact same
  have locations := (field.patch_locations owner codec (mergeImage field other targets) value).trans
    (field.patch_locations owner codec (mergeImage field observed targets) value).symm
  obtain ⟨result, stored⟩ := runPackedStores_of_resources readResources locations storing
  exact ⟨result, by simp [writeMachine, (checkAccessTargets_correct _ _ _ _ _).mpr compare,
    bind, recordImage_of_inAllocation newImage, reads, stored]⟩

end Aethel.AutomaticLayout
