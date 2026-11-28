import Aethel.PackedRecord
import Aethel.PackedTarget
import Aethel.PackedFork
import Aethel.SourceForkJoin
import Lean.Elab.Deriving.FromToJson

namespace Aethel.PackedMIR

open Lean AutomaticLayout ScopedForkJoin

def version : Nat := 2

local instance : ToJson IntegerWidth := ⟨fun width => toJson width.bits⟩

local instance : FromJson IntegerWidth where
  fromJson? input := do
    let bits : Nat ← fromJson? input
    match IntegerWidth.ofNat? bits with
    | some width => return width
    | none => throw s!"invalid integer bit width {bits}"

deriving instance ToJson, FromJson for StoragePolicy
deriving instance ToJson, FromJson for IntegerSlot
deriving instance ToJson, FromJson for PackedType
deriving instance ToJson, FromJson for PackedType.FieldStep
deriving instance ToJson, FromJson for PackedSchema
deriving instance ToJson, FromJson for Core.AccessMode

structure PlacementClaim where
  path : List Nat
  byteOffset : Nat
  bitOffset : Option Nat
  width : Nat
  byteCount : Nat
  deriving Repr, DecidableEq, ToJson, FromJson

structure LayoutClaim where
  byteCount : Nat
  alignment : Nat
  fields : List PlacementClaim
  deriving Repr, DecidableEq, ToJson, FromJson

structure TargetClaim where
  base : Nat := 0
  limit : Nat := 2^64 - 1
  deriving Repr, ToJson, FromJson

def TargetClaim.region (target : TargetClaim) (layout : Layout) : PackedArrayRegion layout :=
  ⟨target.base, 1, target.limit⟩

private def describeField (record : PackedRecord abi schema) (path : { path // path ∈ schema.paths }) :
    PlacementClaim :=
  let resolved := (AutomaticLayout.resolve record.layout path.val).get (by
    obtain ⟨ty, declared⟩ := PackedSchema.typeAt_of_mem_paths path.property
    obtain ⟨placement, slot, found⟩ := record.resolve_leaf declared
    simp [found])
  ⟨path.val, resolved.1.byteOffset, resolved.1.bitOffset, resolved.2.bits, Field.bytes resolved⟩

def describe (record : PackedRecord abi schema) : LayoutClaim :=
  ⟨record.layout.size, record.layout.alignment, schema.paths.attach.map (describeField record)⟩

def PlacementClaim.Describes (claim : PlacementClaim) (record : PackedRecord abi schema) : Prop :=
  ∃ ty placement slot, schema.typeAt claim.path = some ty ∧
    AutomaticLayout.resolve record.layout claim.path = some (placement, .fixed ty.width slot) ∧
    claim.byteOffset = placement.byteOffset ∧ claim.bitOffset = placement.bitOffset ∧
    claim.width = ty.width ∧ claim.byteCount = Field.bytes (placement, .fixed ty.width slot)

def LayoutClaim.Describes (claim : LayoutClaim) (record : PackedRecord abi schema) : Prop :=
  claim.byteCount = record.layout.size ∧ claim.alignment = record.layout.alignment ∧
    claim.fields.map PlacementClaim.path = schema.paths ∧
    ∀ field ∈ claim.fields, field.Describes record

private theorem describeField_correct (record : PackedRecord abi schema) (path : { path // path ∈ schema.paths }) :
    (describeField record path).Describes record := by
  obtain ⟨ty, declared⟩ := PackedSchema.typeAt_of_mem_paths path.property
  obtain ⟨placement, slot, found⟩ := record.resolve_leaf declared
  have resolved : ∀ h, (AutomaticLayout.resolve record.layout path.val).get h =
      (placement, Layout.fixed ty.width slot) := by
    intro valid
    exact Option.get_of_eq_some valid found
  have claim : describeField record path =
      ⟨path.val, placement.byteOffset, placement.bitOffset, ty.width,
        Field.bytes (placement, Layout.fixed ty.width slot)⟩ := by
    simp [describeField, resolved, Layout.bits]
  rw [claim]
  exact ⟨ty, placement, slot, declared, found, rfl, rfl, rfl, rfl⟩

theorem describe_sound (record : PackedRecord abi schema) : (describe record).Describes record := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · change (schema.paths.attach.map (describeField record)).map PlacementClaim.path = _
    rw [List.map_map]
    exact List.attach_map_subtype_val _
  · intro field member
    obtain ⟨path, _, rfl⟩ := List.mem_map.mp member
    exact describeField_correct record path

private theorem PlacementClaim.Describes.unique {record : PackedRecord abi schema} {left right : PlacementClaim}
    (first : left.Describes record) (second : right.Describes record) (path : left.path = right.path) :
    left = right := by
  obtain ⟨ty, place, slot, declared, resolved, byte, bit, width, size⟩ := first
  obtain ⟨otherTy, otherPlace, otherSlot, otherType, otherResolved, otherByte, otherBit, otherWidth, otherSize⟩ := second
  rw [← path, declared] at otherType
  cases otherType
  rw [← path, resolved] at otherResolved
  cases otherResolved
  cases left
  cases right
  simp_all

theorem describe_correct (record : PackedRecord abi schema) (claim : LayoutClaim) :
    describe record = claim ↔ claim.Describes record := by
  constructor
  · rintro rfl
    exact describe_sound record
  · intro valid
    obtain ⟨bytes, alignment, paths, fields⟩ := valid
    have canonical := describe_sound record
    have equalPaths := canonical.2.2.1.trans paths.symm
    have lengths := congrArg List.length equalPaths
    simp only [List.length_map] at lengths
    have equalFields : (describe record).fields = claim.fields := by
      apply List.ext_getElem lengths
      intro index inCanonical inClaim
      have path : (describe record).fields[index].path = claim.fields[index].path := by
        have equal := congrArg (fun xs : List (List Nat) => xs[index]?) equalPaths
        simpa [List.getElem?_eq_getElem inCanonical, List.getElem?_eq_getElem inClaim] using equal
      exact PlacementClaim.Describes.unique (canonical.2.2.2 _ (List.getElem_mem _))
        (fields _ (List.getElem_mem _)) path
    cases claim
    simpa [describe] using And.intro bytes.symm (And.intro alignment.symm equalFields)

structure Task where
  path : List Nat
  bytes : List Nat
  code : Option Nat := none
  deriving Repr, ToJson, FromJson

inductive Op where
  | openScope (id : Nat) (path : List Nat) (mode : Core.AccessMode)
  | reborrow (id parent : Nat) (path : List Nat) (mode : Core.AccessMode)
  | closeScope (id : Nat)
  | load (scope : Nat) (path bytes : List Nat)
  | store (scope : Nat) (path bytes : List Nat) (code : Nat)
  | capturePayload (scope id : Nat) (path bytes : List Nat)
  | loadPayload (scope id : Nat) (bytes : List Nat)
  | loadPayloadField (scope id tag : Nat) (steps : List PackedType.FieldStep) (bytes : List Nat)
  | forgetPayload (id : Nat)
  | fork (scope : Nat) (tasks : List Task)
  deriving Repr, ToJson, FromJson

structure Module where
  version : Nat
  schema : PackedSchema
  layout : LayoutClaim
  target : TargetClaim := {}
  initial : List (List Nat × Nat)
  operations : List Op
  deriving Repr, ToJson, FromJson

def Module.initialValue (mir : Module) (path : List Nat) : Option Nat :=
  (mir.initial.find? fun entry => entry.1 == path).map Prod.snd

theorem Module.initial_allocates (mir : Module) (record : PackedRecord abi mir.schema)
    (paths : mir.initial.map Prod.fst = mir.schema.paths)
    (typed : ∀ entry ∈ mir.initial, ∃ ty, mir.schema.typeAt entry.1 = some ty ∧
      entry.2 < 2 ^ ty.width ∧ ty.Represents entry.2) :
    ∃ memory, record.allocate {} mir.initialValue = some memory := by
  apply record.allocate_complete {} mir.initialValue (by simp)
  intro path ty declared
  cases found : mir.initial.find? (fun entry => entry.1 == path) with
  | none =>
    obtain ⟨entry, member, equal⟩ := List.mem_map.mp (paths ▸ PackedSchema.mem_paths declared)
    have absent := List.find?_eq_none.mp found entry member
    simp [equal] at absent
  | some entry =>
    have equal : entry.1 = path := by simpa using List.find?_some found
    obtain ⟨actual, resolved, fits, valid⟩ := typed entry (List.mem_of_find?_eq_some found)
    rw [equal, declared] at resolved
    cases resolved
    exact ⟨entry.2, by simp [Module.initialValue, found], fits, valid⟩

structure Execution (record : PackedRecord abi schema) where
  memory : record.Memory
  payloads : List (Nat × record.PayloadRef) := []
  observations : List Nat := []

def Execution.payload? {record : PackedRecord abi schema} (state : Execution record) (id : Nat) :
    Option record.PayloadRef :=
  (state.payloads.find? fun entry => entry.1 == id).map Prod.snd

/-- For every successful typed operation the claimed bytes are the exact span
derived from its resolved field. -/
def FootprintClaim (record : PackedRecord abi schema) (path bytes : List Nat) : Prop :=
  ∃ field, record.field path = some field ∧ bytes = field.2.byteOffsets

def checkFootprint (record : PackedRecord abi schema) (path bytes : List Nat) : Bool :=
  (record.field path).any fun field => bytes == field.2.byteOffsets

theorem checkFootprint_correct (record : PackedRecord abi schema) (path bytes : List Nat) :
    checkFootprint record path bytes = true ↔ FootprintClaim record path bytes := by
  cases found : record.field path <;> simp [checkFootprint, FootprintClaim, found]

def Task.resolve (task : Task) (record : PackedRecord abi schema) :
    Option (PackedForkAction record.layout.size) := do
  let ⟨ty, field⟩ ← record.field task.path
  if task.bytes = field.byteOffsets then
    match task.code with
    | none => some (.load ty field)
    | some code => return .store ty field (← ty.decodeCode code)
  else none

inductive Task.Resolves (record : PackedRecord abi schema) :
    Task → PackedForkAction record.layout.size → Prop where
  | load {path : List Nat} {ty : PackedType} {field : PackedValueField record.layout.size ty.width}
      (found : record.field path = some ⟨ty, field⟩) :
    Resolves record ⟨path, field.byteOffsets, none⟩ (.load ty field)
  | store {path : List Nat} {code : Nat} {ty : PackedType}
      {field : PackedValueField record.layout.size ty.width} {value : ty.Value}
      (found : record.field path = some ⟨ty, field⟩) (decoded : ty.decodeCode code = some value) :
    Resolves record ⟨path, field.byteOffsets, some code⟩ (.store ty field value)

theorem Task.resolve_sound {record : PackedRecord abi schema} {task : Task}
    {action : PackedForkAction record.layout.size} (resolved : task.resolve record = some action) :
    task.Resolves record action := by
  obtain ⟨path, bytes, code⟩ := task
  simp only [Task.resolve, bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some] at resolved
  obtain ⟨⟨ty, field⟩, found, sameBytes, selected⟩ := resolved
  subst bytes
  cases code with
  | none =>
    cases selected
    exact .load found
  | some _ =>
    obtain ⟨value, decoded, equal⟩ := Option.bind_eq_some_iff.mp selected
    change some (.store ty field value) = some action at equal
    cases equal
    exact .store found decoded

private theorem Task.Resolves.complete {record : PackedRecord abi schema} {task : Task}
    {action : PackedForkAction record.layout.size} (resolved : task.Resolves record action) :
    task.resolve record = some action := by
  cases resolved with
  | load found => simp [Task.resolve, found, bind]
  | store found decoded => simp [Task.resolve, found, decoded, bind, pure]

inductive CoversFork {record : PackedRecord abi schema} :
    List Task → List (PackedForkAction record.layout.size) → Prop where
  | nil : CoversFork [] []
  | cons : task.Resolves record action → CoversFork tasks actions →
      CoversFork (task :: tasks) (action :: actions)

private theorem CoversFork.permute {record : PackedRecord abi schema} {tasks schedule : List Task}
    {actions : List (PackedForkAction record.layout.size)}
    (covered : CoversFork (record := record) tasks actions) (perm : tasks.Perm schedule) :
    ∃ scheduled, CoversFork (record := record) schedule scheduled ∧ actions.Perm scheduled ∧
      (tasks.zip actions).Perm (schedule.zip scheduled) := by
  induction perm generalizing actions with
  | nil => cases covered; exact ⟨[], .nil, .nil, .nil⟩
  | cons _ _ ih =>
    cases covered with
    | cons resolved rest =>
      obtain ⟨scheduled, correspondence, reordered, paired⟩ := ih rest
      exact ⟨_ :: scheduled, .cons resolved correspondence, .cons _ reordered, .cons _ paired⟩
  | swap _ _ _ =>
    cases covered with
    | cons first rest =>
      cases rest with
      | cons second rest => exact ⟨_, .cons second (.cons first rest), .swap .., .swap ..⟩
  | trans _ _ first second =>
    obtain ⟨_, middle, left, pairedLeft⟩ := first covered
    obtain ⟨scheduled, correspondence, right, pairedRight⟩ := second middle
    exact ⟨scheduled, correspondence, left.trans right, pairedLeft.trans pairedRight⟩

def ForkValid (record : PackedRecord abi schema) (tasks : List Task) : Prop :=
  ∃ actions, CoversFork (record := record) tasks actions ∧
    actions.Pairwise (fun a b => ForkDisjoint (a.footprint record.owner) (b.footprint record.owner))

def checkFork (record : PackedRecord abi schema) (tasks : List Task) : Bool :=
  (tasks.mapM (fun task : Task => task.resolve record)).any fun actions =>
    decide (actions.Pairwise (fun a b => checkForkDisjoint
      (a.footprint record.owner) (b.footprint record.owner) = true))

private theorem coversFork_sound {record : PackedRecord abi schema} {tasks : List Task}
    {actions : List (PackedForkAction record.layout.size)}
    (walked : tasks.mapM (fun task => task.resolve record) = some actions) :
    CoversFork (record := record) tasks actions := by
  induction tasks generalizing actions with
  | nil => cases walked; exact .nil
  | cons task rest ih =>
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at walked
    obtain ⟨_, first, _, remaining, rfl⟩ := walked
    exact .cons (Task.resolve_sound first) (ih remaining)

theorem checkFork_sound (record : PackedRecord abi schema) (tasks : List Task)
    (safe : checkFork record tasks = true) : ForkValid record tasks := by
  unfold checkFork at safe
  cases found : tasks.mapM (fun task => task.resolve record) with
  | none => simp [found] at safe
  | some actions =>
    rw [found] at safe
    have checked : actions.Pairwise (fun a b =>
        checkForkDisjoint (a.footprint record.owner) (b.footprint record.owner) = true) :=
      of_decide_eq_true safe
    exact ⟨actions, coversFork_sound found,
      checked.imp (fun h => (checkForkDisjoint_correct _ _).mp h)⟩

theorem checkFork_complete (record : PackedRecord abi schema) (tasks : List Task)
    (safe : ForkValid record tasks) : checkFork record tasks = true := by
  obtain ⟨actions, covered, independent⟩ := safe
  have resolved : tasks.mapM (fun task : Task => task.resolve record) = some actions := by
    induction covered with
    | nil => rfl
    | cons first _ ih =>
      simp [List.mapM_cons, first.complete, ih (List.pairwise_cons.mp independent).2, bind, pure]
  unfold checkFork
  rw [resolved]
  exact decide_eq_true (independent.imp (fun h => (checkForkDisjoint_correct _ _).mpr h))

def Task.execute {record : PackedRecord abi schema} (scope : Nat) (state : Execution record)
    (task : Task) : Option (Execution record) := do
  match task.code with
  | none =>
    let value ← state.memory.readInScope scope task.path
    return { state with observations := value :: state.observations }
  | some code =>
    let memory ← state.memory.writeInScope scope task.path code
    return { state with memory }

inductive Task.Step {record : PackedRecord abi schema} (scope : Nat) (state : Execution record) :
    Task → Execution record → Prop where
  | load {path bytes : List Nat} (read : state.memory.readInScope scope path = some value) :
      Step scope state ⟨path, bytes, none⟩ { state with observations := value :: state.observations }
  | store {path bytes : List Nat} {code : Nat}
      (written : state.memory.writeInScope scope path code = some memory) :
      Step scope state ⟨path, bytes, some code⟩ { state with memory }

inductive RunsTasks {record : PackedRecord abi schema} (scope : Nat) :
    Execution record → List Task → Execution record → Prop where
  | nil : RunsTasks scope state [] state
  | cons : Task.Step scope state task next → RunsTasks scope next tasks final →
      RunsTasks scope state (task :: tasks) final

private theorem Task.Step.preserves_authority {record : PackedRecord abi schema}
    {state next : Execution record} {scope : Nat} {task : Task}
    (step : Task.Step scope state task next) : next.memory.authority = state.memory.authority := by
  cases step with
  | load _ => rfl
  | store written => exact PackedRecord.Memory.writeInScope_preserves_authority written

private theorem Task.Resolves.readImage_eq_result {record : PackedRecord abi schema}
    {path bytes : List Nat} {action : PackedForkAction record.layout.size}
    (resolved : Resolves record ⟨path, bytes, none⟩ action) (image : Image record.layout.size) :
    record.readImage image path = action.result image := by
  cases resolved with
  | @load _ ty field found =>
    cases loaded : field.load ty.codec image <;>
      simp [PackedRecord.readImage, PackedForkAction.result, found, loaded, bind]

private theorem Task.Step.transfer {record : PackedRecord abi schema}
    {state next other : Execution record} {scope : Nat} {task : Task}
    {action : PackedForkAction record.layout.size} {before image : Image record.layout.size}
    (step : Task.Step scope state task next) (resolved : task.Resolves record action)
    (represented : before.InAllocation record.owner state.memory.heap)
    (same : other.memory.authority = state.memory.authority)
    (current : image.InAllocation record.owner other.memory.heap)
    (unchanged : action.result image = action.result before) :
    ∃ updated, Task.Step scope other task updated := by
  cases step with
  | load read =>
    have loaded := state.memory.readInScope_on_image represented read
    rw [resolved.readImage_eq_result] at loaded
    have currentLoaded := (resolved.readImage_eq_result image).trans (unchanged.trans loaded)
    exact ⟨_, .load (PackedRecord.Memory.readInScope_transfer same read current currentLoaded)⟩
  | store written =>
    obtain ⟨_, stored⟩ := PackedRecord.Memory.writeInScope_transfer same written current
    exact ⟨_, .store stored⟩

private theorem Task.Step.on_image {record : PackedRecord abi schema}
    {state next : Execution record} {scope : Nat} {task : Task}
    {action : PackedForkAction record.layout.size} {before : Image record.layout.size}
    (step : Task.Step scope state task next) (resolved : task.Resolves record action)
    (represented : before.InAllocation record.owner state.memory.heap) :
    (action.apply before).InAllocation record.owner next.memory.heap ∧
      next.observations = (action.result before).toList ++ state.observations := by
  cases resolved with
  | @load path ty field found =>
    cases step with
    | load read =>
      have observed := state.memory.readInScope_on_image represented read
      refine ⟨represented, ?_⟩
      cases loaded : field.load ty.codec before <;>
        simp_all [PackedRecord.readImage, PackedForkAction.result, bind, pure, Option.map]
  | @store path code ty field value found decoded =>
    cases step with
    | store written =>
      obtain ⟨after, applied, stored⟩ := state.memory.writeInScope_on_image represented written
      have plan : record.writeImage before path code = some (field.store ty.codec before value) := by
        simp [PackedRecord.writeImage, found, decoded, bind]
      rw [plan] at applied
      cases applied
      exact ⟨stored, rfl⟩

private def ReadyTasks {record : PackedRecord abi schema} (scope : Nat) (state : Execution record)
    (before : Image record.layout.size) (entries : List (Task × PackedForkAction record.layout.size)) : Prop :=
  ∀ entry ∈ entries, ∀ (other : Execution record) (image : Image record.layout.size),
    other.memory.authority = state.memory.authority → image.InAllocation record.owner other.memory.heap →
    entry.2.result image = entry.2.result before → ∃ updated, Task.Step scope other entry.1 updated

private theorem RunsTasks.ready {record : PackedRecord abi schema} {scope : Nat} {tasks : List Task}
    {state final : Execution record} {before : Image record.layout.size}
    {actions : List (PackedForkAction record.layout.size)}
    (ran : RunsTasks scope state tasks final) (covered : CoversFork (record := record) tasks actions)
    (compatible : actions.Pairwise (fun a b => ForkDisjoint (a.footprint record.owner) (b.footprint record.owner)))
    (represented : before.InAllocation record.owner state.memory.heap) :
    ReadyTasks scope state before (tasks.zip actions) := by
  induction ran generalizing actions before with
  | nil =>
    cases covered
    simp [ReadyTasks]
  | cons first _ ih =>
    cases covered with
    | cons resolved rest =>
      obtain ⟨head, safeTail⟩ := List.pairwise_cons.mp compatible
      have advanced := (first.on_image resolved represented).1
      intro entry member other image same valid result
      simp only [List.zip_cons_cons, List.mem_cons] at member
      rcases member with rfl | inTail
      · exact first.transfer resolved represented same valid result
      · have independent := forkDisjoint_symm (head entry.2 (List.of_mem_zip inTail).2)
        have stable := PackedForkAction.result_stable independent before
        exact ih rest safeTail advanced entry inTail other image
          (same.trans first.preserves_authority.symm) valid (result.trans stable.symm)

private theorem ReadyTasks.run {record : PackedRecord abi schema} {scope : Nat} {tasks : List Task}
    {state : Execution record} {before : Image record.layout.size}
    {actions : List (PackedForkAction record.layout.size)}
    (ready : ReadyTasks scope state before (tasks.zip actions))
    (covered : CoversFork (record := record) tasks actions)
    (compatible : actions.Pairwise (fun a b => ForkDisjoint (a.footprint record.owner) (b.footprint record.owner)))
    (represented : before.InAllocation record.owner state.memory.heap) :
    ∃ final, RunsTasks scope state tasks final := by
  induction covered generalizing state before with
  | nil => exact ⟨state, .nil⟩
  | cons resolved _ ih =>
    obtain ⟨head, safeTail⟩ := List.pairwise_cons.mp compatible
    rw [List.zip_cons_cons] at ready
    obtain ⟨updated, first⟩ := ready _ List.mem_cons_self state before rfl represented rfl
    have advanced := (first.on_image resolved represented).1
    obtain ⟨final, rest⟩ := ih (state := updated) (before := _) (by
      intro entry member other image same valid result
      have independent := forkDisjoint_symm (head entry.2 (List.of_mem_zip member).2)
      have stable := PackedForkAction.result_stable independent before
      exact ready entry (List.mem_cons_of_mem _ member) other image
        (same.trans first.preserves_authority) valid (result.trans stable)) safeTail advanced
    exact ⟨final, .cons first rest⟩

theorem RunsTasks.permute {record : PackedRecord abi schema} {scope : Nat} {tasks schedule : List Task}
    {state final : Execution record} {before : Image record.layout.size}
    {actions : List (PackedForkAction record.layout.size)}
    (ran : RunsTasks scope state tasks final) (covered : CoversFork (record := record) tasks actions)
    (compatible : actions.Pairwise (fun a b => ForkDisjoint (a.footprint record.owner) (b.footprint record.owner)))
    (represented : before.InAllocation record.owner state.memory.heap) (perm : tasks.Perm schedule) :
    ∃ scheduled final, CoversFork (record := record) schedule scheduled ∧ actions.Perm scheduled ∧
      RunsTasks scope state schedule final := by
  obtain ⟨scheduled, corresponds, reordered, paired⟩ := covered.permute perm
  have ready := ran.ready covered compatible represented
  have readySchedule : ReadyTasks scope state before (schedule.zip scheduled) :=
    fun entry member => ready entry (paired.mem_iff.mpr member)
  obtain ⟨final, runs⟩ := readySchedule.run corresponds
    (compatible.perm reordered (fun h => forkDisjoint_symm h)) represented
  exact ⟨scheduled, final, corresponds, reordered, runs⟩

private theorem RunsTasks.preserves_scope {record : PackedRecord abi schema} {scope : Nat}
    {state final : Execution record} {tasks : List Task} (ran : RunsTasks scope state tasks final) :
    final.memory.authority = state.memory.authority ∧ final.payloads = state.payloads := by
  induction ran with
  | nil => exact ⟨rfl, rfl⟩
  | cons step _ ih =>
    refine ⟨ih.1.trans step.preserves_authority, ?_⟩
    cases step <;> exact ih.2

private def Task.writesPath (key : List Nat) (task : Task) : Bool :=
  task.code.isSome && decide (key = task.path)

theorem RunsTasks.generation {record : PackedRecord abi schema} {scope : Nat}
    {state final : Execution record} {tasks : List Task} (ran : RunsTasks scope state tasks final)
    (key : List Nat) :
    final.memory.generation key = state.memory.generation key + tasks.countP (Task.writesPath key) := by
  induction ran with
  | nil => simp
  | cons step _ ih =>
    rw [ih, List.countP_cons]
    cases step with
    | load read => simp [Task.writesPath]
    | store written =>
      rw [PackedRecord.Memory.writeInScope_generation written key]
      simp only [Task.writesPath, Option.isSome_some, Bool.true_and, decide_eq_true_eq]
      omega

private theorem Task.Step.execute_complete {record : PackedRecord abi schema} {scope : Nat}
    {state next : Execution record} {task : Task} (step : Task.Step scope state task next) :
    task.execute scope state = some next := by
  cases step with
  | load read => simp [Task.execute, bind, pure, read]
  | store written => simp [Task.execute, bind, pure, written]

theorem runTasks_complete {record : PackedRecord abi schema} {scope : Nat} {tasks : List Task}
    {state final : Execution record} (ran : RunsTasks scope state tasks final) :
    tasks.foldlM (Task.execute scope) state = some final := by
  induction ran with
  | nil => rfl
  | cons step _ ih => simpa [List.foldlM_cons, bind, step.execute_complete] using ih

theorem RunsTasks.on_image {record : PackedRecord abi schema} {scope : Nat} {tasks : List Task}
    {state final : Execution record} {before : Image record.layout.size}
    {actions : List (PackedForkAction record.layout.size)}
    (ran : RunsTasks scope state tasks final) (covered : CoversFork (record := record) tasks actions)
    (represented : before.InAllocation record.owner state.memory.heap) :
    (applyPackedSchedule actions before).InAllocation record.owner final.memory.heap ∧
      final.observations = ((observePackedSchedule actions before).flatMap Option.toList).reverse ++
        state.observations := by
  induction ran generalizing actions before with
  | nil =>
    cases covered
    exact ⟨represented, rfl⟩
  | cons first _ ih =>
    cases covered with
    | cons resolved rest =>
      obtain ⟨advanced, observation⟩ := first.on_image resolved represented
      obtain ⟨stored, observed⟩ := ih rest advanced
      have reverseResult (result : Option Nat) : result.toList.reverse = result.toList := by
        cases result <;> rfl
      exact ⟨stored, by simpa [observePackedSchedule, observation, List.reverse_append,
        List.append_assoc, reverseResult] using observed⟩

theorem runTasks_sound {record : PackedRecord abi schema} {scope : Nat} {tasks : List Task}
    {state final : Execution record} (ran : tasks.foldlM (Task.execute scope) state = some final) :
    RunsTasks scope state tasks final := by
  induction tasks generalizing state with
  | nil => cases ran; exact .nil
  | cons task tasks ih =>
    obtain ⟨next, first, suffix⟩ := Option.bind_eq_some_iff.mp ran
    refine .cons ?_ (ih suffix)
    obtain ⟨path, bytes, code⟩ := task
    cases code <;> simp only [Task.execute, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at first
    · obtain ⟨_, read, rfl⟩ := first
      exact .load read
    · obtain ⟨_, written, rfl⟩ := first
      exact .store written

private def Execution.observePayload {record : PackedRecord abi schema} (state : Execution record)
    (id : Nat) (bytes : List Nat) (read : record.PayloadRef → Option Nat) : Option (Execution record) := do
  let payload ← state.payload? id
  if checkFootprint record payload.path bytes then
    let value ← read payload
    return { state with observations := value :: state.observations }
  else none

def Op.execute {record : PackedRecord abi schema} (state : Execution record) :
    Op → Option (Execution record)
  | .openScope id path mode => do
    let (opened, memory) ← state.memory.openScope path mode
    if opened = id then some { state with memory } else none
  | .reborrow id parent path mode => do
    let (opened, memory) ← state.memory.reborrowScope parent path mode
    if opened = id then some { state with memory } else none
  | .closeScope id => do
    let memory ← state.memory.closeScope id
    return { state with memory }
  | .load scope path bytes => do
    if checkFootprint record path bytes then
      let value ← state.memory.readInScope scope path
      return { state with observations := value :: state.observations }
    else none
  | .store scope path bytes code => do
    if checkFootprint record path bytes then
      let memory ← state.memory.writeInScope scope path code
      return { state with memory }
    else none
  | .capturePayload scope id path bytes => do
    if (state.payload? id).isNone && checkFootprint record path bytes then
      let payload ← state.memory.openPayloadInScope scope path
      return { state with payloads := (id, payload) :: state.payloads }
    else none
  | .loadPayload scope id bytes =>
    state.observePayload id bytes (state.memory.readPayloadInScope scope)
  | .loadPayloadField scope id tag steps bytes => state.observePayload id bytes fun payload =>
    if payload.tag = tag then state.memory.readPayloadFieldInScope scope payload steps else none
  | .forgetPayload id => do
    let _ ← state.payload? id
    return { state with payloads := state.payloads.filter fun entry => entry.1 != id }
  | .fork scope tasks =>
    if state.memory.scopeActive scope && checkFork record tasks then
      tasks.foldlM (Task.execute scope) state
    else none

inductive Step {record : PackedRecord abi schema} (state : Execution record) :
    Op → Execution record → Prop where
  | openScope {id : Nat} (opened : state.memory.openScope path mode = some (id, memory)) :
      Step state (.openScope id path mode) { state with memory }
  | reborrow {id : Nat} (opened : state.memory.reborrowScope parent path mode = some (id, memory)) :
      Step state (.reborrow id parent path mode) { state with memory }
  | closeScope {id : Nat} (closed : state.memory.closeScope id = some memory) :
      Step state (.closeScope id) { state with memory }
  | load (span : FootprintClaim record path bytes)
      (read : state.memory.readInScope scope path = some value) :
      Step state (.load scope path bytes) { state with observations := value :: state.observations }
  | store (span : FootprintClaim record path bytes)
      (written : state.memory.writeInScope scope path code = some memory) :
      Step state (.store scope path bytes code) { state with memory }
  | capturePayload {id : Nat} (fresh : state.payload? id = none) (span : FootprintClaim record path bytes)
      (captured : state.memory.openPayloadInScope scope path = some payload) :
      Step state (.capturePayload scope id path bytes)
        { state with payloads := (id, payload) :: state.payloads }
  | loadPayload {id : Nat} (found : state.payload? id = some payload)
      (span : FootprintClaim record payload.path bytes)
      (read : state.memory.readPayloadInScope scope payload = some value) :
      Step state (.loadPayload scope id bytes) { state with observations := value :: state.observations }
  | loadPayloadField {id : Nat} (found : state.payload? id = some payload)
      (span : FootprintClaim record payload.path bytes)
      (tagged : payload.tag = tag)
      (read : state.memory.readPayloadFieldInScope scope payload steps = some value) :
      Step state (.loadPayloadField scope id tag steps bytes)
        { state with observations := value :: state.observations }
  | forgetPayload {id : Nat} (found : state.payload? id = some payload) :
      Step state (.forgetPayload id)
        { state with payloads := state.payloads.filter fun entry => entry.1 != id }
  | fork (live : state.memory.scopeActive scope = true) (safe : ForkValid record tasks)
      (ran : RunsTasks scope state tasks final) :
      Step state (.fork scope tasks) final

theorem Op.execute_sound {record : PackedRecord abi schema} {state next : Execution record} {op : Op}
    (ran : op.execute state = some next) : Step state op next := by
  cases op <;>
    simp only [Op.execute, Execution.observePayload, bind, pure, Option.bind_eq_some_iff, Prod.exists, Option.some.injEq,
      Option.ite_none_right_eq_some, Bool.and_eq_true, Option.isNone_iff_eq_none,
      checkFootprint_correct] at ran
  · obtain ⟨_, _, opened, equal, rfl⟩ := ran
    cases equal
    exact .openScope opened
  · obtain ⟨_, _, opened, equal, rfl⟩ := ran
    cases equal
    exact .reborrow opened
  · obtain ⟨_, closed, rfl⟩ := ran
    exact .closeScope closed
  · obtain ⟨span, _, read, rfl⟩ := ran
    exact .load span read
  · obtain ⟨span, _, written, rfl⟩ := ran
    exact .store span written
  · obtain ⟨⟨fresh, span⟩, _, captured, rfl⟩ := ran
    exact .capturePayload fresh span captured
  · obtain ⟨payload, found, span, _, read, rfl⟩ := ran
    exact .loadPayload found span read
  · obtain ⟨payload, found, span, _, ⟨tagged, read⟩, rfl⟩ := ran
    exact .loadPayloadField found span tagged read
  · obtain ⟨_, found, rfl⟩ := ran
    exact .forgetPayload found
  · exact .fork ran.1.1 (checkFork_sound _ _ ran.1.2) (runTasks_sound ran.2)

theorem Step.execute_complete {record : PackedRecord abi schema} {state next : Execution record} {op : Op}
    (step : Step state op next) : op.execute state = some next := by
  cases step with
  | openScope opened => simp [Op.execute, opened, bind]
  | reborrow opened => simp [Op.execute, opened, bind]
  | closeScope closed => simp [Op.execute, closed, bind, pure]
  | load span read => simp [Op.execute, (checkFootprint_correct _ _ _).mpr span, read, bind, pure]
  | store span written => simp [Op.execute, (checkFootprint_correct _ _ _).mpr span, written, bind, pure]
  | capturePayload fresh span captured =>
    simp [Op.execute, fresh, (checkFootprint_correct _ _ _).mpr span, captured, bind, pure]
  | loadPayload found span read =>
    simp [Op.execute, Execution.observePayload, found, (checkFootprint_correct _ _ _).mpr span, read, bind, pure]
  | loadPayloadField found span tagged read =>
    simp [Op.execute, Execution.observePayload, found, (checkFootprint_correct _ _ _).mpr span, tagged, read, bind, pure]
  | forgetPayload found => simp [Op.execute, found, bind, pure]
  | fork live safe ran => simp [Op.execute, live, checkFork_complete _ _ safe, runTasks_complete ran]

/-- Any task permutation can run under the same lexical authority. It yields
the same final image, authority and payload generations. Reads retain the
order of the chosen schedule and each returns its pre-fork value. -/
def ForkScheduleAgreement {record : PackedRecord abi schema} (scope : Nat)
    (state final : Execution record) (tasks : List Task) (before : Image record.layout.size) : Prop :=
    ∃ actions, CoversFork (record := record) tasks actions ∧
      final.observations = ((actions.map (fun action => action.result before)).flatMap
        Option.toList).reverse ++ state.observations ∧
      (∀ schedule, actions.Perm schedule →
        (applyPackedSchedule schedule before).InAllocation record.owner final.memory.heap ∧
        observePackedSchedule schedule before = schedule.map (fun action => action.result before)) ∧
      ∀ order, tasks.Perm order →
        ∃ scheduled result, CoversFork (record := record) order scheduled ∧ actions.Perm scheduled ∧
          (Op.fork scope order).execute state = some result ∧
          (applyPackedSchedule actions before).InAllocation record.owner result.memory.heap ∧
          result.observations = ((scheduled.map (fun action => action.result before)).flatMap
            Option.toList).reverse ++ state.observations ∧
          result.memory.authority = final.memory.authority ∧
          result.memory.generation = final.memory.generation ∧ result.payloads = final.payloads

theorem Step.fork_schedule {record : PackedRecord abi schema} {scope : Nat} {tasks : List Task}
    {state final : Execution record} {before : Image record.layout.size}
    (step : Step state (.fork scope tasks) final)
    (represented : before.InAllocation record.owner state.memory.heap) :
    ForkScheduleAgreement scope state final tasks before := by
  cases step with
  | fork live compatible ran =>
    obtain ⟨actions, resolved, independent⟩ := compatible
    obtain ⟨stored, observed⟩ := ran.on_image resolved represented
    rw [observePackedSchedule_eq_snapshot record.owner actions independent] at observed
    refine ⟨actions, resolved, observed, ?_, ?_⟩
    · intro schedule perm
      refine ⟨?_, observePackedSchedule_eq_snapshot record.owner schedule
        (independent.perm perm (fun h => forkDisjoint_symm h)) before⟩
      rwa [← applyPackedSchedule_perm record.owner perm independent before]
    · intro order perm
      obtain ⟨scheduled, result, covered, reordered, alternate⟩ :=
        ran.permute resolved independent represented perm
      have safe := independent.perm reordered (fun h => forkDisjoint_symm h)
      obtain ⟨bytes, observations⟩ := alternate.on_image covered represented
      rw [← applyPackedSchedule_perm record.owner reordered independent before] at bytes
      rw [observePackedSchedule_eq_snapshot record.owner scheduled safe] at observations
      obtain ⟨authority, payloads⟩ := alternate.preserves_scope
      obtain ⟨refAuthority, refPayloads⟩ := ran.preserves_scope
      have executes : (Op.fork scope order).execute state = some result := by
        simp [Op.execute, live, checkFork_complete record order ⟨scheduled, covered, safe⟩,
          runTasks_complete alternate]
      refine ⟨scheduled, result, covered, reordered, executes, bytes, observations,
        authority.trans refAuthority.symm, ?_, payloads.trans refPayloads.symm⟩
      funext key
      rw [alternate.generation key, ran.generation key, perm.countP_eq (Task.writesPath key)]

private def storeCode (path : List Nat) (code : Nat) (key : List Nat) (old : Option Nat) : Option Nat :=
  if key = path then some code else old

private def Task.updateCode (key : List Nat) (old : Option Nat) (task : Task) : Option Nat :=
  match task.code with
  | none => old
  | some code => storeCode task.path code key old

/-- The logical effect of an operation depends only on declaration paths and
the codes of stores. Byte offsets and scope metadata do not enter this model. -/
def Op.updateCode (key : List Nat) (old : Option Nat) : Op → Option Nat
  | .store _ path _ code => storeCode path code key old
  | .fork _ tasks => tasks.foldl (Task.updateCode key) old
  | _ => old

private theorem written_on_image {record : PackedRecord abi schema}
    {state next : record.Memory} {scope code : Nat} {path : List Nat}
    {before : Image record.layout.size}
    (written : state.writeInScope scope path code = some next)
    (represented : before.InAllocation record.owner state.heap) :
    ∃ after : Image record.layout.size, after.InAllocation record.owner next.heap ∧
      ∀ key, record.readImage after key = storeCode path code key (record.readImage before key) := by
  obtain ⟨after, applied, stored⟩ := state.writeInScope_on_image represented written
  refine ⟨after, stored, fun key => ?_⟩
  by_cases same : key = path
  · subst key
    simpa [storeCode] using record.readImage_after_write applied
  · simpa [storeCode, same] using record.writeImage_frame applied (Ne.symm same)

private theorem RunsTasks.refines_codes {record : PackedRecord abi schema} {scope : Nat}
    {state final : Execution record} {tasks : List Task} {before : Image record.layout.size}
    (ran : RunsTasks scope state tasks final)
    (represented : before.InAllocation record.owner state.memory.heap) :
    ∃ after : Image record.layout.size, after.InAllocation record.owner final.memory.heap ∧
      ∀ key, record.readImage after key = tasks.foldl (Task.updateCode key) (record.readImage before key) := by
  induction ran generalizing before with
  | nil => exact ⟨before, represented, fun _ => rfl⟩
  | cons step _ ih =>
    cases step with
    | load _ => exact ih represented
    | store stored =>
      obtain ⟨middle, advanced, values⟩ := written_on_image stored represented
      obtain ⟨after, finalImage, replay⟩ := ih advanced
      exact ⟨after, finalImage, fun key => by
        simpa only [List.foldl_cons, Task.updateCode, values key] using replay key⟩

theorem Step.refines_codes {record : PackedRecord abi schema} {state next : Execution record}
    {op : Op} {before : Image record.layout.size} (step : Step state op next)
    (represented : before.InAllocation record.owner state.memory.heap) :
    ∃ after : Image record.layout.size, after.InAllocation record.owner next.memory.heap ∧
      ∀ key, record.readImage after key = op.updateCode key (record.readImage before key) := by
  cases step with
  | openScope opened => exact ⟨before, represented.of_allocations
      (PackedRecord.Memory.openScope_allocations opened), fun _ => rfl⟩
  | reborrow opened => exact ⟨before, represented.of_allocations
      (PackedRecord.Memory.reborrowScope_allocations opened), fun _ => rfl⟩
  | closeScope closed => exact ⟨before, represented.of_allocations
      (PackedRecord.Memory.closeScope_allocations closed), fun _ => rfl⟩
  | store _ written => exact written_on_image written represented
  | fork _ _ ran => exact ran.refines_codes represented
  | load | capturePayload | loadPayload | loadPayloadField | forgetPayload =>
    exact ⟨before, represented, fun _ => rfl⟩

inductive Runs {record : PackedRecord abi schema} :
    Execution record → List Op → Execution record → Prop where
  | nil : Runs state [] state
  | cons : Step state op next → Runs next rest final → Runs state (op :: rest) final

private def Task.kernelProgram {record : PackedRecord abi schema} (task : Task) (scope : Nat)
    (state : Execution record) : Option Core.Program :=
  match task.code with
  | none => state.memory.readInScopeProgram scope task.path
  | some code => state.memory.writeInScopeProgram scope task.path code

def tasksKernelPrograms {record : PackedRecord abi schema} (scope : Nat) :
    Execution record → List Task → Option (List Core.Program)
  | _, [] => some []
  | state, task :: rest => do
    let first ← task.kernelProgram scope state
    let next ← task.execute scope state
    let suffix ← tasksKernelPrograms scope next rest
    return first :: suffix

private def tasksKernelProgram {record : PackedRecord abi schema} (scope : Nat)
    (state : Execution record) (tasks : List Task) : Option Core.Program :=
  (tasksKernelPrograms scope state tasks).map List.flatten

private theorem tasksKernelProgram_cons {record : PackedRecord abi schema} (scope : Nat)
    (state : Execution record) (task : Task) (rest : List Task) :
    tasksKernelProgram scope state (task :: rest) = (do
      let first ← task.kernelProgram scope state
      let next ← task.execute scope state
      let suffix ← tasksKernelProgram scope next rest
      return first ++ suffix) := by
  cases first : task.kernelProgram scope state <;> cases next : task.execute scope state <;>
    simp [tasksKernelProgram, tasksKernelPrograms, first, next, bind, pure]
  rename_i current
  cases tasksKernelPrograms scope current rest <;> rfl

private theorem tasksKernelProgram_accesses {record : PackedRecord abi schema} {scope : Nat}
    {state : Execution record} {tasks : List Task} {program : Core.Program}
    (compiled : tasksKernelProgram scope state tasks = some program) :
    program.all Core.Instruction.isByteAccess = true := by
  induction tasks generalizing state program with
  | nil => cases compiled; rfl
  | cons task rest ih =>
    simp only [tasksKernelProgram_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨first, head, _, _, _, tail, rfl⟩ := compiled
    have firstAccesses : first.all Core.Instruction.isByteAccess = true := by
      unfold Task.kernelProgram at head
      split at head
      · exact PackedRecord.Memory.readInScopeProgram_accesses head
      · exact PackedRecord.Memory.writeInScopeProgram_accesses head
    simp only [List.all_append, firstAccesses, ih tail, Bool.and_self]

private def Op.kernelProgram {record : PackedRecord abi schema}
    (state next : Execution record) : Op → Option Core.Program
  | .openScope .. => state.memory.openScopeProgram next.memory
  | .reborrow .. | .forgetPayload .. => some []
  | .closeScope id => state.memory.closeScopeProgram id
  | .load scope path _ | .capturePayload scope _ path _ => state.memory.readInScopeProgram scope path
  | .store scope path _ code => state.memory.writeInScopeProgram scope path code
  | .loadPayload scope id _ | .loadPayloadField scope id _ _ _ => do
    let payload ← state.payload? id
    state.memory.readInScopeProgram scope payload.path
  | .fork scope tasks => tasksKernelProgram scope state tasks

private def kernelProgramFrom {record : PackedRecord abi schema} :
    Execution record → List Op → Option Core.Program
  | _, [] => some []
  | state, op :: rest => do
    let next ← op.execute state
    let first ← op.kernelProgram state next
    let suffix ← kernelProgramFrom next rest
    return first ++ suffix

private theorem keepsExtents_of_byteAccesses {program : Core.Program}
    (accesses : program.all Core.Instruction.isByteAccess = true) :
    program.all Core.Instruction.keepsExtents = true := by
  apply List.all_eq_true.mpr
  intro op member
  have usable := List.all_eq_true.mp accesses op member
  cases op <;> simp_all [Core.Instruction.isByteAccess, Core.Instruction.keepsExtents]

private theorem Op.kernelProgram_keepsExtents {record : PackedRecord abi schema}
    {state next : Execution record} {op : Op} {program : Core.Program}
    (compiled : op.kernelProgram state next = some program) :
    program.all Core.Instruction.keepsExtents = true := by
  cases op with
  | openScope => exact PackedRecord.Memory.openScopeProgram_keepsExtents compiled
  | closeScope => exact PackedRecord.Memory.closeScopeProgram_keepsExtents compiled
  | reborrow | forgetPayload => cases compiled; rfl
  | load | capturePayload =>
    exact keepsExtents_of_byteAccesses (PackedRecord.Memory.readInScopeProgram_accesses compiled)
  | store =>
    exact keepsExtents_of_byteAccesses (PackedRecord.Memory.writeInScopeProgram_accesses compiled)
  | loadPayload | loadPayloadField =>
    obtain ⟨_, _, loaded⟩ := Option.bind_eq_some_iff.mp compiled
    exact keepsExtents_of_byteAccesses (PackedRecord.Memory.readInScopeProgram_accesses loaded)
  | fork => exact keepsExtents_of_byteAccesses (tasksKernelProgram_accesses compiled)

private theorem kernelProgramFrom_keepsExtents {record : PackedRecord abi schema}
    {state : Execution record} {operations : List Op} {program : Core.Program}
    (compiled : kernelProgramFrom state operations = some program) :
    program.all Core.Instruction.keepsExtents = true := by
  induction operations generalizing state program with
  | nil => cases compiled; rfl
  | cons op rest ih =>
    simp only [kernelProgramFrom, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨next, _, first, emitted, tail, continued, rfl⟩ := compiled
    simp [List.all_append, Op.kernelProgram_keepsExtents emitted, ih continued]

private theorem Task.Step.kernel_trace {record : PackedRecord abi schema}
    {scope : Nat} {state next : Execution record} {task : Task} (step : Task.Step scope state task next) :
    ∃ program, task.kernelProgram scope state = some program ∧
      Core.RunsOnStorage state.memory.heap program next.memory.heap := by
  cases step with
  | load read => exact PackedRecord.Memory.readInScope_kernel read
  | store written =>
    obtain ⟨program, compiled, traced⟩ := PackedRecord.Memory.writeInScope_kernel written
    exact ⟨program, compiled, traced.onStorage⟩

private theorem RunsTasks.kernel_trace {record : PackedRecord abi schema} {scope : Nat} {tasks : List Task}
    {state final : Execution record} (ran : RunsTasks scope state tasks final) :
    ∃ program, tasksKernelProgram scope state tasks = some program ∧
      Core.RunsOnStorage state.memory.heap program final.memory.heap := by
  induction ran with
  | nil => exact ⟨[], rfl, Core.Runs.nil.onStorage⟩
  | cons step _ ih =>
    obtain ⟨first, compiled, begun⟩ := step.kernel_trace
    obtain ⟨suffix, remaining, continued⟩ := ih
    exact ⟨first ++ suffix, by simp [tasksKernelProgram_cons, compiled, step.execute_complete,
      remaining, bind, pure], begun.append continued⟩

private theorem RunsTasks.kernel_task_at {record : PackedRecord abi schema} {scope : Nat} {tasks : List Task}
    {state final : Execution record} {earlier later : List Core.Program} {program : Core.Program}
    (ran : RunsTasks scope state tasks final)
    (compiled : tasksKernelPrograms scope state tasks = some (earlier ++ program :: later)) :
    ∃ before after : Execution record, ∃ task, tasks[earlier.length]? = some task ∧
      Task.Step scope before task after ∧
      task.kernelProgram scope before = some program ∧
      Core.RunsOnStorage state.memory.heap earlier.flatten before.memory.heap ∧
      before.memory.authority = state.memory.authority := by
  induction earlier generalizing tasks state with
  | nil =>
    cases ran with
    | nil => cases compiled
    | cons step _ =>
      simp only [tasksKernelPrograms, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
        List.nil_append, List.cons.injEq] at compiled
      obtain ⟨_, first, _, _, _, _, rfl, _⟩ := compiled
      exact ⟨_, _, _, rfl, step, first, Core.Runs.nil.onStorage, rfl⟩
  | cons head earlier ih =>
    cases ran with
    | nil => cases compiled
    | cons step rest =>
      simp only [tasksKernelPrograms, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq, List.cons_append, List.cons.injEq, step.execute_complete] at compiled
      obtain ⟨_, compiledHead, _, rfl, _, suffix, rfl, rfl⟩ := compiled
      obtain ⟨before, after, task, atIndex, selected, picked, traced, same⟩ := ih rest suffix
      obtain ⟨first, computed, begun⟩ := step.kernel_trace
      rw [compiledHead] at computed
      cases computed
      exact ⟨before, after, task, atIndex, selected, picked, begun.append traced, same.trans step.preserves_authority⟩

private theorem Task.Step.kernelProgram_footprint {record : PackedRecord abi schema}
    {state next : Execution record} {task : Task} {scope : Nat}
    {action : PackedForkAction record.layout.size} (step : Task.Step scope state task next)
    (resolved : task.Resolves record action) :
    ∃ program, task.kernelProgram scope state = some program ∧
      TaskFootprint.ofProgram state.memory.heap.resources program = some (action.footprint record.owner) := by
  cases resolved with
  | load found =>
    cases step with
    | load read =>
      obtain ⟨program, compiled, _⟩ := PackedRecord.Memory.readInScope_kernel read
      exact ⟨program, compiled, PackedRecord.Memory.readInScopeProgram_footprint found read compiled⟩
  | store found _ =>
    cases step with
    | store written =>
      obtain ⟨program, compiled, _⟩ := PackedRecord.Memory.writeInScope_kernel written
      exact ⟨program, compiled, PackedRecord.Memory.writeInScopeProgram_footprint found written compiled⟩

private theorem RunsTasks.kernel_footprints {record : PackedRecord abi schema} {scope : Nat}
    {state final : Execution record} {tasks : List Task}
    {actions : List (PackedForkAction record.layout.size)} (ran : RunsTasks scope state tasks final)
    (covered : CoversFork (record := record) tasks actions) :
    ∃ programs, tasksKernelPrograms scope state tasks = some programs ∧
      programs.mapM (TaskFootprint.ofProgram state.memory.heap.resources) =
        some (actions.map (PackedForkAction.footprint record.owner)) := by
  induction ran generalizing actions with
  | nil => cases covered; exact ⟨[], rfl, rfl⟩
  | @cons current task next remaining final step _ ih =>
    cases covered with
    | cons resolved rest =>
      obtain ⟨first, compiled, exactFootprint⟩ := step.kernelProgram_footprint resolved
      obtain ⟨suffix, continued, exactSuffix⟩ := ih rest
      have resources : next.memory.heap.resources = current.memory.heap.resources :=
        congrArg (fun a => a.2.2) step.preserves_authority
      rw [resources] at exactSuffix
      refine ⟨first :: suffix, ?_, ?_⟩
      · simp [tasksKernelPrograms, compiled, step.execute_complete, continued, bind, pure]
      · simp [List.mapM_cons, bind, pure, exactFootprint, exactSuffix]

theorem Step.fork_kernel_footprints {record : PackedRecord abi schema} {state final : Execution record}
    {scope : Nat} {tasks : List Task} (step : Step state (.fork scope tasks) final) :
    ∃ programs footprints, tasksKernelPrograms scope state tasks = some programs ∧
      tasksKernelProgram scope state tasks = some programs.flatten ∧
      programs.mapM (TaskFootprint.ofProgram state.memory.heap.resources) = some footprints ∧
      footprints.Pairwise ForkDisjoint := by
  cases step with
  | fork _ safe ran =>
    obtain ⟨actions, resolved, compatible⟩ := safe
    obtain ⟨programs, compiled, exactFootprints⟩ := ran.kernel_footprints resolved
    exact ⟨programs, _, compiled, by simp [tasksKernelProgram, compiled], exactFootprints,
      compatible.map _ (fun _ _ h => h)⟩

theorem Step.fork_kernel_authority {record : PackedRecord abi schema} {state final : Execution record}
    {scope : Nat} {tasks : List Task} (step : Step state (.fork scope tasks) final) :
    ∃ serial, tasksKernelProgram scope state tasks = some serial ∧
      ∀ reordered, serial.Perm reordered → ∃ joined, Core.Runs state.memory.heap reordered joined ∧
        joined.resources = state.memory.heap.resources := by
  cases step with
  | fork _ _ ran =>
    obtain ⟨serial, compiled, reached, traced, _⟩ := ran.kernel_trace
    exact ⟨serial, compiled, fun _ order => traced.reorder_byteAccesses (tasksKernelProgram_accesses compiled) order⟩

/-- Interleaving the emitted byte programs in task order preserves the
reference fork's storage and each task's reads against its isolated prefix.
This theorem compares the given write operands. -/
theorem Step.fork_kernel_interleavings {record : PackedRecord abi schema} {state final : Execution record}
    {scope : Nat} {tasks : List Task} (step : Step state (.fork scope tasks) final) :
    ∃ programs, tasksKernelPrograms scope state tasks = some programs ∧
      ∀ schedule, SourceVerification.TaskSchedule programs schedule →
        SourceVerification.KernelReadsAgree state.memory.heap programs schedule ∧ ∃ joined,
        Core.Runs state.memory.heap schedule joined ∧ joined.resources = state.memory.heap.resources ∧
        ∀ location, joined.byte location = final.memory.heap.byte location := by
  obtain ⟨programs, footprints, compiled, flattened, decoded, compatible⟩ := step.fork_kernel_footprints
  have trace : Core.RunsOnStorage state.memory.heap programs.flatten final.memory.heap := by
    cases step with
    | fork _ _ ran =>
      obtain ⟨serial, agrees, traced⟩ := ran.kernel_trace
      rw [flattened] at agrees
      cases agrees
      exact traced
  obtain ⟨serial, ranSerial, storage⟩ := trace
  have accesses := tasksKernelProgram_accesses flattened
  refine ⟨programs, compiled, ?_⟩
  intro schedule ordered
  refine ⟨ordered.kernel_reads_agree ranSerial accesses decoded compatible, ?_⟩
  obtain ⟨joined, ranSchedule, resources⟩ := ranSerial.reorder_byteAccesses accesses ordered.perm_flatten.symm
  refine ⟨joined, ranSchedule, resources, fun location => ?_⟩
  have sameByte := congrArg (fun machine : Core.State => machine.byte location) storage
  exact (ordered.kernel_byte_agreement ranSerial ranSchedule accesses decoded compatible location).trans sameByte

/-- Collect the physical samples of a selected store under an interleaving.
Rebuilding its writes from those samples gives the fork-entry program. -/
theorem scheduledStore_fromSamples (field : PackedValueField size width) (codec : PackedCodec α width)
    {state final : Core.State} {owner : Core.OwnerId} {targets : List Structured.AccessTarget}
    {image : Image size} {value : α} {program schedule : Core.Program}
    {earlier later : List Core.Program} {footprints : List TaskFootprint}
    (allowed : AccessAllowed state owner .exclusive field.byteOffsets targets)
    (represented : image.InAllocation owner state)
    (compiled : field.writeProgram codec state owner targets value = some program)
    (ordered : SourceVerification.TaskSchedule (earlier ++ program :: later) schedule)
    (ran : Core.Runs state schedule final) (accesses : schedule.all Core.Instruction.isByteAccess = true)
    (decoded : (earlier ++ program :: later).mapM (TaskFootprint.ofProgram state.resources) = some footprints)
    (compatible : footprints.Pairwise ForkDisjoint) :
    ∃ started remaining siblingStart siblingRest observed samples writes, schedule = started ++ remaining ∧
      SourceVerification.TaskSchedule (earlier ++ later) (siblingStart ++ siblingRest) ∧
      SourceVerification.InterleavedReadSamples state (field.mergeTrace targets) siblingStart started samples observed ∧
      field.writeInstructionsFromSamples codec owner targets value samples = some writes ∧
      program = field.mergeTrace targets ++ writes ∧ SourceVerification.TaskInterleave writes siblingRest remaining := by
  have rebuilt := field.writeProgram_eq_fromSamples codec (targets := targets) (value := value) represented rfl
  obtain ⟨writes, ready, rfl⟩ := Option.map_eq_some_iff.mp (rebuilt.symm.trans compiled)
  obtain ⟨readable, snapshot⟩ := field.mergeTrace_samples allowed represented
  obtain ⟨started, remaining, siblingStart, siblingRest, observed, samples, cut, siblings, collected, late, sampled⟩ :=
    ordered.read_block_samples ran accesses decoded compatible readable
  have sameSamples := Option.some.inj (sampled.symm.trans snapshot)
  exact ⟨started, remaining, siblingStart, siblingRest, observed, samples, writes, cut, siblings,
    collected, by simpa only [sameSamples] using ready, rfl, late⟩

private theorem Task.Step.kernelStore_sampling {record : PackedRecord abi schema}
    {scope code : Nat} {state next : Execution record} {task : Task} {program : Core.Program}
    (step : Task.Step scope state task next) (stored : task.code = some code)
    (compiled : task.kernelProgram scope state = some program) :
    ∃ reads writes samples, program = reads ++ writes ∧
      (∀ op ∈ reads, ∃ location, op.byteAccess state.memory.heap.resources = some (.read location)) ∧
      (∀ op ∈ writes, ∃ location byte, op.byteAccess state.memory.heap.resources = some (.write location byte)) ∧
      reads.mapM (Core.Instruction.readSample state.memory.heap) = some samples ∧
      state.memory.writeInScopeProgramFromSamples scope task.path code samples = some program := by
  cases step with
  | load _ => cases stored
  | store written =>
    cases stored
    exact PackedRecord.Memory.writeInScopeProgram_sampling written compiled

private theorem readSamples_of_sibling_prefix {entry next : Core.State}
    {earlier later : List Core.Program} {group reads : Core.Program} {footprints : List TaskFootprint}
    (prefixRun : Core.RunsOnStorage entry earlier.flatten next)
    (onlyBytes : earlier.flatten.all Core.Instruction.isByteAccess = true)
    (sameResources : next.resources = entry.resources)
    (covered : ∀ op ∈ reads, op ∈ group)
    (decoded : (earlier ++ group :: later).mapM (TaskFootprint.ofProgram entry.resources) = some footprints)
    (compatible : footprints.Pairwise ForkDisjoint) :
    reads.mapM (Core.Instruction.readSample next) = reads.mapM (Core.Instruction.readSample entry) := by
  obtain ⟨reached, traced, sameStorage⟩ := prefixRun
  apply mapM_eq_of_mem
  intro reader isRead
  unfold Core.Instruction.readSample
  rw [sameResources]
  cases resolves : reader.byteAccess entry.resources with
  | none => rfl
  | some event =>
    cases event with
    | write _ _ => rfl
    | read location =>
      have framed : earlier.flatten.filterMap (Core.Instruction.writeValueAt entry.resources location) = [] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro writer member
        obtain ⟨sibling, present, included⟩ := List.mem_flatten.mp member
        have noWrite := TaskFootprint.siblings_do_not_write_reads decoded compatible (covered reader isRead)
          resolves (List.mem_append_left _ present)
        exact List.filterMap_eq_nil_iff.mp noWrite writer included
      have reachedFrame := traced.byte_after_accesses onlyBytes location
      rw [framed] at reachedFrame
      have agrees := congrArg (fun s : Core.State => s.byte location) sameStorage
      have same : next.byte location = entry.byte location := agrees.symm.trans reachedFrame
      simp [Core.ByteAccess.readSample, same]

/-- An admitted store group can regenerate its emitted operands from that
task's actual boundary samples under any task-order-preserving scheduler. -/
def ForkKernelSampling {record : PackedRecord abi schema} (scope : Nat) (state : Execution record)
    (tasks : List Task) (programs : List Core.Program) : Prop :=
  ∀ {earlier later : List Core.Program} {program : Core.Program}, programs = earlier ++ program :: later →
  ∀ {task : Task}, tasks[earlier.length]? = some task → ∀ {code : Nat}, task.code = some code →
    ∃ reads writes expected, program = reads ++ writes ∧
      (∀ op ∈ writes, ∃ location byte, op.byteAccess state.memory.heap.resources = some (.write location byte)) ∧
      reads.mapM (Core.Instruction.readSample state.memory.heap) = some expected ∧
      state.memory.writeInScopeProgramFromSamples scope task.path code expected = some program ∧
      ∀ schedule, SourceVerification.TaskSchedule programs schedule → ∀ {joined},
        Core.Runs state.memory.heap schedule joined →
        ∃ started remaining siblingStart siblingRest observed samples, schedule = started ++ remaining ∧
          SourceVerification.TaskSchedule (earlier ++ later) (siblingStart ++ siblingRest) ∧
          SourceVerification.InterleavedReadSamples state.memory.heap reads siblingStart started samples observed ∧
          state.memory.writeInScopeProgramFromSamples scope task.path code samples = some program ∧
          SourceVerification.TaskInterleave writes siblingRest remaining

theorem Step.fork_kernel_sampling {record : PackedRecord abi schema} {state final : Execution record}
    {scope : Nat} {tasks : List Task} (step : Step state (.fork scope tasks) final) :
    ∃ programs, tasksKernelPrograms scope state tasks = some programs ∧ ForkKernelSampling scope state tasks programs := by
  obtain ⟨programs, footprints, compiled, flattened, decoded, compatible⟩ := step.fork_kernel_footprints
  cases step with
  | fork _ _ ran =>
    refine ⟨programs, compiled, ?_⟩
    intro earlier later program groups task atIndex code stored
    subst programs
    obtain ⟨before, _, actual, picked, selected, kernel, prefixRun, same⟩ := ran.kernel_task_at compiled
    have sameTask := Option.some.inj (picked.symm.trans atIndex)
    subst actual
    obtain ⟨reads, writes, expected, parts, readable, writable, snapshot, rebuild⟩ :=
      selected.kernelStore_sampling stored kernel
    have sameResources : before.memory.heap.resources = state.memory.heap.resources :=
      congrArg (fun a => a.2.2) same
    have allAccesses := tasksKernelProgram_accesses flattened
    have earlierAccesses : earlier.flatten.all Core.Instruction.isByteAccess = true := by
      apply List.all_eq_true.mpr
      intro op member
      apply List.all_eq_true.mp allAccesses
      rw [List.flatten_append]
      exact List.mem_append_left _ member
    have fromEntry := readSamples_of_sibling_prefix prefixRun earlierAccesses sameResources
      (fun op member => by rw [parts]; exact List.mem_append_left _ member) decoded compatible
    have currentReads : ∀ op ∈ reads, ∃ location,
        op.byteAccess state.memory.heap.resources = some (.read location) := by
      simpa only [sameResources] using readable
    have entrySnapshot := fromEntry.symm.trans snapshot
    have entryRebuild : state.memory.writeInScopeProgramFromSamples scope task.path code expected = some program := by
      rw [← PackedRecord.Memory.sampledProgram_of_authority same]
      exact rebuild
    refine ⟨reads, writes, expected, parts, by simpa only [sameResources] using writable,
      entrySnapshot, entryRebuild, ?_⟩
    intro schedule order joined executed
    have scheduleAccesses := List.all_eq_true.mpr fun op member =>
      List.all_eq_true.mp allAccesses op (order.perm_flatten.mem_iff.mp member)
    rw [parts] at order decoded
    obtain ⟨started, remaining, siblingStart, siblingRest, observed, samples, cut, siblings, collected, late, sampled⟩ :=
      order.read_block_samples executed scheduleAccesses decoded compatible currentReads
    have equalSamples := Option.some.inj (sampled.symm.trans entrySnapshot)
    refine ⟨started, remaining, siblingStart, siblingRest, observed, samples, cut, siblings, collected, ?_, late⟩
    rwa [equalSamples]

theorem Step.kernel_trace {record : PackedRecord abi schema} {state next : Execution record}
    {op : Op} (step : Step state op next) :
    ∃ program, op.kernelProgram state next = some program ∧
      Core.RunsOnStorage state.memory.heap program next.memory.heap := by
  cases step with
  | openScope opened =>
    obtain ⟨program, computed, traced⟩ := PackedRecord.Memory.openScope_kernel opened
    exact ⟨program, computed, traced.onStorage⟩
  | reborrow opened =>
    refine ⟨[], rfl, ?_⟩
    rw [PackedRecord.Memory.reborrowScope_heap opened]
    exact Core.Runs.nil.onStorage
  | closeScope closed =>
    obtain ⟨program, computed, traced⟩ := PackedRecord.Memory.closeScope_kernel closed
    exact ⟨program, computed, traced.onStorage⟩
  | load _ read => exact PackedRecord.Memory.readInScope_kernel read
  | store _ written =>
    obtain ⟨program, computed, traced⟩ := PackedRecord.Memory.writeInScope_kernel written
    exact ⟨program, computed, traced.onStorage⟩
  | capturePayload _ _ captured => exact PackedRecord.Memory.openPayloadInScope_kernel captured
  | loadPayload found _ read =>
    obtain ⟨program, computed, traced⟩ := PackedRecord.Memory.readPayloadInScope_kernel read
    exact ⟨program, by simp [Op.kernelProgram, found, computed, bind], traced⟩
  | loadPayloadField found _ _ read =>
    obtain ⟨program, computed, traced⟩ := PackedRecord.Memory.readPayloadFieldInScope_kernel read
    exact ⟨program, by simp [Op.kernelProgram, found, computed, bind], traced⟩
  | forgetPayload _ => exact ⟨[], rfl, Core.Runs.nil.onStorage⟩
  | fork _ _ tasks => exact tasks.kernel_trace

theorem Runs.kernel_trace {record : PackedRecord abi schema} {state final : Execution record}
    {code : List Op} (ran : Runs state code final) :
    ∃ program, kernelProgramFrom state code = some program ∧
      Core.RunsOnStorage state.memory.heap program final.memory.heap := by
  induction ran with
  | nil => exact ⟨[], rfl, Core.Runs.nil.onStorage⟩
  | cons step _ ih =>
    obtain ⟨first, computed, begun⟩ := step.kernel_trace
    obtain ⟨rest, remaining, continued⟩ := ih
    exact ⟨first ++ rest, by simp [kernelProgramFrom, step.execute_complete, computed,
      remaining, bind, pure], begun.append continued⟩

theorem Runs.refines_codes {record : PackedRecord abi schema} {state final : Execution record}
    {code : List Op} {before : Image record.layout.size} (ran : Runs state code final)
    (represented : before.InAllocation record.owner state.memory.heap) :
    ∃ after : Image record.layout.size, after.InAllocation record.owner final.memory.heap ∧
      ∀ key, record.readImage after key = code.foldl (Op.updateCode key) (record.readImage before key) := by
  induction ran generalizing before with
  | nil => exact ⟨before, represented, fun _ => rfl⟩
  | cons step _ ih =>
    obtain ⟨_, advanced, values⟩ := step.refines_codes represented
    obtain ⟨after, finalImage, replay⟩ := ih advanced
    exact ⟨after, finalImage, fun key => by simpa only [List.foldl_cons, values key] using replay key⟩

theorem Runs.preserves_image {record : PackedRecord abi schema} {state final : Execution record}
    {code : List Op} {before : Image record.layout.size} (ran : Runs state code final)
    (represented : before.InAllocation record.owner state.memory.heap) :
    ∃ after : Image record.layout.size, after.InAllocation record.owner final.memory.heap :=
  (ran.refines_codes represented).imp (fun _ h => h.1)

private theorem Runs.split {record : PackedRecord abi schema} {initial final : Execution record}
    {start rest : List Op} (ran : Runs initial (start ++ rest) final) :
    ∃ state, Runs initial start state ∧ Runs state rest final := by
  induction start generalizing initial with
  | nil => exact ⟨initial, .nil, ran⟩
  | cons _ _ ih =>
    cases ran with
    | cons step tail =>
      obtain ⟨state, earlier, later⟩ := ih tail
      exact ⟨state, .cons step earlier, later⟩

theorem run_sound {record : PackedRecord abi schema} {state final : Execution record}
    {code : List Op} (ran : code.foldlM Op.execute state = some final) :
    Runs state code final := by
  induction code generalizing state with
  | nil => cases ran; exact .nil
  | cons op rest ih =>
    obtain ⟨next, ranOp, ranRest⟩ := Option.bind_eq_some_iff.mp ran
    exact .cons (Op.execute_sound ranOp) (ih ranRest)

theorem Runs.execute_complete {record : PackedRecord abi schema} {state final : Execution record}
    {code : List Op} (ran : Runs state code final) : code.foldlM Op.execute state = some final := by
  induction ran with
  | nil => rfl
  | cons step _ ih =>
    rw [List.foldlM_cons]
    exact Option.bind_eq_some_iff.mpr ⟨_, step.execute_complete, ih⟩

/-- Admission requires the canonical serialized layout, a mathematical
initial image, and a complete operational trace through cleanup. -/
def Module.Admissible (mir : Module) : Prop :=
  mir.version = PackedMIR.version ∧
    ∃ (record : PackedRecord .natural mir.schema) (initial : record.Memory)
      (final : Execution record) (dropped : Core.State),
      PackedRecord.plan .natural mir.schema 0 = some record ∧ mir.layout.Describes record ∧
      (mir.target.region record.layout).Valid ∧ mir.initial.map Prod.fst = mir.schema.paths ∧
      record.Initialized {} mir.initialValue initial ∧ Runs { memory := initial } mir.operations final ∧
      final.memory.scopes = [] ∧ final.payloads = [] ∧
      Core.Step final.memory.heap (.destroy record.owner) dropped

structure Accepted (mir : Module) where
  record : PackedRecord .natural mir.schema
  initial : record.Memory
  final : Execution record
  format : mir.version = version
  planned : PackedRecord.plan .natural mir.schema 0 = some record
  placement : describe record = mir.layout
  targetFits : (mir.target.region record.layout).Valid
  initialPaths : mir.initial.map Prod.fst = mir.schema.paths
  starts : record.allocate {} mir.initialValue = some initial
  runs : Runs { memory := initial } mir.operations final
  closes : final.memory.scopes = [] ∧ final.payloads = []
  dropped : Core.State
  cleanup : Core.Step final.memory.heap (.destroy record.owner) dropped

private def requireSome (value : Option α) (error : String) : Except String { result // value = some result } :=
  match value with
  | none => .error error
  | some result => .ok ⟨result, rfl⟩

private theorem requireSome_of_some {value : Option α} {result : α} {error : String}
    (found : value = some result) : requireSome value error = .ok ⟨result, found⟩ := by
  subst value
  rfl

def validate (mir : Module) : Except String (Accepted mir) := do
  if format : mir.version = version then
    let ⟨record, planned⟩ ← requireSome (PackedRecord.plan .natural mir.schema 0) "invalid packed schema"
    if placement : describe record = mir.layout then
      let targetFits : PLift (mir.target.region record.layout).Valid ←
        if fits : (mir.target.region record.layout).Valid then pure ⟨fits⟩
        else throw "packed record exceeds the target address-space or alignment bounds"
      let initialPaths : PLift (mir.initial.map Prod.fst = mir.schema.paths) ←
        if paths : mir.initial.map Prod.fst = mir.schema.paths then pure ⟨paths⟩
        else throw "initial values must match declaration paths in order"
      let ⟨initial, starts⟩ ← requireSome (record.allocate {} mir.initialValue) "invalid packed initializer"
      let ⟨final, ran⟩ ← requireSome (mir.operations.foldlM Op.execute { memory := initial })
        "invalid packed operation or physical footprint"
      if closes : final.memory.scopes = [] ∧ final.payloads = [] then
        let ⟨dropped, ended⟩ ← requireSome (Core.execute final.memory.heap (.destroy record.owner))
          "packed record destruction failed"
        return ⟨record, initial, final, format, planned, placement, targetFits.down,
          initialPaths.down, starts, run_sound ran, closes, dropped, Core.execute_sound ended⟩
      else .error "packed execution leaked a scope or payload"
    else .error "packed layout does not match the validated schema"
  else .error s!"unsupported packed MIR version {mir.version}"

theorem Accepted.admissible {mir : Module} (accepted : Accepted mir) : mir.Admissible := by
  refine ⟨accepted.format, accepted.record, accepted.initial, accepted.final, accepted.dropped,
    accepted.planned, (describe_correct _ _).mp accepted.placement, accepted.targetFits, accepted.initialPaths, ?_,
    accepted.runs, accepted.closes.1, accepted.closes.2, accepted.cleanup⟩
  exact (accepted.record.allocate_correct {} mir.initialValue accepted.initial).mp accepted.starts

theorem validate_complete {mir : Module} (valid : mir.Admissible) :
    ∃ accepted, validate mir = .ok accepted := by
  obtain ⟨format, record, initial, final, dropped, planned, placement, targetFits, paths, initialized,
    runs, scopes, payloads, cleanup⟩ := valid
  have starts := (record.allocate_correct {} mir.initialValue initial).mpr initialized
  have ran := runs.execute_complete
  have ended := Core.execute_complete cleanup
  have closed : final.memory.scopes = [] ∧ final.payloads = [] := ⟨scopes, payloads⟩
  have described := (describe_correct record mir.layout).mpr placement
  simp [validate, format, requireSome_of_some planned, described, targetFits, paths,
    requireSome_of_some starts, requireSome_of_some ran, closed, requireSome_of_some ended,
    bind, pure, Except.bind, Except.pure]

theorem validate_correct (mir : Module) : (∃ accepted, validate mir = .ok accepted) ↔ mir.Admissible :=
  ⟨fun ⟨accepted, _⟩ => accepted.admissible, validate_complete⟩

def parse (text : String) : Except String Module :=
  (Json.parse text).bind fromJson?

/-- Extract the concrete reference kernel program, including the bytes of
each store computed for this admitted execution. -/
def Accepted.kernelProgram {mir : Module} (accepted : Accepted mir) : Option Core.Program := do
  let created ← accepted.initial.allocationInstruction
  let body ← kernelProgramFrom { memory := accepted.initial } mir.operations
  return created :: body ++ [.destroy accepted.record.owner]

theorem Accepted.kernelProgram_correct {mir : Module} (accepted : Accepted mir) :
    ∃ program, accepted.kernelProgram = some program ∧ Core.RunsOnStorage {} program accepted.dropped := by
  obtain ⟨_, allocation, created⟩ := PackedRecord.allocationInstruction_correct accepted.starts
  obtain ⟨body, computed, ran⟩ := accepted.runs.kernel_trace
  exact ⟨_, by simp [kernelProgram, allocation, computed, bind, pure],
    (Core.Runs.cons created .nil).onStorage.append (ran.append (Core.Runs.cons accepted.cleanup .nil).onStorage)⟩

/-- Extract the byte operands from the emitted body using only the entry
authority and allocation extents. Scope changes occur in program order. -/
def Accepted.kernelOperands {mir : Module} (accepted : Accepted mir) : Option (List Core.ByteAccess) := do
  let body ← kernelProgramFrom { memory := accepted.initial } mir.operations
  Core.traceByteOperands accepted.initial.heap.resources body

theorem Accepted.kernelOperands_correct {mir : Module} (accepted : Accepted mir) :
    ∃ (image : Image accepted.record.layout.size) (body : Core.Program) (operands : List Core.ByteAccess)
      (reached : Core.State),
      accepted.kernelProgram = some (.alloc accepted.record.owner image.toBytes :: body ++
        [.destroy accepted.record.owner]) ∧
      accepted.kernelOperands = some operands ∧
      Core.ByteOperands accepted.initial.heap body operands reached ∧
      reached.withoutObservations = accepted.final.memory.heap.withoutObservations ∧
      body.all Core.Instruction.keepsExtents = true ∧
      ∀ access ∈ operands, access.location.allocation = accepted.record.owner ∧
        access.location.offset < accepted.record.layout.size := by
  obtain ⟨image, created⟩ := PackedRecord.allocate_kernel accepted.starts
  obtain ⟨body, built, reached, ran, agrees⟩ := accepted.runs.kernel_trace
  obtain ⟨operands, decoded⟩ := ran.byteOperands
  have allocated {heap : Core.State} (step : Core.Step {}
      (.alloc accepted.record.owner image.toBytes) heap) :
      heap.allocation accepted.record.owner = some ⟨accepted.record.owner, image.toBytes⟩ ∧
      heap.resources.allocations = [(accepted.record.owner, accepted.record.layout.size)] := by
    cases step
    simp [Core.State.allocation, Core.State.addAllocation, Core.State.resources, Image.toBytes]
  obtain ⟨initialAllocation, extents⟩ := allocated created
  have fixed := kernelProgramFrom_keepsExtents built
  refine ⟨image, body, operands, reached, ?_, ?_, decoded, agrees, fixed, ?_⟩
  · simp [kernelProgram, PackedRecord.Memory.allocationInstruction, initialAllocation, built, bind, pure]
  · simp [kernelOperands, built, decoded.computes, bind]
  · intro access member
    obtain ⟨size, reachable, inside⟩ := decoded.inBounds fixed member
    by_cases owner : access.location.allocation = accepted.record.owner
    · have exactSize : accepted.record.layout.size = size := by
        simpa [Core.ResourceState.extent, extents, owner] using reachable
      exact ⟨owner, exactSize.symm ▸ inside⟩
    · simp [Core.ResourceState.extent, extents, Ne.symm owner] at reachable

structure TargetOperand (wordBits : Nat) where
  address : BitVec wordBits
  writeValue : Option UInt8
  deriving Repr, DecidableEq

def TargetOperand.mapAddress (addressOf : Nat → BitVec wordBits) (access : Core.ByteAccess) :
    TargetOperand wordBits :=
  ⟨addressOf access.location.offset,
    match access with | .read _ => none | .write _ value => some value⟩

def TargetOperand.ofAccess (region : PackedArrayRegion layout) (wordBits : Nat) (access : Core.ByteAccess) :
    TargetOperand wordBits :=
  TargetOperand.mapAddress (region.wordAddress wordBits 0) access

/-- Word-sized physical operands for the actual checked kernel body. -/
def Accepted.kernelTargetOperands {mir : Module} (accepted : Accepted mir) (wordBits : Nat) :
    Option (List (TargetOperand wordBits)) :=
  if mir.target.limit < 2 ^ wordBits then
    accepted.kernelOperands.map (List.map (TargetOperand.ofAccess (mir.target.region accepted.record.layout) wordBits))
  else none

private theorem Accepted.targetAddress_exact {mir : Module} (accepted : Accepted mir) {wordBits offset : Nat}
    (limitFits : mir.target.limit < 2 ^ wordBits) (inside : offset < accepted.record.layout.size) :
    ((mir.target.region accepted.record.layout).wordAddress wordBits 0 offset).toNat = mir.target.base + offset ∧
      mir.target.base + offset < mir.target.limit := by
  have firstRow : 0 < (mir.target.region accepted.record.layout).count := by
    change 0 < 1
    decide
  have endBound := (mir.target.region accepted.record.layout).row_end_within accepted.targetFits firstRow
  have exactWord := ((mir.target.region accepted.record.layout).wordAddress_exact accepted.targetFits
    firstRow inside limitFits).2.2.2.2.2
  refine ⟨by simpa [PackedArrayRegion.rowBase, TargetClaim.region] using exactWord, ?_⟩
  simp [PackedArrayRegion.rowBase, TargetClaim.region] at endBound
  omega

theorem Accepted.kernelTargetOperands_exact {mir : Module} (accepted : Accepted mir) {wordBits : Nat}
    (limitFits : mir.target.limit < 2 ^ wordBits) :
    ∃ operands, accepted.kernelOperands = some operands ∧
      accepted.kernelTargetOperands wordBits = some (operands.map
        (TargetOperand.ofAccess (mir.target.region accepted.record.layout) wordBits)) ∧
      ∀ access ∈ operands,
        access.location.allocation = accepted.record.owner ∧
        ((TargetOperand.ofAccess (mir.target.region accepted.record.layout) wordBits access).address).toNat =
          mir.target.base + access.location.offset ∧
        mir.target.base + access.location.offset < mir.target.limit := by
  obtain ⟨_, _, operands, _, _, traced, _, _, _, bounded⟩ := accepted.kernelOperands_correct
  refine ⟨operands, traced, by simp [kernelTargetOperands, limitFits, traced], ?_⟩
  intro access member
  obtain ⟨owner, inside⟩ := bounded access member
  exact ⟨owner, accepted.targetAddress_exact limitFits inside⟩

structure TargetMemory (wordBits : Nat) where
  bytes : BitVec wordBits → Option UInt8
  observations : List UInt8 := []

def TargetMemory.ofBytes (wordBits base : Nat) (bytes : List UInt8) : TargetMemory wordBits :=
  { bytes := fun address =>
      if base ≤ address.toNat then bytes[address.toNat - base]? else none }

def TargetMemory.store (memory : TargetMemory wordBits) (address : BitVec wordBits)
    (value : UInt8) : TargetMemory wordBits :=
  { memory with bytes := fun query => if query = address then some value else memory.bytes query }

def TargetMemory.observe (memory : TargetMemory wordBits) (value : UInt8) : TargetMemory wordBits :=
  { memory with observations := value :: memory.observations }

def TargetOperand.execute (memory : TargetMemory wordBits) (operand : TargetOperand wordBits) :
    Option (TargetMemory wordBits) := do
  let old ← memory.bytes operand.address
  return match operand.writeValue with
    | none => memory.observe old
    | some value => memory.store operand.address value

def TargetMemory.Represents (memory : TargetMemory wordBits) (state : Core.State)
    (owner : Core.OwnerId) (size : Nat) (addressOf : Nat → BitVec wordBits) : Prop :=
  memory.observations = state.observations ∧
    ∀ offset, offset < size → memory.bytes (addressOf offset) = state.byte ⟨owner, offset⟩

/-- Legal byte operations refine fixed-word memory execution. Authority-only
kernel steps contribute no target operations. -/
theorem targetOperands_refine {state final : Core.State} {body : Core.Program} {accesses : List Core.ByteAccess}
    (trace : Core.ByteOperands state body accesses final) (fixed : body.all Core.Instruction.keepsExtents = true)
    {wordBits : Nat} {owner : Core.OwnerId} {size : Nat} {addressOf : Nat → BitVec wordBits}
    (distinctAddresses : ∀ left right, left < size → right < size → addressOf left = addressOf right → left = right)
    (bounded : ∀ access ∈ accesses, access.location.allocation = owner ∧ access.location.offset < size)
    {memory : TargetMemory wordBits} (represents : memory.Represents state owner size addressOf) :
    ∃ target, (accesses.map (TargetOperand.mapAddress addressOf)).foldlM TargetOperand.execute memory =
        some target ∧ target.Represents final owner size addressOf := by
  induction trace generalizing memory with
  | nil => exact ⟨memory, rfl, represents⟩
  | @cons current op next body accesses final step _ ih =>
    obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp fixed
    have restBound : ∀ access ∈ accesses, access.location.allocation = owner ∧ access.location.offset < size :=
      fun access member => bounded access (List.mem_append_right _ member)
    cases decoded : op.byteAccess current.resources with
    | none =>
      obtain ⟨bytes, observations⟩ := step.preserves_data_withoutOperand head decoded
      have preserved : memory.Represents next owner size addressOf :=
        ⟨represents.1.trans observations.symm, fun offset within => by rw [bytes]; exact represents.2 offset within⟩
      simpa [decoded] using ih tail restBound preserved
    | some access =>
      have inside := bounded access (List.mem_append_left _ (by simp [decoded]))
      have effect := step.refines_byteAccess decoded
      cases access with
      | read location =>
        obtain ⟨value, loaded, rfl⟩ := effect
        have same : (⟨owner, location.offset⟩ : ByteLocation) = location := by
          cases location
          simpa [Core.ByteAccess.location] using inside.1.symm
        have prior := (represents.2 location.offset inside.2).trans (same ▸ loaded)
        obtain ⟨target, ran, result⟩ := ih tail restBound (memory := memory.observe value)
          ⟨by simp [TargetMemory.observe, Core.State.observe, represents.1], represents.2⟩
        exact ⟨target, by
          simp [TargetOperand.mapAddress, TargetOperand.execute, Core.ByteAccess.location,
            List.foldlM_cons, prior, ran, bind, pure], result⟩
      | write location value =>
        obtain ⟨⟨previous, loaded⟩, rfl⟩ := effect
        have same : (⟨owner, location.offset⟩ : ByteLocation) = location := by
          cases location
          simpa [Core.ByteAccess.location] using inside.1.symm
        have prior := (represents.2 location.offset inside.2).trans (same ▸ loaded)
        have after : (memory.store (addressOf location.offset) value).Represents
            (current.store location value) owner size addressOf := by
          refine ⟨represents.1, ?_⟩
          intro offset within
          by_cases equal : offset = location.offset
          · subst offset
            rw [same]
            exact (by simpa only [TargetMemory.store, ↓reduceIte] using
              (Core.State.store_byte_written current location previous value loaded).symm)
          · have different : addressOf offset ≠ addressOf location.offset :=
              fun h => equal (distinctAddresses _ _ within inside.2 h)
            have distinct : location ≠ ⟨owner, offset⟩ := fun eq => equal (congrArg ByteLocation.offset eq).symm
            simpa [TargetMemory.store, different, Core.State.store_byte_other _ _ _ _ distinct] using
              represents.2 offset within
        obtain ⟨target, ran, result⟩ := ih tail restBound after
        exact ⟨target, by
          simp [TargetOperand.mapAddress, TargetOperand.execute, Core.ByteAccess.location,
            List.foldlM_cons, prior, ran, bind, pure], result⟩

def Accepted.replayTarget {mir : Module} (accepted : Accepted mir) (wordBits : Nat) :
    Option (TargetMemory wordBits) := do
  let allocation ← accepted.initial.heap.allocation accepted.record.owner
  let operations ← accepted.kernelTargetOperands wordBits
  operations.foldlM TargetOperand.execute (TargetMemory.ofBytes wordBits mir.target.base allocation.bytes)

theorem Accepted.replayTarget_correct {mir : Module} (accepted : Accepted mir) {wordBits : Nat}
    (limitFits : mir.target.limit < 2 ^ wordBits) :
    ∃ operands body reached target,
      accepted.kernelOperands = some operands ∧
      Core.ByteOperands accepted.initial.heap body operands reached ∧
      accepted.replayTarget wordBits = some target ∧ target.observations = reached.observations ∧
      ∀ offset, offset < accepted.record.layout.size →
        target.bytes ((mir.target.region accepted.record.layout).wordAddress wordBits 0 offset) =
          accepted.final.memory.heap.byte ⟨accepted.record.owner, offset⟩ := by
  obtain ⟨_, body, operands, reached, _, traced, steps, storage, fixed, bounded⟩ :=
    accepted.kernelOperands_correct
  obtain ⟨initial, created⟩ := PackedRecord.allocate_kernel accepted.starts
  have seeded {heap : Core.State} (step : Core.Step {} (.alloc accepted.record.owner initial.toBytes) heap) :
      heap.allocation accepted.record.owner = some ⟨accepted.record.owner, initial.toBytes⟩ ∧
      heap.observations = [] := by
    cases step
    simp [Core.State.allocation, Core.State.addAllocation]
  obtain ⟨allocation, noReads⟩ := seeded created
  let addressOf := (mir.target.region accepted.record.layout).wordAddress wordBits 0
  have addressExact (offset : Nat) (inside : offset < accepted.record.layout.size) :
      (addressOf offset).toNat = mir.target.base + offset :=
    (accepted.targetAddress_exact limitFits inside).1
  have unique (left right : Nat) (leftFits : left < accepted.record.layout.size)
      (rightFits : right < accepted.record.layout.size) (same : addressOf left = addressOf right) : left = right := by
    have equal := congrArg BitVec.toNat same
    rw [addressExact left leftFits, addressExact right rightFits] at equal
    omega
  have represented :
      (TargetMemory.ofBytes wordBits mir.target.base initial.toBytes).Represents accepted.initial.heap
        accepted.record.owner accepted.record.layout.size addressOf := by
    refine ⟨noReads.symm, fun offset inside => ?_⟩
    simp [TargetMemory.ofBytes, addressExact offset inside, Core.State.byte, allocation, bind]
  obtain ⟨target, ran, same⟩ := targetOperands_refine steps fixed unique bounded represented
  have finalBytes : reached.byte = accepted.final.memory.heap.byte := by
    change reached.withoutObservations.byte = accepted.final.memory.heap.withoutObservations.byte
    exact congrArg Core.State.byte storage
  have sameMapper : TargetOperand.ofAccess (mir.target.region accepted.record.layout) wordBits =
      TargetOperand.mapAddress addressOf := rfl
  exact ⟨operands, body, reached, target, traced, steps,
    by simpa [replayTarget, kernelTargetOperands, limitFits, allocation, traced, sameMapper, bind]
      using ran,
    same.1, fun offset inside => (same.2 offset inside).trans (congrFun finalBytes _)⟩

def Accepted.checkKernelProgram {mir : Module} (accepted : Accepted mir) (claimed : Core.Program) : Bool :=
  decide (accepted.kernelProgram = some claimed ∧
    Core.checkResources {} claimed = some accepted.dropped.resources)

theorem Accepted.checkKernelProgram_correct {mir : Module} (accepted : Accepted mir) (claimed : Core.Program) :
    accepted.checkKernelProgram claimed = true ↔ accepted.kernelProgram = some claimed := by
  simp only [checkKernelProgram, decide_eq_true_eq]
  refine ⟨And.left, fun same => ⟨same, ?_⟩⟩
  obtain ⟨_, extracted, ran⟩ := accepted.kernelProgram_correct
  cases Option.some.inj (same.symm.trans extracted)
  exact ran.checkResources

theorem Accepted.checkKernelProgram_sound {mir : Module} (accepted : Accepted mir) {claimed : Core.Program}
    (checked : accepted.checkKernelProgram claimed = true) : Core.RunsOnStorage {} claimed accepted.dropped := by
  have same := (accepted.checkKernelProgram_correct claimed).mp checked
  obtain ⟨_, extracted, ran⟩ := accepted.kernelProgram_correct
  cases Option.some.inj (same.symm.trans extracted)
  exact ran

/-- An admitted execution is implemented by a legal program of byte-kernel
instructions, from allocation through destruction. The kernel can retain
the raw byte observations that typed loads decode and consume. -/
theorem Accepted.kernel_trace {mir : Module} (accepted : Accepted mir) :
    ∃ image : Image accepted.record.layout.size, ∃ body : Core.Program,
      Core.RunsOnStorage {} (.alloc accepted.record.owner image.toBytes ::
        body ++ [.destroy accepted.record.owner]) accepted.dropped := by
  obtain ⟨image, created⟩ := PackedRecord.allocate_kernel accepted.starts
  obtain ⟨body, _, ran⟩ := accepted.runs.kernel_trace
  exact ⟨image, body, (Core.Runs.cons created .nil).onStorage.append
    (ran.append (Core.Runs.cons accepted.cleanup .nil).onStorage)⟩

theorem Accepted.prefix_kernel_safe {mir : Module} (accepted : Accepted mir) {start rest : List Op}
    (cut : mir.operations = start ++ rest) :
    ∃ state : Execution accepted.record,
      Runs { memory := accepted.initial } start state ∧ Runs state rest accepted.final ∧
      state.memory.heap.OwnersValid ∧ state.memory.heap.ReferencesLive ∧ state.memory.heap.ViewsCompatible := by
  have ran := accepted.runs
  rw [cut] at ran
  obtain ⟨state, before, after⟩ := ran.split
  obtain ⟨_, created⟩ := PackedRecord.allocate_kernel accepted.starts
  obtain ⟨_, _, traced⟩ := before.kernel_trace
  have prefixTrace := (Core.Runs.cons created .nil).onStorage.append traced
  exact ⟨state, before, after, prefixTrace.safe⟩

private theorem foldl_preserves_code {α : Type} {update : Option Nat → α → Option Nat}
    (preserves : ∀ old item, old.isSome → (update old item).isSome) (items : List α)
    {old : Option Nat} (present : old.isSome) : (items.foldl update old).isSome := by
  induction items generalizing old with
  | nil => exact present
  | cons item _ ih => exact ih (preserves old item present)

private theorem storeCode_present {path key : List Nat} {code : Nat} {old : Option Nat}
    (present : old.isSome) : (storeCode path code key old).isSome := by
  unfold storeCode
  split
  · rfl
  · exact present

private theorem Op.updateCode_present (key : List Nat) (old : Option Nat) (op : Op)
    (present : old.isSome) : (op.updateCode key old).isSome := by
  cases op with
  | store => exact storeCode_present present
  | fork _ tasks =>
    apply foldl_preserves_code _ tasks present
    intro value task valid
    unfold Task.updateCode
    split
    · exact valid
    · exact storeCode_present valid
  | openScope | reborrow | closeScope | load | capturePayload | loadPayload | loadPayloadField | forgetPayload =>
    exact present

/-- Every execution cut has a live representation of all declared fields.
The values at that cut are obtained by replaying the declaration-path
stores from the initializer, independently of the chosen layout. -/
theorem Accepted.prefix_codes {mir : Module} (accepted : Accepted mir) {start rest : List Op}
    (cut : mir.operations = start ++ rest) :
    ∃ state : Execution accepted.record, ∃ image : Image accepted.record.layout.size,
      Runs { memory := accepted.initial } start state ∧ Runs state rest accepted.final ∧
      image.InAllocation accepted.record.owner state.memory.heap ∧
      ∀ key ty, mir.schema.typeAt key = some ty → ∃ code,
        start.foldl (Op.updateCode key) (mir.initialValue key) = some code ∧
        accepted.record.readImage image key = some code ∧ code < 2 ^ ty.width ∧ ty.Represents code := by
  have ran := accepted.runs
  rw [cut] at ran
  obtain ⟨state, earlier, later⟩ := ran.split
  obtain ⟨_, allocated, initialized⟩ := PackedRecord.allocate_on_image accepted.starts
  obtain ⟨image, represented, values⟩ := earlier.refines_codes allocated
  refine ⟨state, image, earlier, later, represented, fun key ty declared => ?_⟩
  obtain ⟨original, supplied, initialRead⟩ := initialized key ty declared
  have present : (mir.initialValue key).isSome := by simp [supplied]
  obtain ⟨code, replay⟩ := Option.isSome_iff_exists.mp
    (foldl_preserves_code (Op.updateCode_present key) start present)
  have decoded := values key
  rw [initialRead, ← supplied, replay] at decoded
  exact ⟨code, replay, decoded, accepted.record.readImage_typed declared decoded⟩

theorem Accepted.final_codes {mir : Module} (accepted : Accepted mir) :
    ∃ image : Image accepted.record.layout.size,
      image.InAllocation accepted.record.owner accepted.final.memory.heap ∧
      ∀ key ty, mir.schema.typeAt key = some ty →
        accepted.record.readImage image key = mir.operations.foldl (Op.updateCode key) (mir.initialValue key) := by
  obtain ⟨_, image, _, later, represented, values⟩ :=
    accepted.prefix_codes (start := mir.operations) (rest := []) (by simp)
  cases later
  refine ⟨image, represented, fun key ty declared => ?_⟩
  obtain ⟨_, replay, decoded, _⟩ := values key ty declared
  exact decoded.trans replay.symm

theorem Accepted.fork_at {mir : Module} (accepted : Accepted mir)
    {start rest : List Op} {scope : Nat} {tasks : List Task}
    (atFork : mir.operations = start ++ .fork scope tasks :: rest) :
    ∃ state next : Execution accepted.record, ∃ before : Image accepted.record.layout.size,
      Runs { memory := accepted.initial } start state ∧
      Step state (.fork scope tasks) next ∧ Runs next rest accepted.final ∧
      before.InAllocation accepted.record.owner state.memory.heap ∧
      ForkScheduleAgreement scope state next tasks before := by
  have ran := accepted.runs
  rw [atFork] at ran
  obtain ⟨state, earlier, later⟩ := ran.split
  cases later with
  | cons step later =>
    obtain ⟨initial, allocated, _⟩ := PackedRecord.allocate_on_image accepted.starts
    obtain ⟨before, represented, _⟩ := earlier.refines_codes (before := initial) allocated
    exact ⟨state, _, before, earlier, step, later, represented, step.fork_schedule represented⟩

/-- At a fork's actual entry state, every byte-instruction shuffle has the
original authority throughout. Value agreement additionally needs the
task-local dependencies and the checked disjoint footprints. -/
theorem Accepted.fork_kernel_authority_at {mir : Module} (accepted : Accepted mir)
    {start rest : List Op} {scope : Nat} {tasks : List Task}
    (cut : mir.operations = start ++ .fork scope tasks :: rest) :
    ∃ state next : Execution accepted.record, ∃ serial : Core.Program,
      Runs { memory := accepted.initial } start state ∧ Step state (.fork scope tasks) next ∧
      Runs next rest accepted.final ∧ tasksKernelProgram scope state tasks = some serial ∧
      ∀ reordered, serial.Perm reordered → ∃ joined, Core.Runs state.memory.heap reordered joined ∧
        joined.resources = state.memory.heap.resources := by
  have ran := accepted.runs
  rw [cut] at ran
  obtain ⟨state, earlier, later⟩ := ran.split
  cases later with
  | cons step tail =>
    obtain ⟨serial, compiled, orders⟩ := step.fork_kernel_authority
    exact ⟨state, _, serial, earlier, step, tail, compiled, orders⟩

/-- Decode each task's emitted instructions using the checked fork's entry
authority, including the reads performed by masked stores. -/
theorem Accepted.fork_kernel_footprints_at {mir : Module} (accepted : Accepted mir)
    {start rest : List Op} {scope : Nat} {tasks : List Task}
    (cut : mir.operations = start ++ .fork scope tasks :: rest) :
    ∃ state next : Execution accepted.record, ∃ programs footprints,
      Runs { memory := accepted.initial } start state ∧ Step state (.fork scope tasks) next ∧
      Runs next rest accepted.final ∧ tasksKernelPrograms scope state tasks = some programs ∧
      tasksKernelProgram scope state tasks = some programs.flatten ∧
      programs.mapM (TaskFootprint.ofProgram state.memory.heap.resources) = some footprints ∧
      footprints.Pairwise ForkDisjoint := by
  have ran := accepted.runs
  rw [cut] at ran
  obtain ⟨state, earlier, later⟩ := ran.split
  cases later with
  | cons step tail =>
    obtain ⟨programs, footprints, grouped, flattened, decoded, compatible⟩ := step.fork_kernel_footprints
    exact ⟨state, _, programs, footprints, earlier, step, tail, grouped, flattened, decoded, compatible⟩

theorem Accepted.fork_kernel_interleavings_at {mir : Module} (accepted : Accepted mir)
    {start rest : List Op} {scope : Nat} {tasks : List Task}
    (cut : mir.operations = start ++ .fork scope tasks :: rest) :
    ∃ state next : Execution accepted.record, ∃ programs,
      Runs { memory := accepted.initial } start state ∧ Step state (.fork scope tasks) next ∧
      Runs next rest accepted.final ∧ tasksKernelPrograms scope state tasks = some programs ∧
      ∀ schedule, SourceVerification.TaskSchedule programs schedule →
        SourceVerification.KernelReadsAgree state.memory.heap programs schedule ∧ ∃ joined,
        Core.Runs state.memory.heap schedule joined ∧ joined.resources = state.memory.heap.resources ∧
        ∀ location, joined.byte location = next.memory.heap.byte location := by
  have ran := accepted.runs
  rw [cut] at ran
  obtain ⟨state, earlier, later⟩ := ran.split
  cases later with
  | cons step tail =>
    obtain ⟨programs, compiled, schedules⟩ := step.fork_kernel_interleavings
    exact ⟨state, _, programs, earlier, step, tail, compiled, schedules⟩

theorem Accepted.fork_kernel_sampling_at {mir : Module} (accepted : Accepted mir)
    {start rest : List Op} {scope : Nat} {tasks : List Task}
    (cut : mir.operations = start ++ .fork scope tasks :: rest) :
    ∃ state next : Execution accepted.record, ∃ programs,
      Runs { memory := accepted.initial } start state ∧ Step state (.fork scope tasks) next ∧
      Runs next rest accepted.final ∧ tasksKernelPrograms scope state tasks = some programs ∧
      ForkKernelSampling scope state tasks programs := by
  have ran := accepted.runs
  rw [cut] at ran
  obtain ⟨state, earlier, later⟩ := ran.split
  cases later with
  | cons step tail =>
    obtain ⟨programs, compiled, sampled⟩ := step.fork_kernel_sampling
    exact ⟨state, _, programs, earlier, step, tail, compiled, sampled⟩

theorem Runs.final_load {record : PackedRecord abi schema} {initial final : Execution record} {earlier : List Op}
    {scope closing : Nat} {path bytes : List Nat}
    (ran : Runs initial (earlier ++ [.load scope path bytes, .closeScope closing]) final)
    {image : Image record.layout.size}
    (represented : image.InAllocation record.owner final.memory.heap) :
    ∃ code, final.observations.head? = some code ∧ record.readImage image path = some code := by
  obtain ⟨state, _, remainder⟩ := ran.split
  cases remainder with
  | cons load rest =>
    cases load with
    | load span read =>
      cases rest with
      | cons close done =>
        cases close with
        | closeScope closed =>
          cases done
          have before := represented.of_allocations (PackedRecord.Memory.closeScope_allocations closed).symm
          exact ⟨_, rfl, PackedRecord.Memory.readInScope_on_image before read⟩

theorem Runs.final_payload_field {record : PackedRecord abi schema} {initial final : Execution record}
    {earlier : List Op} {scope id tag closing : Nat} {path bytes : List Nat} {steps : List PackedType.FieldStep}
    (ran : Runs initial (earlier ++ [.capturePayload scope id path bytes, .loadPayloadField scope id tag steps bytes,
      .forgetPayload id, .closeScope closing]) final)
    {image : Image record.layout.size} (represented : image.InAllocation record.owner final.memory.heap) :
    ∃ code ty whole, final.observations.head? = some code ∧ schema.typeAt path = some ty ∧
      record.readImage image path = some whole ∧ ty.projectTaggedCode tag whole steps = some code := by
  obtain ⟨state, _, remainder⟩ := ran.split
  cases remainder with
  | cons capture rest =>
    cases capture with
    | capturePayload fresh span opened =>
      cases rest with
      | cons load rest =>
        cases load with
        | loadPayloadField found span tagged read =>
          cases rest with
          | cons forget rest =>
            cases forget with
            | forgetPayload unused =>
              cases rest with
              | cons close done =>
                cases close with
                | closeScope closed =>
                  cases done
                  have before := represented.of_allocations (PackedRecord.Memory.closeScope_allocations closed).symm
                  simp only [Execution.payload?, List.find?_cons, BEq.rfl, Option.map_some] at found
                  cases found
                  have pathEq := PackedRecord.Memory.openPayloadInScope_path opened
                  obtain ⟨ty, whole, declared, loaded, result⟩ :=
                    PackedRecord.Memory.readPayloadFieldInScope_on_image before read
                  exact ⟨_, ty, whole, rfl, pathEq ▸ declared, pathEq ▸ loaded, tagged ▸ result⟩

theorem Accepted.field_addresses {mir : Module} (accepted : Accepted mir) {path : List Nat}
    {placement : Σ ty : PackedType, PackedValueField accepted.record.layout.size ty.width}
    (_located : accepted.record.field path = some placement) :
    ∃ addresses,
      (mir.target.region accepted.record.layout).addresses 0 placement.2 = some addresses ∧
      ∀ address ∈ addresses, address < mir.target.limit := by
  let region := mir.target.region accepted.record.layout
  let addresses := placement.2.byteOffsets.map (fun byte => region.rowBase 0 + byte)
  have resolved : region.addresses 0 placement.2 = some addresses :=
    (region.addresses_correct 0 placement.2 addresses).mpr
      ⟨accepted.targetFits, show 0 < 1 from by decide, rfl⟩
  exact ⟨addresses, resolved, fun address member => (region.addresses_within resolved member).2.2⟩

theorem Accepted.field_word_addresses {mir : Module} (accepted : Accepted mir) {path : List Nat}
    {placement : Σ ty : PackedType, PackedValueField accepted.record.layout.size ty.width} {wordBits : Nat}
    (located : accepted.record.field path = some placement) (limitFits : mir.target.limit < 2 ^ wordBits) :
    let region := mir.target.region accepted.record.layout
    ∃ addresses, region.addresses 0 placement.2 = some addresses ∧
      (placement.2.byteOffsets.map fun byte => (region.wordAddress wordBits 0 byte).toNat) = addresses := by
  obtain ⟨addresses, resolved, _⟩ := accepted.field_addresses located
  exact ⟨addresses, resolved, PackedArrayRegion.wordAddresses_exact resolved limitFits⟩

theorem Accepted.aligned_subvalue_address {mir : Module} (accepted : Accepted mir) {path : List Nat}
    {ty : PackedType} {field : PackedValueField accepted.record.layout.size ty.width}
    {offset alignment : Nat} (located : accepted.record.field path = some ⟨ty, field⟩)
    (required : ty.RequiresAddress offset alignment) :
    let address := mir.target.base + (field.start + offset) / 8
    address % alignment = 0 ∧ address ≤ mir.target.limit := by
  obtain ⟨_, baseMultiple, relativeMultiple, within⟩ := accepted.record.field_alignedSubvalue located required
  have rootAligned := Nat.dvd_trans (Nat.dvd_of_mod_eq_zero baseMultiple)
    (Nat.dvd_of_mod_eq_zero accepted.targetFits.2.2.1)
  obtain ⟨reps, coordinates⟩ := Nat.dvd_of_mod_eq_zero relativeMultiple
  have byteAligned : alignment ∣ (field.start + offset) / 8 := by
    exact ⟨reps, by rw [coordinates, Nat.mul_right_comm, Nat.mul_div_cancel _ (by decide)]⟩
  have bound := accepted.targetFits.2.2.2
  change mir.target.base + 1 * accepted.record.layout.size ≤ mir.target.limit at bound
  exact ⟨Nat.mod_eq_zero_of_dvd (Nat.dvd_add rootAligned byteAligned), by omega⟩

end Aethel.PackedMIR
