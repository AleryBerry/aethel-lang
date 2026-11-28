import Aethel.ScopedForkJoin

namespace Aethel.SourceVerification

open Core ScopedForkJoin

inductive TaskAccess (target : Type) where
  | read (place : target)
  | write (place : target) (value : UInt8)
  deriving Repr, DecidableEq

def TaskAccess.target : TaskAccess α → α
  | .read place | .write place _ => place

def TaskAccess.map (f : α → β) : TaskAccess α → TaskAccess β
  | .read place => .read (f place)
  | .write place value => .write (f place) value

/-- A task's byte accesses in program order. Each handle is named by its
field offset in the initialized record. -/
abbrev ByteTask := List (TaskAccess Nat)

def TaskAccess.instruction : TaskAccess Nat → Instruction
  | .read offset => .read offset
  | .write offset value => .write offset value

def TaskAccess.writtenOffset : TaskAccess Nat → Option Nat
  | .read _ => none
  | .write offset _ => some offset

def ByteTask.reads (task : ByteTask) : List Nat :=
  task.filterMap fun access => match access with
  | .read offset => some offset
  | .write _ _ => none

def ByteTask.writes (task : ByteTask) : List Nat :=
  task.filterMap TaskAccess.writtenOffset

def ByteTask.code (task : ByteTask) : Program :=
  task.map TaskAccess.instruction

def ByteTask.footprint (task : ByteTask) : TaskFootprint :=
  ⟨task.reads.map (⟨0, ·⟩), task.writes.map (⟨0, ·⟩)⟩

def ByteTask.check (task : ByteTask) (resources : ResourceState) : Bool :=
  task.all fun access => decide (checkInstruction resources access.instruction = some resources)

def TasksSeparated : List ByteTask → Prop
  | [] => True
  | task :: remaining =>
    ForkDisjoint task.footprint (ByteTask.footprint remaining.flatten) ∧ TasksSeparated remaining

/-- Gather the serial accesses and check each task against all other tasks.
Each task may access the same field more than once. -/
private def separatedTasks : List ByteTask → Option ByteTask
  | [] => some []
  | task :: remaining => do
    let tail ← separatedTasks remaining
    if checkForkDisjoint task.footprint tail.footprint then some (task ++ tail) else none

private theorem separatedTasks_correct (tasks : List ByteTask) (serial : ByteTask) :
    separatedTasks tasks = some serial ↔ serial = tasks.flatten ∧ TasksSeparated tasks := by
  induction tasks generalizing serial with
  | nil => simp [separatedTasks, TasksSeparated, eq_comm]
  | cons task remaining ih =>
    simp only [separatedTasks, bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
      Option.some.injEq, TasksSeparated, List.flatten_cons, ih, checkForkDisjoint_correct]
    constructor
    · rintro ⟨tail, ⟨rfl, separated⟩, disjoint, rfl⟩
      exact ⟨rfl, disjoint, separated⟩
    · rintro ⟨rfl, disjoint, separated⟩
      exact ⟨_, ⟨rfl, separated⟩, disjoint, rfl⟩

def checkTasks (tasks : List ByteTask) (resources : ResourceState) : Bool :=
  (separatedTasks tasks).any fun serial => serial.check resources

theorem checkTasks_correct (tasks : List ByteTask) (resources : ResourceState) :
    checkTasks tasks resources = true ↔
      TasksSeparated tasks ∧ ByteTask.check tasks.flatten resources = true := by
  simp only [checkTasks, Option.any_eq_true, separatedTasks_correct]
  constructor
  · rintro ⟨_, ⟨rfl, separated⟩, checked⟩
    exact ⟨separated, checked⟩
  · rintro ⟨separated, checked⟩
    exact ⟨_, ⟨rfl, separated⟩, checked⟩

/-- Interleavings retain the order of accesses within each task. -/
inductive TaskInterleave {α : Type u} : List α → List α → List α → Prop where
  | done : TaskInterleave [] [] []
  | left : TaskInterleave left right schedule → TaskInterleave (store :: left) right (store :: schedule)
  | right : TaskInterleave left right schedule → TaskInterleave left (store :: right) (store :: schedule)

theorem TaskInterleave.swap {left right schedule : List α}
    (ran : TaskInterleave left right schedule) : TaskInterleave right left schedule := by
  induction ran with
  | done => exact .done
  | left _ ih => exact .right ih
  | right _ ih => exact .left ih

theorem TaskInterleave.serial (left right : List α) :
    TaskInterleave left right (left ++ right) := by
  induction left with
  | nil =>
    induction right with
    | nil => exact .done
    | cons _ _ ih => exact .right ih
  | cons _ _ ih => exact .left ih

/-- A schedule interleaves one task with a schedule of the remaining tasks.
The relation records ordering within each task and permits every global
ordering that respects those task-local orders. -/
inductive TaskSchedule {α : Type u} : List (List α) → List α → Prop where
  | empty : TaskSchedule [] []
  | next : TaskSchedule remaining tail → TaskInterleave task tail ordered →
      TaskSchedule (task :: remaining) ordered

theorem TaskSchedule.serial (tasks : List (List α)) : TaskSchedule tasks tasks.flatten := by
  induction tasks with
  | nil => exact .empty
  | cons task remaining ih => exact .next ih (.serial task remaining.flatten)

private theorem TaskSchedule.all_empty {tasks : List (List α)}
    (empty : tasks.all List.isEmpty = true) : TaskSchedule tasks [] := by
  induction tasks with
  | nil => exact .empty
  | cons task rest ih =>
    obtain ⟨first, remaining⟩ := Bool.and_eq_true_iff.mp empty
    cases task with
    | nil => exact .next (ih remaining) .done
    | cons op tail => cases first

private theorem TaskSchedule.prepend_pick {tasks : List (List α)} {task : Nat} {next : α} {pending later : List α}
    (atIndex : tasks[task]? = some (next :: pending))
    (ordered : TaskSchedule (tasks.set task pending) later) : TaskSchedule tasks (next :: later) := by
  induction tasks generalizing task later with
  | nil => simp at atIndex
  | cons first rest ih =>
    cases task with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at atIndex
      subst first
      cases ordered with
      | next remaining interleaved => exact .next remaining (.left interleaved)
    | succ task =>
      cases ordered with
      | next remaining interleaved => exact .next (ih atIndex remaining) (.right interleaved)

/-- Each choice advances the selected task by one instruction. All tasks
must have finished when choices run out. -/
inductive PickedSchedule {α : Type u} : List (List α) → List Nat → List α → Prop where
  | done (exhausted : ∀ task ∈ tasks, task = []) : PickedSchedule tasks [] []
  | pick (selected : tasks[index]? = some (next :: pending))
      (rest : PickedSchedule (tasks.set index pending) picks schedule) :
      PickedSchedule tasks (index :: picks) (next :: schedule)

theorem PickedSchedule.order {tasks : List (List α)} {picks : List Nat} {schedule : List α}
    (chosen : PickedSchedule tasks picks schedule) : TaskSchedule tasks schedule := by
  induction chosen with
  | done exhausted =>
    apply TaskSchedule.all_empty (List.all_eq_true.mpr ?_)
    intro task member
    rw [exhausted task member]
    rfl
  | pick selected _ ih => exact TaskSchedule.prepend_pick selected ih

private theorem TaskInterleave.extend_picks {first tail schedule : List α} {tasks : List (List α)}
    {picks : List Nat} (interleaved : TaskInterleave first tail schedule)
    (chosen : PickedSchedule tasks picks tail) : ∃ choices, PickedSchedule (first :: tasks) choices schedule := by
  induction interleaved generalizing tasks picks with
  | done =>
    cases chosen with
    | done exhausted =>
      refine ⟨[], .done ?_⟩
      intro task member
      rcases List.mem_cons.mp member with rfl | later
      · rfl
      · exact exhausted task later
  | left _ ih =>
    obtain ⟨choices, combined⟩ := ih chosen
    exact ⟨0 :: choices, .pick rfl combined⟩
  | right _ ih =>
    cases chosen with
    | @pick tasks index op pending picks later selected rest =>
      obtain ⟨choices, combined⟩ := ih rest
      exact ⟨(index + 1) :: choices, .pick (index := index + 1) selected combined⟩

/-- Task indices describe all task-order-preserving interleavings. -/
theorem TaskSchedule.has_picks {tasks : List (List α)} {schedule : List α}
    (order : TaskSchedule tasks schedule) : ∃ picks, PickedSchedule tasks picks schedule := by
  induction order with
  | empty => exact ⟨[], .done (by simp)⟩
  | next _ interleaved ih =>
    obtain ⟨_, chosen⟩ := ih
    exact interleaved.extend_picks chosen

theorem TaskInterleave.perm_append {left right schedule : List α}
    (ran : TaskInterleave left right schedule) : schedule.Perm (left ++ right) := by
  induction ran with
  | done => exact .nil
  | left _ ih => exact ih.cons _
  | right _ ih => exact (ih.cons _).trans List.perm_middle.symm

theorem TaskSchedule.perm_flatten {tasks : List (List α)} {schedule : List α}
    (ordered : TaskSchedule tasks schedule) : schedule.Perm tasks.flatten := by
  induction ordered with
  | empty => exact .nil
  | next _ order ih => exact order.perm_append.trans (ih.append_left _)

private theorem TaskInterleave.focus_inner {first tail schedule task rest : List α}
    (outer : TaskInterleave first tail schedule) (inner : TaskInterleave task rest tail) :
    ∃ siblings, TaskInterleave first rest siblings ∧ TaskInterleave task siblings schedule := by
  induction outer generalizing task rest with
  | done =>
    cases inner
    exact ⟨[], .done, .done⟩
  | left _ ih =>
    obtain ⟨siblings, combined, focused⟩ := ih inner
    exact ⟨_ :: siblings, .left combined, .right focused⟩
  | right _ ih =>
    cases inner with
    | left ordered =>
      obtain ⟨siblings, combined, focused⟩ := ih ordered
      exact ⟨siblings, combined, .left focused⟩
    | right ordered =>
      obtain ⟨siblings, combined, focused⟩ := ih ordered
      exact ⟨_ :: siblings, .right combined, .right focused⟩

private theorem TaskSchedule.focus {earlier later : List (List α)} {task schedule : List α}
    (ordered : TaskSchedule (earlier ++ task :: later) schedule) :
    ∃ siblings, TaskSchedule (earlier ++ later) siblings ∧ TaskInterleave task siblings schedule := by
  induction earlier generalizing schedule with
  | nil =>
    cases ordered with
    | next remaining interleaved => exact ⟨_, remaining, interleaved⟩
  | cons first earlier ih =>
    cases ordered with
    | next remaining interleaved =>
      obtain ⟨_, remainder, focused⟩ := ih remaining
      obtain ⟨_, siblingOrder, taskOrder⟩ := interleaved.focus_inner focused
      exact ⟨_, .next remainder siblingOrder, taskOrder⟩

private theorem TaskInterleave.cut_left {left siblings schedule : List α}
    (ordered : TaskInterleave left siblings schedule) {start rest : List α} (parts : left = start ++ rest) :
    ∃ siblingStart siblingRest scheduledStart scheduledRest,
      siblings = siblingStart ++ siblingRest ∧ schedule = scheduledStart ++ scheduledRest ∧
      TaskInterleave start siblingStart scheduledStart ∧ TaskInterleave rest siblingRest scheduledRest := by
  induction ordered generalizing start rest with
  | done =>
    cases start <;> simp at parts
    subst rest
    exact ⟨[], [], [], [], rfl, rfl, .done, .done⟩
  | @left left siblings schedule head ordered ih =>
    cases start with
    | nil =>
      cases parts
      exact ⟨[], _, [], _, rfl, rfl, .done, .left ordered⟩
    | cons op start =>
      obtain ⟨sameHead, tailParts⟩ := List.cons.inj parts
      subst op
      obtain ⟨siblingStart, siblingRest, scheduledStart, scheduledRest, sibParts, scheduledParts, early, late⟩ :=
        ih tailParts
      exact ⟨siblingStart, siblingRest, head :: scheduledStart, scheduledRest, sibParts,
        congrArg (List.cons head) scheduledParts, .left early, late⟩
  | right ordered ih =>
    rename_i op
    obtain ⟨siblingStart, siblingRest, scheduledStart, scheduledRest, sibParts, scheduledParts, early, late⟩ := ih parts
    exact ⟨op :: siblingStart, siblingRest, op :: scheduledStart, scheduledRest,
      congrArg (List.cons op) sibParts, congrArg (List.cons op) scheduledParts, .right early, late⟩

private theorem TaskInterleave.split_at {left right earlier later : List α}
    (ordered : TaskInterleave left right (earlier ++ later)) :
    ∃ leftEarly leftLate rightEarly rightLate,
      left = leftEarly ++ leftLate ∧ right = rightEarly ++ rightLate ∧
      TaskInterleave leftEarly rightEarly earlier ∧ TaskInterleave leftLate rightLate later := by
  induction earlier generalizing left right with
  | nil => exact ⟨[], left, [], right, rfl, rfl, .done, ordered⟩
  | cons op earlier ih =>
    cases ordered with
    | left ordered =>
      obtain ⟨leftEarly, leftLate, rightEarly, rightLate, leftParts, rightParts, early, late⟩ := ih ordered
      exact ⟨op :: leftEarly, leftLate, rightEarly, rightLate,
        congrArg (List.cons op) leftParts, rightParts, .left early, late⟩
    | right ordered =>
      obtain ⟨leftEarly, leftLate, rightEarly, rightLate, leftParts, rightParts, early, late⟩ := ih ordered
      exact ⟨leftEarly, leftLate, op :: rightEarly, rightLate,
        leftParts, congrArg (List.cons op) rightParts, .right early, late⟩

private theorem TaskInterleave.append {left right ordered leftRest rightRest later : List α}
    (early : TaskInterleave left right ordered) (late : TaskInterleave leftRest rightRest later) :
    TaskInterleave (left ++ leftRest) (right ++ rightRest) (ordered ++ later) := by
  induction early with
  | done => exact late
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

/-- Attribute an instruction occurrence to its task and split both the task
and its siblings at that occurrence. -/
theorem TaskSchedule.cut {tasks : List (List α)} {schedule : List α} (ordered : TaskSchedule tasks schedule)
    {start rest : List α} {op : α} (cut : schedule = start ++ op :: rest) :
    ∃ earlier later taskStart taskRest siblingStart siblingRest,
      tasks = earlier ++ (taskStart ++ op :: taskRest) :: later ∧
      TaskSchedule (earlier ++ later) (siblingStart ++ siblingRest) ∧
      TaskInterleave taskStart siblingStart start ∧ TaskInterleave taskRest siblingRest rest := by
  induction ordered generalizing start rest with
  | empty => cases start <;> simp at cut
  | @next remaining tail first schedule _ order ih =>
    rw [cut] at order
    obtain ⟨firstStart, firstRest, tailStart, tailRest, firstParts, tailParts, begun, continues⟩ := order.split_at
    cases continues with
    | left suffix =>
      exact ⟨[], remaining, firstStart, _, tailStart, _, by simp [firstParts],
        by simpa only [List.nil_append, ← tailParts] using ‹TaskSchedule remaining tail›, begun, suffix⟩
    | right suffix =>
      obtain ⟨earlier, later, taskStart, taskRest, siblingStart, siblingRest,
        location, siblings, started, continued⟩ := ih tailParts
      obtain ⟨shadowStart, siblingBegin, taskBegin⟩ := begun.focus_inner started
      obtain ⟨shadowRest, siblingContinue, taskContinue⟩ := suffix.focus_inner continued
      have composite := siblingBegin.append siblingContinue
      rw [← firstParts] at composite
      exact ⟨first :: earlier, later, taskStart, taskRest, shadowStart, shadowRest,
        by simp [location], .next siblings composite, taskBegin, taskContinue⟩

private theorem TaskSchedule.members {tasks : List ByteTask} {schedule : ByteTask}
    (ordered : TaskSchedule tasks schedule) {store : TaskAccess Nat} (member : store ∈ schedule) :
    store ∈ tasks.flatten := ordered.perm_flatten.mem_iff.mp member

/-- Samples of an attributed read-only task prefix. Sibling instructions
execute on the same machine but do not enter the task's sample list. -/
inductive InterleavedReadSamples : State → Program → Program → Program → List (BitVec 8) → State → Prop where
  | nil : InterleavedReadSamples state [] [] [] [] state
  | task (step : Step state op (state.observe value))
      (address : op.byteAccess state.resources = some (.read location))
      (live : state.byte location = some value)
      (tail : InterleavedReadSamples (state.observe value) task siblings schedule samples final) :
      InterleavedReadSamples state (op :: task) siblings (op :: schedule) (value.toBitVec :: samples) final
  | sibling (step : Step state op next) (access : op.isByteAccess = true)
      (tail : InterleavedReadSamples next task siblings schedule samples final) :
      InterleavedReadSamples state task (op :: siblings) (op :: schedule) samples final

theorem TaskInterleave.read_samples {state final : State} {task siblings schedule : Program}
    (ordered : TaskInterleave task siblings schedule) (ran : Runs state schedule final)
    (accesses : schedule.all Instruction.isByteAccess = true)
    (reads : ∀ op ∈ task, ∃ location, op.byteAccess state.resources = some (.read location)) :
    ∃ samples, InterleavedReadSamples state task siblings schedule samples final := by
  induction ordered generalizing state final with
  | done => cases ran; exact ⟨[], .nil⟩
  | left _ ih =>
    cases ran with
    | cons step tail =>
      obtain ⟨_, rest⟩ := Bool.and_eq_true_iff.mp accesses
      obtain ⟨_, decoded⟩ := reads _ List.mem_cons_self
      obtain ⟨value, live, rfl⟩ := step.refines_byteAccess decoded
      obtain ⟨samples, observed⟩ := ih tail rest (fun op member => reads op (List.mem_cons_of_mem _ member))
      exact ⟨value.toBitVec :: samples, .task step decoded live observed⟩
  | right _ ih =>
    cases ran with
    | cons step tail =>
      obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp accesses
      obtain ⟨samples, observed⟩ := ih tail rest (by rwa [step.resources_of_byteAccess first])
      exact ⟨samples, .sibling step first observed⟩

theorem InterleavedReadSamples.eq_entry_samples {state final : State} {task siblings schedule : Program}
    {samples : List (BitVec 8)} (observed : InterleavedReadSamples state task siblings schedule samples final)
    (stable : ∀ op ∈ task, ∀ location, op.byteAccess state.resources = some (.read location) →
      ∀ sibling ∈ siblings, sibling.writeValueAt state.resources location = none) :
    task.mapM (Instruction.readSample state) = some samples := by
  induction observed with
  | nil => rfl
  | @task state op value location task siblings schedule samples final step address live _ ih =>
    have rest : task.mapM (Instruction.readSample state) = some samples :=
      ih (fun op member => stable op (List.mem_cons_of_mem _ member))
    simp [List.mapM_cons, Instruction.readSample, ByteAccess.readSample, address, live, rest, bind, pure]
  | @sibling state op next task siblings schedule samples final step access _ ih =>
    have resources := step.resources_of_byteAccess access
    have unchanged : task.mapM (Instruction.readSample state) = task.mapM (Instruction.readSample next) := by
      apply mapM_eq_of_mem
      intro read member
      unfold Instruction.readSample
      rw [resources]
      cases decoded : read.byteAccess state.resources with
      | none => rfl
      | some event =>
        cases event with
        | write _ _ => rfl
        | read location =>
          have effect := step.byte_after_access access location
          rw [stable read member location decoded op List.mem_cons_self] at effect
          simpa [ByteAccess.readSample, Option.or] using congrArg (Option.map UInt8.toBitVec) effect.symm
    rw [unchanged]
    apply ih
    rw [resources]
    exact fun read member location decoded sibling present =>
      stable read member location decoded sibling (List.mem_cons_of_mem _ present)

/-- Collect all reads of one task prefix from an order-preserving schedule.
Their sequence equals a snapshot of those read locations at fork entry. -/
theorem TaskSchedule.read_block_samples {earlier later : List Program} {reads rest schedule : Program}
    {state final : State} {footprints : List TaskFootprint}
    (ordered : TaskSchedule (earlier ++ (reads ++ rest) :: later) schedule)
    (ran : Runs state schedule final) (accesses : schedule.all Instruction.isByteAccess = true)
    (decoded : (earlier ++ (reads ++ rest) :: later).mapM (TaskFootprint.ofProgram state.resources) = some footprints)
    (compatible : footprints.Pairwise ForkDisjoint)
    (readable : ∀ op ∈ reads, ∃ location, op.byteAccess state.resources = some (.read location)) :
    ∃ started remaining siblingStart siblingRest observed samples, schedule = started ++ remaining ∧
      TaskSchedule (earlier ++ later) (siblingStart ++ siblingRest) ∧
      InterleavedReadSamples state reads siblingStart started samples observed ∧
      TaskInterleave rest siblingRest remaining ∧
      reads.mapM (Instruction.readSample state) = some samples := by
  obtain ⟨siblingTrace, siblingOrder, focused⟩ := ordered.focus
  obtain ⟨siblingStart, siblingRest, started, remaining, sibParts, cut, early, late⟩ :=
    focused.cut_left (start := reads) rfl
  have executed := run_complete ran
  rw [cut, run_append, Option.bind_eq_some_iff] at executed
  obtain ⟨observed, ranEarly, _⟩ := executed
  have onlyBytes := (Bool.and_eq_true_iff.mp (List.all_append ▸ (cut ▸ accesses))).1
  obtain ⟨samples, sampled⟩ := early.read_samples (run_sound ranEarly) onlyBytes readable
  refine ⟨started, remaining, siblingStart, siblingRest, observed, samples, cut, sibParts ▸ siblingOrder,
    sampled, late, sampled.eq_entry_samples ?_⟩
  intro op readMember location address sibling before
  have inTrace : sibling ∈ siblingTrace := by
    rw [sibParts]
    exact List.mem_append_left _ before
  obtain ⟨siblingTask, present, inTask⟩ := List.mem_flatten.mp (siblingOrder.perm_flatten.mem_iff.mp inTrace)
  have noWrite := TaskFootprint.siblings_do_not_write_reads decoded compatible
    (List.mem_append_left _ readMember) address present
  exact List.filterMap_eq_nil_iff.mp noWrite sibling inTask

theorem ByteTask.check_code {task : ByteTask} {resources : ResourceState}
    (checked : task.check resources = true) : checkResources resources task.code = some resources := by
  induction task with
  | nil => rfl
  | cons head tail ih =>
    simp only [ByteTask.check, List.all_cons, Bool.and_eq_true] at checked
    simpa [ByteTask.code, checkResources, of_decide_eq_true checked.1] using ih checked.2

theorem TaskSchedule.checked {tasks : List ByteTask} {schedule : ByteTask}
    {resources : ResourceState} (ordered : TaskSchedule tasks schedule)
    (fork : checkTasks tasks resources = true) : checkResources resources schedule.code = some resources := by
  have stores := ((checkTasks_correct _ _).mp fork).2
  exact ByteTask.check_code (List.all_eq_true.mpr fun store member =>
    List.all_eq_true.mp stores store (ordered.members member))

/-- The record's handles name the byte at their field offset. -/
def RecordAddresses (state : State) : Prop :=
  ∀ id handle, state.handle id = some handle → handle.location = ⟨0, id⟩

theorem TaskSchedule.executes {tasks : List ByteTask} {schedule : ByteTask} {state : State}
    (ordered : TaskSchedule tasks schedule) (fork : checkTasks tasks state.resources = true) :
    ∃ final, Runs state schedule.code final ∧ final.resources = state.resources := by
  have checked := ordered.checked fork
  rw [checkResources_correct, Option.map_eq_some_iff] at checked
  obtain ⟨final, executed, restored⟩ := checked
  exact ⟨final, Core.run_sound executed, restored⟩

private def TaskAccess.valueAt (location : ByteLocation) : TaskAccess Nat → Option UInt8
  | .read _ => none
  | .write offset value => if location = ⟨0, offset⟩ then some value else none

private def ByteTask.writesAt (location : ByteLocation) (task : ByteTask) : List UInt8 :=
  task.filterMap (TaskAccess.valueAt location)

private theorem ByteTask.none_at {location : ByteLocation} {task : ByteTask}
    (outside : location ∉ task.footprint.writes) : task.writesAt location = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro access member
  cases access with
  | read offset => rfl
  | write offset value =>
    have present : offset ∈ task.writes := List.mem_filterMap.mpr ⟨.write offset value, member, rfl⟩
    have different : location ≠ ⟨0, offset⟩ := fun equal =>
      outside (equal ▸ List.mem_map_of_mem present)
    simp [TaskAccess.valueAt, different]

theorem TaskInterleave.filterMap_left {left right schedule : List α} {select : α → Option β}
    (ran : TaskInterleave left right schedule) (outside : right.filterMap select = []) :
    schedule.filterMap select = left.filterMap select := by
  induction ran with
  | done => rfl
  | left _ ih =>
    simp only [List.filterMap_cons]
    rw [ih outside]
  | right _ ih =>
    rename_i _ _ _ store _
    cases value : select store with
    | none =>
      simp only [List.filterMap_cons, value] at outside ⊢
      exact ih outside
    | some entry => simp [value] at outside

/-- If at most one task contains selected events, every schedule keeps their
order and multiplicity from the serial task list. -/
theorem TaskSchedule.filterMap_eq_flatten {tasks : List (List α)} {schedule : List α}
    {select : α → Option β} (ordered : TaskSchedule tasks schedule)
    (unique : tasks.Pairwise (fun a b => a.filterMap select = [] ∨ b.filterMap select = [])) :
    schedule.filterMap select = tasks.flatten.filterMap select := by
  induction ordered with
  | empty => rfl
  | @next remaining tail task schedule _ interleaved ih =>
    obtain ⟨apart, rest⟩ := List.pairwise_cons.mp unique
    have tailAgrees := ih rest
    rw [List.flatten_cons, List.filterMap_append]
    by_cases outside : task.filterMap select = []
    · rw [outside, List.nil_append, interleaved.swap.filterMap_left outside, tailAgrees]
    · have onlyHead : remaining.flatten.filterMap select = [] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro entry member
        obtain ⟨other, otherMember, inOther⟩ := List.mem_flatten.mp member
        exact List.filterMap_eq_nil_iff.mp ((apart other otherMember).resolve_left outside) entry inOther
      rw [onlyHead, List.append_nil, interleaved.filterMap_left (tailAgrees.trans onlyHead)]

theorem TaskSchedule.kernel_byte_agreement {tasks : List Program} {schedule : Program}
    {state scheduled serial : State} {footprints : List TaskFootprint}
    (ordered : TaskSchedule tasks schedule) (serialRun : Runs state tasks.flatten serial)
    (scheduledRun : Runs state schedule scheduled)
    (accesses : tasks.flatten.all Instruction.isByteAccess = true)
    (decoded : tasks.mapM (TaskFootprint.ofProgram state.resources) = some footprints)
    (compatible : footprints.Pairwise ForkDisjoint) (location : ByteLocation) :
    scheduled.byte location = serial.byte location := by
  have scheduledAccesses := List.all_eq_true.mpr fun op member =>
    List.all_eq_true.mp accesses op (ordered.perm_flatten.mem_iff.mp member)
  rw [scheduledRun.byte_after_accesses scheduledAccesses, serialRun.byte_after_accesses accesses,
    ordered.filterMap_eq_flatten (TaskFootprint.pairwise_writeValuesAt decoded compatible location)]

private theorem TaskInterleave.kernel_read_of_noSiblingWrite {reader sibling schedule : Program}
    {state isolated scheduled observed : State} {op : Instruction} {location : ByteLocation}
    (ordered : TaskInterleave reader sibling schedule)
    (readerRun : Runs state reader isolated) (scheduledRun : Runs state schedule scheduled)
    (accesses : (reader ++ sibling).all Instruction.isByteAccess = true)
    (noWrites : sibling.filterMap (Instruction.writeValueAt state.resources location) = [])
    (read : op.byteAccess state.resources = some (.read location))
    (step : Step scheduled op observed) :
    ∃ value, isolated.byte location = some value ∧ observed = scheduled.observe value := by
  have readerAccesses : reader.all Instruction.isByteAccess = true :=
    (Bool.and_eq_true_iff.mp (List.all_append ▸ accesses)).1
  have scheduledAccesses := List.all_eq_true.mpr fun op member =>
    List.all_eq_true.mp accesses op (ordered.perm_append.mem_iff.mp member)
  have sameByte : scheduled.byte location = isolated.byte location := by
    rw [scheduledRun.byte_after_accesses scheduledAccesses, readerRun.byte_after_accesses readerAccesses,
      ordered.filterMap_left noWrites]
  have currentRead : op.byteAccess scheduled.resources = some (.read location) := by
    rwa [scheduledRun.resources_of_byteAccesses scheduledAccesses]
  simpa only [ByteAccess.Effect, sameByte] using step.refines_byteAccess currentRead

/-- A read after an interleaved prefix sees the byte from the reader's own
prefix whenever sibling writes exclude that byte. -/
theorem TaskInterleave.kernel_read_at_cut {reader sibling schedule : Program}
    {state isolated scheduled observed : State} {op : Instruction} {location : ByteLocation}
    {footprint : TaskFootprint} (ordered : TaskInterleave reader sibling schedule)
    (readerRun : Runs state reader isolated) (scheduledRun : Runs state schedule scheduled)
    (accesses : (reader ++ sibling).all Instruction.isByteAccess = true)
    (decoded : TaskFootprint.ofProgram state.resources sibling = some footprint)
    (outside : location ∉ footprint.writes) (read : op.byteAccess state.resources = some (.read location))
    (step : Step scheduled op observed) :
    ∃ value, isolated.byte location = some value ∧ observed = scheduled.observe value :=
  ordered.kernel_read_of_noSiblingWrite readerRun scheduledRun accesses
    (TaskFootprint.writeValuesAt_empty decoded outside) read step

def KernelReadsAgree (state : State) (tasks : List Program) (schedule : Program) : Prop :=
  ∀ {start rest : Program} {op : Instruction} {location : ByteLocation} {before after : State},
    schedule = start ++ op :: rest → Runs state start before → Step before op after →
    op.byteAccess state.resources = some (.read location) →
    ∃ earlier later taskStart taskRest siblingStart siblingRest,
      tasks = earlier ++ (taskStart ++ op :: taskRest) :: later ∧
      TaskSchedule (earlier ++ later) (siblingStart ++ siblingRest) ∧
      TaskInterleave taskStart siblingStart start ∧ TaskInterleave taskRest siblingRest rest ∧
      ∃ isolated value, Runs state taskStart isolated ∧ isolated.byte location = some value ∧
        after = before.observe value

theorem TaskSchedule.kernel_reads_agree {tasks : List Program} {schedule : Program}
    {state serial : State} {footprints : List TaskFootprint}
    (ordered : TaskSchedule tasks schedule) (serialRun : Runs state tasks.flatten serial)
    (accesses : tasks.flatten.all Instruction.isByteAccess = true)
    (decoded : tasks.mapM (TaskFootprint.ofProgram state.resources) = some footprints)
    (compatible : footprints.Pairwise ForkDisjoint) : KernelReadsAgree state tasks schedule := by
  intro start rest op location before after cut ranPrefix step read
  obtain ⟨earlier, later, taskStart, taskRest, sibStart, sibRest, taskParts, siblings, early, late⟩ := ordered.cut cut
  have taskMember : (taskStart ++ op :: taskRest) ∈ tasks := by
    rw [taskParts]
    exact List.mem_append_right _ List.mem_cons_self
  have readMember : op ∈ taskStart ++ op :: taskRest := List.mem_append_right _ List.mem_cons_self
  have noSiblingWrites : sibStart.filterMap (Instruction.writeValueAt state.resources location) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro instruction inPrefix
    have inSiblings := siblings.perm_flatten.mem_iff.mp (List.mem_append_left _ inPrefix)
    obtain ⟨sibling, present, inSibling⟩ := List.mem_flatten.mp inSiblings
    have noWrite := TaskFootprint.siblings_do_not_write_reads (taskParts ▸ decoded) compatible readMember read present
    exact List.filterMap_eq_nil_iff.mp noWrite instruction inSibling
  obtain ⟨isolated, isolatedRun, _⟩ := serialRun.replay_byteAccesses (replay := taskStart) accesses
    (fun _ member => List.mem_flatten_of_mem taskMember (List.mem_append_left _ member))
  have prefixAccesses := List.all_eq_true.mpr fun instruction member => by
    have scheduled : instruction ∈ schedule := by
      rw [cut]
      exact List.mem_append_left _ (early.perm_append.mem_iff.mpr member)
    exact List.all_eq_true.mp accesses instruction (ordered.perm_flatten.mem_iff.mp scheduled)
  obtain ⟨value, sampled, observed⟩ := early.kernel_read_of_noSiblingWrite
    isolatedRun ranPrefix prefixAccesses noSiblingWrites read step
  exact ⟨earlier, later, taskStart, taskRest, sibStart, sibRest, taskParts, siblings, early, late,
    isolated, value, isolatedRun, sampled, observed⟩

private theorem TaskInterleave.keeps_writesAt {left right schedule : ByteTask}
    (ran : TaskInterleave left right schedule) {location : ByteLocation}
    (outside : right.writesAt location = []) :
    schedule.writesAt location = left.writesAt location := ran.filterMap_left outside

private theorem TaskSchedule.writesAt_agrees {tasks : List ByteTask} {schedule : ByteTask}
    (ordered : TaskSchedule tasks schedule) (separated : TasksSeparated tasks) (location : ByteLocation) :
    schedule.writesAt location = ByteTask.writesAt location tasks.flatten := by
  induction ordered with
  | empty => rfl
  | @next remaining tail task ordered _ interleaved ih =>
    have agrees := ih separated.2
    have combined : ByteTask.writesAt location (task :: remaining).flatten =
        ByteTask.writesAt location task ++ ByteTask.writesAt location remaining.flatten := by
      simp only [List.flatten_cons, ByteTask.writesAt, List.filterMap_append]
    rw [combined]
    by_cases written : location ∈ (ByteTask.footprint task).writes
    · have outside := ByteTask.none_at (separated.1.1 location written).2
      rw [outside, List.append_nil, interleaved.keeps_writesAt (agrees.trans outside)]
    · have outside := ByteTask.none_at written
      rw [outside, List.nil_append, interleaved.swap.keeps_writesAt outside, agrees]

private theorem ByteTask.executes_writesAt {task : ByteTask} {state final : State}
    (addresses : RecordAddresses state) (ran : Runs state task.code final) (location : ByteLocation) :
    final.byte location = (task.writesAt location).foldl (fun _ value => some value) (state.byte location) := by
  induction task generalizing state with
  | nil =>
    cases ran
    rfl
  | cons head tail ih =>
    cases ran with
    | cons first rest =>
      cases head with
      | read offset =>
        cases first
        have tailFrame := @ih _ (by exact addresses) rest
        exact tailFrame
      | write offset value =>
        cases first with
        | write handle live _ _ =>
          have same := addresses offset _ handle
          rw [ih (by exact addresses) rest]
          simp only [ByteTask.writesAt, List.filterMap_cons, TaskAccess.valueAt]
          by_cases atLocation : location = ⟨0, offset⟩
          · simp only [atLocation, ite_true, List.foldl_cons]
            rw [← same, State.store_byte_written _ _ _ _ live]
          · simp only [ite_eq_right atLocation]
            rw [State.store_byte_other _ _ _ _ (fun eq => atLocation (eq.symm.trans same))]

theorem ByteTask.handles_preserved {task : ByteTask} {state final : State}
    (ran : Runs state task.code final) : final.handles = state.handles := by
  induction task generalizing state with
  | nil =>
    cases ran
    rfl
  | cons head tail ih =>
    cases ran with
    | cons first continued =>
      cases head <;> cases first <;> have preserved := @ih _ continued <;> exact preserved

theorem ByteTask.frames_byte {task : ByteTask} {state final : State}
    (addresses : RecordAddresses state) (ran : Runs state task.code final)
    {offset : Nat} (outside : offset ∉ task.writes) :
    final.byte ⟨0, offset⟩ = state.byte ⟨0, offset⟩ := by
  have untouched : (⟨0, offset⟩ : ByteLocation) ∉ task.footprint.writes := by
    intro wrote
    obtain ⟨store, member, location⟩ := List.mem_map.mp wrote
    have same : store = offset := congrArg ByteLocation.offset location
    exact outside (same ▸ member)
  simp only [ByteTask.executes_writesAt addresses ran, ByteTask.none_at untouched, List.foldl_nil]

theorem ByteTask.sibling_read_stable {reader sibling : ByteTask} {state final : State} {offset : Nat}
    (apart : ForkDisjoint reader.footprint sibling.footprint) (read : offset ∈ reader.reads)
    (roots : RecordAddresses state) (ran : Runs state sibling.code final) :
    final.byte ⟨0, offset⟩ = state.byte ⟨0, offset⟩ := by
  apply ByteTask.frames_byte roots ran
  intro written
  exact (apart.2 ⟨0, offset⟩ (List.mem_map_of_mem written)).1 (List.mem_map_of_mem read)

/-- Immediately before a reader's next access, an interleaved prefix exposes
the same byte as the reader's own prefix run in isolation. -/
theorem TaskInterleave.read_at_cut {reader sibling schedule : ByteTask} {state scheduled isolated : State}
    {offset : Nat} (order : TaskInterleave reader sibling schedule)
    (apart : ForkDisjoint (ByteTask.footprint (reader ++ [.read offset])) sibling.footprint)
    (roots : RecordAddresses state) (runSchedule : Runs state schedule.code scheduled)
    (runReader : Runs state reader.code isolated) :
    scheduled.byte ⟨0, offset⟩ = isolated.byte ⟨0, offset⟩ := by
  have reads : offset ∈ ByteTask.reads (reader ++ [.read offset]) := by
    simp [ByteTask.reads, List.filterMap_append]
  have outside : (⟨0, offset⟩ : ByteLocation) ∉ sibling.footprint.writes :=
    fun written => (apart.2 _ written).1 (List.mem_map_of_mem reads)
  rw [ByteTask.executes_writesAt roots runSchedule, ByteTask.executes_writesAt roots runReader,
    order.keeps_writesAt (ByteTask.none_at outside)]

/-- Every legal interleaving has the same byte contents. A task may repeat an
access to its own field, and each schedule retains the parent resources. -/
theorem task_schedule_deterministic {tasks : List ByteTask} {first second : ByteTask}
    {state firstFinal secondFinal : State} {resources : ResourceState}
    (checked : checkTasks tasks resources = true) (addresses : RecordAddresses state)
    (order1 : TaskSchedule tasks first) (order2 : TaskSchedule tasks second)
    (run1 : Runs state first.code firstFinal) (run2 : Runs state second.code secondFinal) :
    ∀ location, firstFinal.byte location = secondFinal.byte location := by
  have separated := ((checkTasks_correct _ _).mp checked).1
  intro location
  rw [ByteTask.executes_writesAt addresses run1, ByteTask.executes_writesAt addresses run2,
    order1.writesAt_agrees separated, order2.writesAt_agrees separated]

end Aethel.SourceVerification
