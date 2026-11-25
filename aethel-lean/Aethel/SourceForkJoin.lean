import Aethel.ScopedForkJoin

namespace Aethel.SourceVerification

open Core ScopedForkJoin

/-- A task's primitive stores in program order. The field handle is its
offset in the initialized byte record. -/
abbrev StoreTask := List (Nat × UInt8)

def StoreTask.code (task : StoreTask) : Program :=
  task.map fun (offset, value) => .write offset value

def StoreTask.footprint (task : StoreTask) : TaskFootprint :=
  ⟨[], task.map fun (offset, _) => ⟨0, offset⟩⟩

def StoreTask.check (task : StoreTask) (resources : ResourceState) : Bool :=
  task.all fun (offset, value) => decide (checkInstruction resources (.write offset value) = some resources)

def StoreTasksSeparated : List StoreTask → Prop
  | [] => True
  | task :: remaining =>
    ForkDisjoint task.footprint (StoreTask.footprint remaining.flatten) ∧ StoreTasksSeparated remaining

/-- Gather the serial stores and check each task against all other tasks.
Stores inside a task keep their original order and may repeat a field. -/
private def separatedStores : List StoreTask → Option StoreTask
  | [] => some []
  | task :: remaining => do
    let tail ← separatedStores remaining
    if checkForkDisjoint task.footprint tail.footprint then some (task ++ tail) else none

private theorem separatedStores_correct (tasks : List StoreTask) (serial : StoreTask) :
    separatedStores tasks = some serial ↔ serial = tasks.flatten ∧ StoreTasksSeparated tasks := by
  induction tasks generalizing serial with
  | nil => simp [separatedStores, StoreTasksSeparated, eq_comm]
  | cons task remaining ih =>
    simp only [separatedStores, bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
      Option.some.injEq, StoreTasksSeparated, List.flatten_cons, ih, checkForkDisjoint_correct]
    constructor
    · rintro ⟨tail, ⟨rfl, separated⟩, disjoint, rfl⟩
      exact ⟨rfl, disjoint, separated⟩
    · rintro ⟨rfl, disjoint, separated⟩
      exact ⟨_, ⟨rfl, separated⟩, disjoint, rfl⟩

def checkStoreTasks (tasks : List StoreTask) (resources : ResourceState) : Bool :=
  (separatedStores tasks).any fun serial => serial.check resources

theorem checkStoreTasks_correct (tasks : List StoreTask) (resources : ResourceState) :
    checkStoreTasks tasks resources = true ↔
      StoreTasksSeparated tasks ∧ StoreTask.check tasks.flatten resources = true := by
  simp only [checkStoreTasks, Option.any_eq_true, separatedStores_correct]
  constructor
  · rintro ⟨_, ⟨rfl, separated⟩, checked⟩
    exact ⟨separated, checked⟩
  · rintro ⟨separated, checked⟩
    exact ⟨_, ⟨rfl, separated⟩, checked⟩

/-- Interleavings retain the order of stores within each task. -/
inductive StoreInterleave : StoreTask → StoreTask → StoreTask → Prop where
  | done : StoreInterleave [] [] []
  | left : StoreInterleave left right schedule → StoreInterleave (store :: left) right (store :: schedule)
  | right : StoreInterleave left right schedule → StoreInterleave left (store :: right) (store :: schedule)

theorem StoreInterleave.swap {left right schedule : StoreTask}
    (ran : StoreInterleave left right schedule) : StoreInterleave right left schedule := by
  induction ran with
  | done => exact .done
  | left _ ih => exact .right ih
  | right _ ih => exact .left ih

theorem StoreInterleave.serial (left right : StoreTask) :
    StoreInterleave left right (left ++ right) := by
  induction left with
  | nil =>
    induction right with
    | nil => exact .done
    | cons _ _ ih => exact .right ih
  | cons _ _ ih => exact .left ih

/-- A schedule interleaves one task with a schedule of the remaining tasks.
The relation records ordering within each task and permits every global
ordering that respects those task-local orders. -/
inductive StoreSchedule : List StoreTask → StoreTask → Prop where
  | empty : StoreSchedule [] []
  | next : StoreSchedule remaining tail → StoreInterleave task tail ordered →
      StoreSchedule (task :: remaining) ordered

theorem StoreSchedule.serial (tasks : List StoreTask) : StoreSchedule tasks tasks.flatten := by
  induction tasks with
  | nil => exact .empty
  | cons task remaining ih => exact .next ih (.serial task remaining.flatten)

private theorem StoreInterleave.members {left right schedule : StoreTask}
    (ran : StoreInterleave left right schedule) {store : Nat × UInt8} (member : store ∈ schedule) :
    store ∈ left ∨ store ∈ right := by
  induction ran with
  | done => cases member
  | left _ ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact .inl List.mem_cons_self
    · exact (ih tail).imp (List.mem_cons_of_mem _) id
  | right _ ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact .inr List.mem_cons_self
    · exact (ih tail).imp id (List.mem_cons_of_mem _)

private theorem StoreSchedule.members {tasks : List StoreTask} {schedule : StoreTask}
    (ordered : StoreSchedule tasks schedule) {store : Nat × UInt8} (member : store ∈ schedule) :
    store ∈ tasks.flatten := by
  induction ordered with
  | empty => exact member
  | next _ order ih =>
    exact List.mem_append.mpr ((order.members member).imp id ih)

theorem StoreTask.check_code {task : StoreTask} {resources : ResourceState}
    (checked : task.check resources = true) : checkResources resources task.code = some resources := by
  induction task with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨offset, value⟩ := head
    simp only [StoreTask.check, List.all_cons, Bool.and_eq_true] at checked
    simpa [StoreTask.code, checkResources, of_decide_eq_true checked.1] using ih checked.2

theorem StoreSchedule.checked {tasks : List StoreTask} {schedule : StoreTask}
    {resources : ResourceState} (ordered : StoreSchedule tasks schedule)
    (fork : checkStoreTasks tasks resources = true) : checkResources resources schedule.code = some resources := by
  have stores := ((checkStoreTasks_correct _ _).mp fork).2
  exact StoreTask.check_code (List.all_eq_true.mpr fun store member =>
    List.all_eq_true.mp stores store (ordered.members member))

/-- The record's handles name the byte at their field offset. -/
def RecordAddresses (state : State) : Prop :=
  ∀ id handle, state.handle id = some handle → handle.location = ⟨0, id⟩

theorem StoreSchedule.executes {tasks : List StoreTask} {schedule : StoreTask} {state : State}
    (ordered : StoreSchedule tasks schedule) (fork : checkStoreTasks tasks state.resources = true) :
    ∃ final, Runs state schedule.code final ∧ final.resources = state.resources := by
  have checked := ordered.checked fork
  rw [checkResources_correct, Option.map_eq_some_iff] at checked
  obtain ⟨final, executed, restored⟩ := checked
  exact ⟨final, Core.run_sound executed, restored⟩

private def StoreTask.writesAt (location : ByteLocation) (task : StoreTask) : List UInt8 :=
  task.filterMap fun (offset, value) => if location = ⟨0, offset⟩ then some value else none

private theorem StoreTask.none_at {location : ByteLocation} {task : StoreTask}
    (outside : location ∉ task.footprint.writes) : task.writesAt location = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro store member
  obtain ⟨offset, value⟩ := store
  have different : location ≠ ⟨0, offset⟩ := fun equal =>
    outside (equal ▸ List.mem_map.mpr ⟨(offset, value), member, rfl⟩)
  simp [different]

private theorem StoreInterleave.keeps_writesAt {left right schedule : StoreTask}
    (ran : StoreInterleave left right schedule) {location : ByteLocation}
    (outside : right.writesAt location = []) :
    schedule.writesAt location = left.writesAt location := by
  induction ran with
  | done => rfl
  | left _ ih =>
    simp only [StoreTask.writesAt, List.filterMap_cons] at ih ⊢
    rw [ih outside]
  | right _ ih =>
    rename_i _ _ _ store _
    obtain ⟨offset, value⟩ := store
    by_cases touches : location = ⟨0, offset⟩
    · simp [StoreTask.writesAt, touches] at outside
    · simp only [StoreTask.writesAt, List.filterMap_cons, ite_eq_right touches] at outside ⊢
      exact ih outside

private theorem StoreSchedule.writesAt_agrees {tasks : List StoreTask} {schedule : StoreTask}
    (ordered : StoreSchedule tasks schedule) (separated : StoreTasksSeparated tasks) (location : ByteLocation) :
    schedule.writesAt location = StoreTask.writesAt location tasks.flatten := by
  induction ordered with
  | empty => rfl
  | @next remaining tail task ordered _ interleaved ih =>
    have agrees := ih separated.2
    have combined : StoreTask.writesAt location (task :: remaining).flatten =
        task.writesAt location ++ StoreTask.writesAt location remaining.flatten := by
      simp only [List.flatten_cons, StoreTask.writesAt, List.filterMap_append]
    rw [combined]
    by_cases written : location ∈ task.footprint.writes
    · have outside := StoreTask.none_at (separated.1.1 location written).2
      rw [outside, List.append_nil, interleaved.keeps_writesAt (agrees.trans outside)]
    · have outside := StoreTask.none_at written
      rw [outside, List.nil_append, interleaved.swap.keeps_writesAt outside, agrees]

private theorem StoreTask.executes_writesAt {task : StoreTask} {state final : State}
    (addresses : RecordAddresses state) (ran : Runs state task.code final) (location : ByteLocation) :
    final.byte location = (task.writesAt location).foldl (fun _ value => some value) (state.byte location) := by
  induction task generalizing state with
  | nil =>
    cases ran
    rfl
  | cons head tail ih =>
    obtain ⟨offset, value⟩ := head
    cases ran with
    | cons write rest =>
      cases write with
      | write handle live _ _ =>
        have same := addresses offset _ handle
        rw [ih (by exact addresses) rest]
        simp only [StoreTask.writesAt, List.filterMap_cons]
        by_cases atLocation : location = ⟨0, offset⟩
        · simp only [atLocation, ite_true, List.foldl_cons]
          rw [← same, State.store_byte_written _ _ _ _ live]
        · simp only [ite_eq_right atLocation]
          rw [State.store_byte_other _ _ _ _ (fun eq => atLocation (eq.symm.trans same))]

theorem StoreTask.handles_preserved {task : StoreTask} {state final : State}
    (ran : Runs state task.code final) : final.handles = state.handles := by
  induction task generalizing state with
  | nil =>
    cases ran
    rfl
  | cons head tail ih =>
    cases ran with
    | cons first continued =>
      cases first
      have preserved := @ih _ continued
      exact preserved

theorem StoreTask.frames_byte {task : StoreTask} {state final : State}
    (addresses : RecordAddresses state) (ran : Runs state task.code final)
    {offset : Nat} (outside : offset ∉ task.map Prod.fst) :
    final.byte ⟨0, offset⟩ = state.byte ⟨0, offset⟩ := by
  have untouched : (⟨0, offset⟩ : ByteLocation) ∉ task.footprint.writes := by
    intro wrote
    obtain ⟨store, member, location⟩ := List.mem_map.mp wrote
    exact outside (List.mem_map.mpr ⟨store, member, congrArg ByteLocation.offset location⟩)
  simp only [StoreTask.executes_writesAt addresses ran, StoreTask.none_at untouched, List.foldl_nil]

/-- Every legal interleaving has the same byte contents. A task may repeat a
write to its own field, and each schedule retains the parent resources. -/
theorem storeTasks_schedule_deterministic {tasks : List StoreTask} {first second : StoreTask}
    {state firstFinal secondFinal : State} {resources : ResourceState}
    (checked : checkStoreTasks tasks resources = true) (addresses : RecordAddresses state)
    (order1 : StoreSchedule tasks first) (order2 : StoreSchedule tasks second)
    (run1 : Runs state first.code firstFinal) (run2 : Runs state second.code secondFinal) :
    ∀ location, firstFinal.byte location = secondFinal.byte location := by
  have separated := ((checkStoreTasks_correct _ _).mp checked).1
  intro location
  rw [StoreTask.executes_writesAt addresses run1, StoreTask.executes_writesAt addresses run2,
    order1.writesAt_agrees separated, order2.writesAt_agrees separated]

end Aethel.SourceVerification
