import Aethel.PackedMIR

namespace Aethel.PackedMIR

open AutomaticLayout ScopedForkJoin SourceVerification

private structure StoreInput where
  path : List Nat
  code : Nat
  samplesRev : List (BitVec 8) := []

private structure Cursor where
  pending : Core.Program
  store : Option StoreInput

private def Cursor.start (task : Task) (program : Core.Program) : Cursor :=
  ⟨program, task.code.map fun code => { path := task.path, code }⟩

/-- A pending store takes its write operands from the sampled reconstruction.
The emitted group supplies the independently checked instruction sequence. -/
private def Cursor.materialize {record : PackedRecord abi schema} (cursor : Cursor)
    (entry : record.Memory) (scope : Nat) (heap : Core.State) : Option Core.Program :=
  match cursor.store, cursor.pending with
  | some store, op :: rest =>
    match op.byteAccess heap.resources with
    | some (.write ..) => do
      let rebuilt ← entry.writeInScopeProgramFromSamples scope store.path store.code store.samplesRev.reverse
      let writes := rebuilt.drop store.samplesRev.length
      if writes = op :: rest then some writes else none
    | _ => some cursor.pending
  | _, _ => some cursor.pending

private def Cursor.collect (cursor : Cursor) (access : Option Core.ByteAccess)
    (next : Core.State) : Option StoreInput := do
  let store ← cursor.store
  let some (.read _) := access | none
  let sample ← next.observations.head?
  some { store with samplesRev := sample.toBitVec :: store.samplesRev }

private def Cursor.advance {record : PackedRecord abi schema} (cursor : Cursor)
    (entry : record.Memory) (scope : Nat) (heap : Core.State) :
    Option (Core.Instruction × Core.State × Cursor) := do
  let op :: pending ← cursor.materialize entry scope heap | none
  let next ← Core.execute heap op
  return (op, next, ⟨pending, cursor.collect (op.byteAccess heap.resources) next⟩)

private def runCursors {record : PackedRecord abi schema} (entry : record.Memory) (scope : Nat)
    (heap : Core.State) (cursors : List Cursor) : List Nat → Option (Core.Program × Core.State)
  | [] => if cursors.all (fun cursor => cursor.pending.isEmpty) then some ([], heap) else none
  | task :: rest => do
    let cursor ← cursors[task]?
    let (op, next, cursor) ← cursor.advance entry scope heap
    let (tail, final) ← runCursors entry scope next (cursors.set task cursor) rest
    return (op :: tail, final)

/-- Execute a fork of admitted packed MIR. The operation index selects the
fork, and each pick consumes the next byte instruction of that task. -/
def Accepted.runForkSchedule {mir : Module} (accepted : Accepted mir) (operation : Nat)
    (picks : List Nat) : Option (Core.Program × Core.State) := do
  let .fork scope tasks :: _ := mir.operations.drop operation | none
  let entry ← (mir.operations.take operation).foldlM Op.execute { memory := accepted.initial }
  let programs ← tasksKernelPrograms scope entry tasks
  runCursors entry.memory scope entry.memory.heap (tasks.zipWith Cursor.start programs) picks

private theorem Cursor.materialize_pending {record : PackedRecord abi schema} {cursor : Cursor}
    {entry : record.Memory} {scope : Nat} {heap : Core.State} {ready : Core.Program}
    (materialized : cursor.materialize entry scope heap = some ready) : ready = cursor.pending := by
  unfold Cursor.materialize at materialized
  split at materialized
  next store op rest available pending =>
    split at materialized
    next =>
      obtain ⟨writes, _, guarded⟩ := Option.bind_eq_some_iff.mp materialized
      obtain ⟨agrees, recorded⟩ := Option.ite_none_right_eq_some.mp guarded
      exact (Option.some.inj recorded).symm.trans (agrees.trans pending.symm)
    next => exact (Option.some.inj materialized).symm
  next => exact (Option.some.inj materialized).symm

private theorem Cursor.advance_sound {record : PackedRecord abi schema} {cursor : Cursor}
    {entry : record.Memory} {scope : Nat} {heap next : Core.State} {op : Core.Instruction}
    {updated : Cursor} (ran : cursor.advance entry scope heap = some (op, next, updated)) :
    cursor.pending = op :: updated.pending ∧ Core.Step heap op next ∧
      ∀ {input location}, cursor.store = some input → op.byteAccess heap.resources = some (.read location) →
        ∃ value, heap.byte location = some value ∧
          updated.store = some { input with samplesRev := value.toBitVec :: input.samplesRev } := by
  unfold Cursor.advance at ran
  cases prepared : cursor.materialize entry scope heap with
  | none => simp [prepared, bind] at ran
  | some ready =>
    cases ready with
    | nil => simp [prepared, bind] at ran
    | cons instruction pending =>
      simp only [prepared, bind, Option.bind_some, Option.bind_eq_some_iff, pure, Option.some.injEq] at ran
      obtain ⟨_, executed, same⟩ := ran
      cases same
      have step := Core.execute_sound executed
      refine ⟨(Cursor.materialize_pending prepared).symm, step, ?_⟩
      intro input location collecting read
      obtain ⟨value, live, rfl⟩ := step.refines_byteAccess read
      exact ⟨value, live, by simp [Cursor.collect, collecting, read, Core.State.observe, bind]⟩

/-- In a collecting cursor, the samples already taken followed by the
remaining physical reads suffice to reconstruct the original store group. -/
private inductive Cursor.Ready {record : PackedRecord abi schema} (entry : record.Memory)
    (scope : Nat) (heap : Core.State) : Cursor → Prop where
  | plain (pending : Core.Program) : Ready entry scope heap ⟨pending, none⟩
  | collecting {input : StoreInput} {original consumed reads writes : Core.Program} {samples : List (BitVec 8)}
      (parts : original = consumed ++ reads ++ writes) (count : consumed.length = input.samplesRev.length)
      (snapshot : reads.mapM (Core.Instruction.readSample heap) = some samples)
      (writable : ∀ op ∈ writes, ∃ place value, op.byteAccess heap.resources = some (.write place value))
      (rebuilt : entry.writeInScopeProgramFromSamples scope input.path input.code
        (input.samplesRev.reverse ++ samples) = some original) :
      Ready entry scope heap ⟨reads ++ writes, some input⟩

private theorem Cursor.Ready.frame {record : PackedRecord abi schema} {entry : record.Memory} {scope : Nat}
    {heap next : Core.State} {cursor : Cursor} (ready : Cursor.Ready entry scope heap cursor)
    (resources : next.resources = heap.resources)
    (samples : ∀ op ∈ cursor.pending, op.readSample next = op.readSample heap) :
    Cursor.Ready entry scope next cursor := by
  cases ready with
  | plain pending => exact .plain pending
  | collecting parts count snapshot writable rebuilt =>
    refine .collecting parts count ?_ (by simpa only [resources] using writable) rebuilt
    rw [mapM_eq_of_mem (fun op member => samples op (List.mem_append_left _ member))]
    exact snapshot

private theorem observed_sample {heap next : Core.State} {op : Core.Instruction} {sample : BitVec 8}
    (step : Core.Step heap op next) (sampled : op.readSample heap = some sample) :
    ∃ (place : ByteLocation) (byte : UInt8), op.byteAccess heap.resources = some (.read place) ∧
      byte.toBitVec = sample ∧ next = heap.observe byte := by
  unfold Core.Instruction.readSample at sampled
  obtain ⟨access, decoded, observed⟩ := Option.bind_eq_some_iff.mp sampled
  cases access with
  | write _ _ => cases observed
  | read place =>
    obtain ⟨byte, live, same⟩ := Option.map_eq_some_iff.mp observed
    obtain ⟨observed, atPlace, nextState⟩ := step.refines_byteAccess decoded
    have equal := Option.some.inj (atPlace.symm.trans live)
    exact ⟨place, byte, decoded, same, equal ▸ nextState⟩

private theorem Cursor.advance_prepared {record : PackedRecord abi schema} {entry : record.Memory}
    {scope : Nat} {heap next : Core.State} {cursor : Cursor} {op : Core.Instruction} {pending : Core.Program}
    (ready : cursor.materialize entry scope heap = some (op :: pending)) (step : Core.Step heap op next) :
    cursor.advance entry scope heap = some (op, next, ⟨pending, cursor.collect (op.byteAccess heap.resources) next⟩) := by
  simp [Cursor.advance, ready, Core.execute_complete step, bind, pure]

private theorem Cursor.Ready.advance {record : PackedRecord abi schema} {entry : record.Memory} {scope : Nat}
    {heap next : Core.State} {cursor : Cursor} {op : Core.Instruction} {pending : Core.Program}
    (ready : Cursor.Ready entry scope heap cursor) (selected : cursor.pending = op :: pending)
    (step : Core.Step heap op next) :
    ∃ updated, cursor.advance entry scope heap = some (op, next, updated) ∧
      updated.pending = pending ∧ Cursor.Ready entry scope next updated := by
  cases ready with
  | plain existing =>
    have materialized : (Cursor.mk existing none).materialize entry scope heap = some (op :: pending) :=
      congrArg some selected
    exact ⟨_, Cursor.advance_prepared materialized step, rfl, .plain pending⟩
  | @collecting input original consumed reads writes samples parts count snapshot writable rebuilt =>
    cases reads with
    | nil =>
      have noSamples : samples = [] := (Option.some.inj snapshot).symm
      subst samples
      have suffix : writes = op :: pending := selected
      obtain ⟨place, value, decoded⟩ := writable op (suffix ▸ List.mem_cons_self)
      have reconstructed : original.drop input.samplesRev.length = op :: pending := by
        rw [← count, parts, List.append_nil, List.drop_left, suffix]
      have rebuiltAll : entry.writeInScopeProgramFromSamples scope input.path input.code input.samplesRev.reverse =
          some original := by simpa using rebuilt
      have materialized : (Cursor.mk ([] ++ writes) (some input)).materialize entry scope heap =
          some (op :: pending) := by
        simp [Cursor.materialize, suffix, decoded, rebuiltAll, reconstructed, bind]
      have advanced := Cursor.advance_prepared materialized step
      rw [decoded] at advanced
      exact ⟨⟨pending, none⟩, advanced, rfl, .plain pending⟩
    | cons first reads =>
      obtain ⟨head, tail⟩ := List.cons.inj selected
      subst first
      subst pending
      simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at snapshot
      obtain ⟨sample, sampled, upcoming, later, rfl⟩ := snapshot
      obtain ⟨place, byte, decoded, same, rfl⟩ := observed_sample step sampled
      have materialized : (Cursor.mk ((op :: reads) ++ writes) (some input)).materialize entry scope heap =
          some (op :: (reads ++ writes)) := by simp [Cursor.materialize, decoded]
      have advanced := Cursor.advance_prepared materialized step
      let updated := { input with samplesRev := byte.toBitVec :: input.samplesRev }
      refine ⟨⟨reads ++ writes, some updated⟩, ?_, rfl,
        .collecting (original := original) (consumed := consumed ++ [op]) ?_ ?_ later writable ?_⟩
      · simpa [Cursor.collect, decoded, Core.State.observe, bind, updated] using advanced
      · simpa [List.append_assoc] using parts
      · simp [updated, count]
      · simpa [updated, List.reverse_cons, List.append_assoc, same] using rebuilt

private def FramesReads (resources : Core.ResourceState) (groups : List Core.Program) : Prop :=
  ∀ {writer reader : Nat} {writing reading : Core.Program}, writer ≠ reader →
    groups[writer]? = some writing → groups[reader]? = some reading →
    ∀ {op read : Core.Instruction} {place : ByteLocation}, op ∈ writing → read ∈ reading →
      read.byteAccess resources = some (.read place) → op.writeValueAt resources place = none

private theorem FramesReads.tail {resources : Core.ResourceState} {groups : List Core.Program}
    {index : Nat} {op : Core.Instruction} {pending : Core.Program} (framed : FramesReads resources groups)
    (picked : groups[index]? = some (op :: pending)) : FramesReads resources (groups.set index pending) := by
  have inside := (List.getElem?_eq_some_iff.mp picked).choose
  have previous {task : Nat} {remaining : Core.Program} (found : (groups.set index pending)[task]? = some remaining) :
      ∃ original, groups[task]? = some original ∧ ∀ instr ∈ remaining, instr ∈ original := by
    by_cases selected : task = index
    · subst task
      rw [List.getElem?_set_self inside] at found
      cases found
      exact ⟨_, picked, fun _ member => List.mem_cons_of_mem _ member⟩
    · rw [List.getElem?_set_ne (Ne.symm selected)] at found
      exact ⟨_, found, fun _ member => member⟩
  intro writer reader writing reading distinct writesGroup readsGroup instruction read place writes reads decoded
  obtain ⟨_, oldWriter, ofWriter⟩ := previous writesGroup
  obtain ⟨_, oldReader, ofReader⟩ := previous readsGroup
  exact framed distinct oldWriter oldReader (ofWriter _ writes) (ofReader _ reads) decoded

private theorem sample_of_framed_step {heap next : Core.State} {write read : Core.Instruction}
    (step : Core.Step heap write next) (byteOnly : write.isByteAccess = true)
    (framed : ∀ place, read.byteAccess heap.resources = some (.read place) →
      write.writeValueAt heap.resources place = none) :
    read.readSample next = read.readSample heap := by
  unfold Core.Instruction.readSample
  rw [step.resources_of_byteAccess byteOnly]
  cases decoded : read.byteAccess heap.resources with
  | none => rfl
  | some event =>
    cases event with
    | write _ _ => rfl
    | read place =>
      have byte := step.byte_after_access byteOnly place
      rw [framed place decoded] at byte
      simp [Core.ByteAccess.readSample, byte, Option.or]

private theorem runCursors_sound {record : PackedRecord abi schema} {entry : record.Memory}
    {scope : Nat} {heap final : Core.State} {cursors : List Cursor} {picks : List Nat} {program : Core.Program}
    (ran : runCursors entry scope heap cursors picks = some (program, final)) :
    PickedSchedule (cursors.map Cursor.pending) picks program ∧ Core.Runs heap program final := by
  induction picks generalizing heap cursors program final with
  | nil =>
    simp only [runCursors, Option.ite_none_right_eq_some, Option.some.injEq] at ran
    obtain ⟨empty, equal⟩ := ran
    cases equal
    refine ⟨.done ?_, .nil⟩
    intro task member
    obtain ⟨cursor, present, rfl⟩ := List.mem_map.mp member
    exact List.isEmpty_iff.mp (List.all_eq_true.mp empty cursor present)
  | cons task rest ih =>
    simp only [runCursors, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ran
    obtain ⟨cursor, selected, ⟨op, next, updated⟩, advanced, ⟨tail, last⟩, continued, equal⟩ := ran
    cases equal
    obtain ⟨pending, step, _⟩ := Cursor.advance_sound advanced
    obtain ⟨order, suffix⟩ := ih continued
    rw [List.map_set] at order
    have atTask : (cursors.map Cursor.pending)[task]? = some (op :: updated.pending) := by
      simp [selected, pending]
    exact ⟨.pick atTask order, .cons step suffix⟩

private theorem runCursors_complete {record : PackedRecord abi schema} {entry : record.Memory}
    {scope : Nat} {groups : List Core.Program} {heap final : Core.State} {cursors : List Cursor}
    {picks : List Nat} {program : Core.Program}
    (picked : PickedSchedule groups picks program) (ran : Core.Runs heap program final)
    (accesses : program.all Core.Instruction.isByteAccess = true)
    (table : cursors.map Cursor.pending = groups) (framed : FramesReads heap.resources groups)
    (ready : ∀ (index : Nat) cursor, cursors[index]? = some cursor → Cursor.Ready entry scope heap cursor) :
    runCursors entry scope heap cursors picks = some (program, final) := by
  induction picked generalizing heap final cursors with
  | done exhausted =>
    cases ran
    have empty : cursors.all (fun cursor => cursor.pending.isEmpty) = true := by
      apply List.all_eq_true.mpr
      intro cursor member
      have present : cursor.pending ∈ _ := table ▸ List.mem_map_of_mem (f := Cursor.pending) member
      simp [exhausted cursor.pending present]
    simp [runCursors, empty]
  | @pick groups index op pending picks program selected _ ih =>
    cases ran with
    | cons step suffix =>
      rename_i middle
      obtain ⟨access, following⟩ := Bool.and_eq_true_iff.mp accesses
      have atPick := congrArg (fun (groups : List Core.Program) => groups[index]?) table
      rw [selected, List.getElem?_map] at atPick
      obtain ⟨cursor, found, exactHead⟩ := Option.map_eq_some_iff.mp atPick
      obtain ⟨updated, advanced, left, readyUpdated⟩ := (ready index cursor found).advance exactHead step
      have bounds := (List.getElem?_eq_some_iff.mp found).choose
      have resources := step.resources_of_byteAccess access
      have readyNext : ∀ (task : Nat) current, (cursors.set index updated)[task]? = some current →
          Cursor.Ready entry scope middle current := by
        intro task current atTask
        by_cases chosen : task = index
        · subst task
          rw [List.getElem?_set_self bounds] at atTask
          cases atTask
          exact readyUpdated
        · rw [List.getElem?_set_ne (Ne.symm chosen)] at atTask
          have otherGroup := congrArg (fun (groups : List Core.Program) => groups[task]?) table
          rw [List.getElem?_map, atTask] at otherGroup
          apply (ready task current atTask).frame resources
          intro read member
          exact sample_of_framed_step step access (fun _ decoded =>
            framed (Ne.symm chosen) selected otherGroup.symm List.mem_cons_self member decoded)
      have nextTable : (cursors.set index updated).map Cursor.pending = groups.set index pending := by
        rw [List.map_set, left, table]
      have nextFramed : FramesReads middle.resources (groups.set index pending) := by
        rw [resources]
        exact framed.tail selected
      have continued := ih suffix following nextTable nextFramed readyNext
      simp [runCursors, found, advanced, continued, bind, pure]

private theorem split_at_lookup {items : List α} {index : Nat} {item : α}
    (found : items[index]? = some item) :
    items = items.take index ++ item :: items.drop (index + 1) ∧ (items.take index).length = index := by
  obtain ⟨inside, get⟩ := List.getElem?_eq_some_iff.mp found
  have tail := List.drop_eq_getElem_cons inside
  rw [get] at tail
  exact ⟨(List.take_append_drop index items).symm.trans (congrArg (items.take index ++ ·) tail),
    by simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt inside)]⟩

private theorem FramesReads.of_footprints {resources : Core.ResourceState}
    {groups : List Core.Program} {footprints : List TaskFootprint}
    (decoded : groups.mapM (TaskFootprint.ofProgram resources) = some footprints)
    (compatible : footprints.Pairwise ForkDisjoint) : FramesReads resources groups := by
  intro writer reader writing reading distinct writesGroup readsGroup op read place inWriter inReader address
  obtain ⟨split, _⟩ := split_at_lookup readsGroup
  have sibling : writing ∈ groups.take reader ++ groups.drop (reader + 1) := by
    by_cases earlier : writer < reader
    · have found : (groups.take reader)[writer]? = some writing := by
        rwa [List.getElem?_take_of_lt earlier]
      exact List.mem_append_left _ (List.mem_of_getElem? found)
    · have shifted : reader + 1 + (writer - (reader + 1)) = writer := by omega
      have found : (groups.drop (reader + 1))[writer - (reader + 1)]? = some writing := by
        rwa [List.getElem?_drop, shifted]
      exact List.mem_append_right _ (List.mem_of_getElem? found)
  have footprintsAt : (groups.take reader ++ reading :: groups.drop (reader + 1)).mapM
      (TaskFootprint.ofProgram resources) = some footprints := by
    exact congrArg (List.mapM (TaskFootprint.ofProgram resources)) split |>.symm.trans decoded
  have untouched := TaskFootprint.siblings_do_not_write_reads footprintsAt compatible inReader address sibling
  exact List.filterMap_eq_nil_iff.mp untouched op inWriter

private theorem access_of_groups {resources : Core.ResourceState} {groups : List Core.Program}
    {footprints : List TaskFootprint} (decoded : groups.mapM (TaskFootprint.ofProgram resources) = some footprints)
    {op : Core.Instruction} (member : op ∈ groups.flatten) : op.isByteAccess = true := by
  obtain ⟨group, present, inGroup⟩ := List.mem_flatten.mp member
  obtain ⟨_, _, extracted⟩ := mapM_member decoded present
  obtain ⟨events, byteAccesses, _⟩ := Option.map_eq_some_iff.mp extracted
  obtain ⟨_, _, resolves⟩ := mapM_member byteAccesses inGroup
  cases op <;> first | rfl | cases resolves

private theorem tasksKernelPrograms_length {record : PackedRecord abi schema} {scope : Nat}
    {state : Execution record} {tasks : List Task} {programs : List Core.Program}
    (compiled : tasksKernelPrograms scope state tasks = some programs) : tasks.length = programs.length := by
  induction tasks generalizing state programs with
  | nil => cases compiled; rfl
  | cons task rest ih =>
    simp only [tasksKernelPrograms, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨_, _, _, _, _, tail, rfl⟩ := compiled
    simp [ih tail]

private theorem Cursor.start_pending {tasks : List Task} {programs : List Core.Program}
    (length : tasks.length = programs.length) : (tasks.zipWith Cursor.start programs).map Cursor.pending = programs := by
  induction tasks generalizing programs with
  | nil => cases programs <;> simp_all
  | cons task rest ih =>
    cases programs with
    | nil => simp at length
    | cons program tail => simp [Cursor.start, ih (by simpa using length)]

private theorem Cursor.start_ready {record : PackedRecord abi schema} {state : Execution record}
    {scope : Nat} {tasks : List Task} {groups : List Core.Program} (sampling : ForkKernelSampling scope state tasks groups)
    {index : Nat} {cursor : Cursor} (selected : (tasks.zipWith Cursor.start groups)[index]? = some cursor) :
    Cursor.Ready state.memory scope state.memory.heap cursor := by
  obtain ⟨task, program, atTask, atProgram, rfl⟩ := List.getElem?_zipWith_eq_some.mp selected
  cases stored : task.code with
  | none => simpa only [Cursor.start, stored, Option.map_none] using
      (Cursor.Ready.plain (entry := state.memory) (scope := scope) (heap := state.memory.heap) program)
  | some code =>
    obtain ⟨split, size⟩ := split_at_lookup atProgram
    obtain ⟨reads, writes, samples, parts, writable, snapshot, ready, _⟩ :=
      sampling split (by simpa only [size] using atTask) stored
    unfold Cursor.start
    rw [stored, Option.map_some, parts]
    exact .collecting (original := program) (consumed := []) parts rfl snapshot writable ready

/-- A successful dynamic schedule consumes the exact admitted groups and
agrees with the typed fork on every byte and on resource authority. -/
theorem Accepted.runForkSchedule_sound {mir : Module} (accepted : Accepted mir)
    {operation : Nat} {picks : List Nat} {program : Core.Program} {heap : Core.State}
    (ran : accepted.runForkSchedule operation picks = some (program, heap)) :
    ∃ scope tasks rest, mir.operations.drop operation = .fork scope tasks :: rest ∧
      ∃ entry next : Execution accepted.record, ∃ groups,
        Runs { memory := accepted.initial } (mir.operations.take operation) entry ∧
        Step entry (.fork scope tasks) next ∧ Runs next rest accepted.final ∧
        tasksKernelPrograms scope entry tasks = some groups ∧ PickedSchedule groups picks program ∧
        Core.Runs entry.memory.heap program heap ∧ KernelReadsAgree entry.memory.heap groups program ∧
        heap.resources = entry.memory.heap.resources ∧
        ∀ location, heap.byte location = next.memory.heap.byte location := by
  unfold Accepted.runForkSchedule at ran
  split at ran
  next scope tasks rest atFork =>
    simp only [bind, Option.bind_eq_some_iff] at ran
    obtain ⟨entry, evaluated, groups, generated, scheduled⟩ := ran
    have cut : mir.operations = mir.operations.take operation ++ .fork scope tasks :: rest := by
      rw [← atFork, List.take_append_drop]
    obtain ⟨expected, after, expectedGroups, before, fork, later, emitted, agreement⟩ :=
      accepted.fork_kernel_interleavings_at cut
    rw [before.execute_complete] at evaluated
    cases evaluated
    rw [emitted] at generated
    cases generated
    obtain ⟨order, traced⟩ := runCursors_sound scheduled
    rw [Cursor.start_pending (tasksKernelPrograms_length emitted)] at order
    obtain ⟨readsAgree, joined, legal, resources, bytes⟩ := agreement program order.order
    have same := Option.some.inj ((Core.run_complete traced).symm.trans (Core.run_complete legal))
    cases same
    exact ⟨scope, tasks, rest, atFork, entry, after, groups, before, fork, later,
      emitted, order, traced, readsAgree, resources, bytes⟩
  next => cases ran

/-- Every legal sequence of task picks at an admitted fork runs to
completion. Mask regeneration succeeds at each task's first write. -/
theorem Accepted.runForkSchedule_complete {mir : Module} (accepted : Accepted mir)
    {operation scope : Nat} {tasks : List Task} {rest : List Op}
    (atFork : mir.operations.drop operation = .fork scope tasks :: rest) :
    ∃ entry : Execution accepted.record, ∃ groups,
      Runs { memory := accepted.initial } (mir.operations.take operation) entry ∧
      tasksKernelPrograms scope entry tasks = some groups ∧
      ∀ {picks program}, PickedSchedule groups picks program → ∃ heap,
        Core.Runs entry.memory.heap program heap ∧ accepted.runForkSchedule operation picks = some (program, heap) := by
  have cut : mir.operations = mir.operations.take operation ++ .fork scope tasks :: rest := by
    rw [← atFork, List.take_append_drop]
  obtain ⟨entry, _, groups, before, fork, _, compiled, agreement⟩ := accepted.fork_kernel_interleavings_at cut
  obtain ⟨sampledGroups, compiledForSampling, sampling⟩ := fork.fork_kernel_sampling
  have sameSamples := Option.some.inj (compiledForSampling.symm.trans compiled)
  subst sampledGroups
  obtain ⟨decodedGroups, footprints, compiledForDecoding, _, decoded, compatible⟩ := fork.fork_kernel_footprints
  have sameDecoded := Option.some.inj (compiledForDecoding.symm.trans compiled)
  subst decodedGroups
  refine ⟨entry, groups, before, compiled, ?_⟩
  intro picks program picked
  obtain ⟨_, heap, legal, _, _⟩ := agreement program picked.order
  have accesses : program.all Core.Instruction.isByteAccess = true :=
    List.all_eq_true.mpr fun op member => access_of_groups decoded (picked.order.perm_flatten.mem_iff.mp member)
  have executed := runCursors_complete picked legal accesses
    (Cursor.start_pending (tasksKernelPrograms_length compiled))
    (FramesReads.of_footprints decoded compatible) (fun _ _ selected => Cursor.start_ready sampling selected)
  exact ⟨heap, legal, by simp [Accepted.runForkSchedule, atFork, before.execute_complete, compiled, executed, bind]⟩

theorem Accepted.runForkSchedule_covers {mir : Module} (accepted : Accepted mir)
    {operation scope : Nat} {tasks : List Task} {rest : List Op}
    (atFork : mir.operations.drop operation = .fork scope tasks :: rest) :
    ∃ entry : Execution accepted.record, ∃ groups,
      Runs { memory := accepted.initial } (mir.operations.take operation) entry ∧
      tasksKernelPrograms scope entry tasks = some groups ∧
      ∀ {program}, TaskSchedule groups program → ∃ picks heap,
        accepted.runForkSchedule operation picks = some (program, heap) := by
  obtain ⟨entry, groups, before, compiled, complete⟩ := accepted.runForkSchedule_complete atFork
  refine ⟨entry, groups, before, compiled, ?_⟩
  intro program order
  obtain ⟨picks, chosen⟩ := order.has_picks
  obtain ⟨heap, _, ran⟩ := complete chosen
  exact ⟨picks, heap, ran⟩

end Aethel.PackedMIR
