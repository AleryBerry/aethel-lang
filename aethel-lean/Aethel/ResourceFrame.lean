import Aethel.ResourceLiveness

namespace Aethel.Core

theorem State.store_byte_other (s : State) (written observed : ByteLocation) (value : UInt8)
    (different : written ≠ observed) :
    (s.store written value).byte observed = s.byte observed := by
  simp only [State.byte, State.allocation, State.store, List.find?_map, Function.comp_def]
  generalize h : s.allocations.find? (fun a => a.owner == observed.allocation) = found
  cases found <;> simp only [Option.map_none, Option.map_some, bind, Option.bind]
  rename_i allocation
  have owner : allocation.owner = observed.allocation := by simpa using List.find?_some h
  by_cases same : observed.allocation = written.allocation <;>
    simp [owner, same, List.getElem?_set]
  exact fun equalOffset => False.elim (different (by cases written; cases observed; congr; exact same.symm))

theorem State.store_byte_written (s : State) (p : ByteLocation) (old value : UInt8)
    (live : s.byte p = some old) :
    (s.store p value).byte p = some value := by
  simp only [State.byte, State.allocation, State.store, List.find?_map, Function.comp_def]
  simp only [State.byte, State.allocation, bind, Option.bind_eq_some_iff] at live
  obtain ⟨allocation, found, read⟩ := live
  have owner : allocation.owner = p.allocation := by simpa using List.find?_some found
  have bound := (List.getElem?_eq_some_iff.mp read).choose
  simp [found, owner, bind, bound]

theorem Step.write_frame {s next : State} {id : HandleId} {h : Handle} {value : UInt8}
    (step : Step s (.write id value) next) (found : s.handle id = some h)
    (observed : ByteLocation) (different : h.location ≠ observed) :
    next.byte observed = s.byte observed := by
  cases step
  rename_i writer old authority alive available lookup
  have same := Option.some.inj (lookup.symm.trans found)
  exact s.store_byte_other writer.location observed value (same.symm ▸ different)

/-- Physical byte effects of a single successful access. A read observes the
current byte. A write changes storage and requires a live destination. -/
def ByteAccess.Effect (state next : State) : ByteAccess → Prop
  | .read location => ∃ value, state.byte location = some value ∧ next = state.observe value
  | .write location value => (∃ old, state.byte location = some old) ∧ next = state.store location value

theorem Step.refines_byteAccess {state next : State} {op : Instruction} {access : ByteAccess}
    (step : Step state op next) (decoded : op.byteAccess state.resources = some access) :
    access.Effect state next := by
  cases step <;> simp_all [Instruction.byteAccess]
  all_goals subst access; simp_all [ByteAccess.Effect]

def ByteAccess.location : ByteAccess → ByteLocation
  | .read location | .write location _ => location

theorem Step.byteAccess_inBounds {state next : State} {op : Instruction} {access : ByteAccess}
    (step : Step state op next) (decoded : op.byteAccess state.resources = some access) :
    ∃ size, state.resources.extent access.location.allocation = some size ∧ access.location.offset < size := by
  have live : state.resources.live access.location = true := by
    have effect := step.refines_byteAccess decoded
    rw [State.resources_live]
    cases access with
    | read _ =>
      obtain ⟨value, present, _⟩ := effect
      simp [ByteAccess.location, present]
    | write _ _ =>
      obtain ⟨value, present⟩ := effect.1
      simp [ByteAccess.location, present]
  simpa only [ResourceState.live, Option.any_eq_true, decide_eq_true_eq] using live

/-- Instructions in the body of a single-allocation packed program may use
or change authority without changing which allocations exist or their sizes. -/
def Instruction.keepsExtents : Instruction → Bool
  | .alloc .. | .destroy .. => false
  | _ => true

theorem Step.preserves_extents {state next : State} {op : Instruction}
    (step : Step state op next) (fixed : op.keepsExtents = true) :
    next.resources.allocations = state.resources.allocations := by
  cases step <;> simp_all [Instruction.keepsExtents, State.addHandle, State.addView, State.observe,
    State.removeView, State.removeHandle, State.resources_store] <;> rfl

theorem Step.preserves_data_withoutOperand {state next : State} {op : Instruction}
    (step : Step state op next) (fixed : op.keepsExtents = true)
    (noOperand : op.byteAccess state.resources = none) :
    next.byte = state.byte ∧ next.observations = state.observations := by
  cases step <;> simp_all [Instruction.keepsExtents, Instruction.byteAccess] <;> exact ⟨rfl, rfl⟩

/-- The ordered physical byte operands of legal steps, resolving each handle
or view in the state in which the corresponding instruction executes. -/
inductive ByteOperands : State → Program → List ByteAccess → State → Prop where
  | nil : ByteOperands state [] [] state
  | cons (step : Step state op next) (rest : ByteOperands next program accesses final) :
      ByteOperands state (op :: program) ((op.byteAccess state.resources).toList ++ accesses) final

def traceByteOperands (resources : ResourceState) : Program → Option (List ByteAccess)
  | [] => some []
  | op :: rest => do
    let next ← checkInstruction resources op
    let tail ← traceByteOperands next rest
    return (op.byteAccess resources).toList ++ tail

theorem ByteOperands.computes {state final : State} {program : Program} {accesses : List ByteAccess}
    (ran : ByteOperands state program accesses final) :
    traceByteOperands state.resources program = some accesses := by
  induction ran with
  | nil => rfl
  | cons step _ ih =>
    simp [traceByteOperands, checkInstruction_correct, execute_complete step, ih, bind, pure]

theorem traceByteOperands_correct (state : State) (program : Program) (accesses : List ByteAccess) :
    traceByteOperands state.resources program = some accesses ↔ ∃ final, ByteOperands state program accesses final := by
  refine ⟨?_, fun ⟨_, ran⟩ => ran.computes⟩
  intro checked
  induction program generalizing state accesses with
  | nil =>
    cases checked
    exact ⟨_, .nil⟩
  | cons op rest ih =>
    obtain ⟨resources, advanced, tail⟩ := Option.bind_eq_some_iff.mp checked
    rw [checkInstruction_correct] at advanced
    obtain ⟨next, executed, rfl⟩ := Option.map_eq_some_iff.mp advanced
    obtain ⟨remaining, observed, exactAccesses⟩ := Option.bind_eq_some_iff.mp tail
    have same := Option.some.inj exactAccesses
    subst accesses
    obtain ⟨final, ran⟩ := ih _ _ observed
    exact ⟨final, .cons (execute_sound executed) ran⟩

theorem Runs.byteOperands {state final : State} {program : Program} (ran : Runs state program final) :
    ∃ accesses, ByteOperands state program accesses final := by
  induction ran with
  | nil => exact ⟨[], .nil⟩
  | cons step _ ih =>
    obtain ⟨_, ran⟩ := ih
    exact ⟨_, .cons step ran⟩

theorem ByteOperands.inBounds {state final : State} {program : Program} {accesses : List ByteAccess}
    (ran : ByteOperands state program accesses final) (fixed : program.all Instruction.keepsExtents = true)
    {access : ByteAccess} (member : access ∈ accesses) :
    ∃ size, state.resources.extent access.location.allocation = some size ∧ access.location.offset < size := by
  induction ran with
  | nil => simp at member
  | cons step _ ih =>
    obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp fixed
    rcases List.mem_append.mp member with first | later
    · exact step.byteAccess_inBounds (Option.mem_toList.mp first)
    · obtain ⟨size, extent, bound⟩ := ih tail later
      exact ⟨size, by simpa only [ResourceState.extent, step.preserves_extents head] using extent, bound⟩

private theorem Step.byteAccess_exists {state next : State} {op : Instruction}
    (step : Step state op next) (access : op.isByteAccess = true) :
    ∃ decoded, op.byteAccess state.resources = some decoded := by
  cases step <;> simp_all [Instruction.isByteAccess, Instruction.byteAccess]

def Instruction.writeValueAt (resources : ResourceState) (loc : ByteLocation) (op : Instruction) : Option UInt8 :=
  (op.byteAccess resources).bind fun
    | .read _ => none
    | .write target value => if target = loc then some value else none

def ByteAccess.readSample (state : State) : ByteAccess → Option (BitVec 8)
  | .read location => (state.byte location).map UInt8.toBitVec
  | .write .. => none

def Instruction.readSample (state : State) (op : Instruction) : Option (BitVec 8) :=
  (op.byteAccess state.resources).bind (ByteAccess.readSample state)

theorem Program.readSamples_of_byteAccesses (state : State) {program : Program} {accesses : List ByteAccess}
    (decoded : program.mapM (Instruction.byteAccess state.resources) = some accesses) :
    program.mapM (Instruction.readSample state) = accesses.mapM (ByteAccess.readSample state) := by
  induction program generalizing accesses with
  | nil => cases decoded; rfl
  | cons op rest ih =>
    simp only [List.mapM_cons, pure, bind, Option.bind_eq_some_iff, Option.some.injEq] at decoded
    obtain ⟨head, resolves, tail, recorded, rfl⟩ := decoded
    simp [List.mapM_cons, Instruction.readSample, resolves, ih recorded, pure, bind]

theorem Step.byte_after_access {state next : State} {op : Instruction}
    (step : Step state op next) (access : op.isByteAccess = true) (loc : ByteLocation) :
    next.byte loc = (op.writeValueAt state.resources loc).or (state.byte loc) := by
  obtain ⟨decoded, resolved⟩ := step.byteAccess_exists access
  have effect := step.refines_byteAccess resolved
  cases decoded with
  | read source =>
    obtain ⟨value, _, rfl⟩ := effect
    simp [Instruction.writeValueAt, resolved, State.byte, State.allocation, State.observe, Option.or]
  | write target value =>
    obtain ⟨⟨old, live⟩, rfl⟩ := effect
    by_cases same : target = loc
    · subst target
      simp [State.store_byte_written _ _ _ _ live, Instruction.writeValueAt, resolved, Option.or]
    · simp [State.store_byte_other _ _ _ _ same, Instruction.writeValueAt, resolved, same, Option.or]

/-- Within a byte-only trace the kernel resources are constant, so each
location's final byte follows its ordered list of resolved write operands. -/
theorem Runs.byte_after_accesses {state next : State} {program : Program}
    (ran : Runs state program next) (accesses : program.all Instruction.isByteAccess = true)
    (loc : ByteLocation) :
    next.byte loc = (program.filterMap (Instruction.writeValueAt state.resources loc)).foldl
      (fun _ value => some value) (state.byte loc) := by
  induction ran with
  | nil => rfl
  | cons step _ ih =>
    obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp accesses
    rw [ih rest, step.resources_of_byteAccess first, step.byte_after_access first loc]
    simp only [List.filterMap_cons]
    split <;> rename_i selected <;> simp [selected, Option.or]

end Aethel.Core
