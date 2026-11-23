import Aethel.RecordRuntime

namespace Aethel.AutomaticLayout

open Core Structured

/-- The whole storage span of the selected field or inline record. Packed
leaves reserve their containing byte, even if they use a single bit. -/
def inferView (layout : Layout) (path : List Nat) : Option (Nat × Nat) :=
  (resolve layout path).map fun field => (field.1.byteOffset, field.bytes)

theorem inferView_within {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    {path : List Nat} {offset width : Nat} (planned : Conforms abi schema layout)
    (inferred : inferView layout path = some (offset, width)) :
    offset + width ≤ layout.size := by
  obtain ⟨field, found, coordinates⟩ := Option.map_eq_some_iff.mp inferred
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj coordinates
  obtain ⟨_, _, _, valid⟩ := resolve_sound planned found
  exact valid.1

structure RecordView where
  private mk ::
  path : List Nat
  mode : AccessMode
  offset : Nat
  width : Nat
  firstView : ViewId

def RecordView.byteOffsets (scope : RecordView) : List Nat :=
  (List.range scope.width).map fun i => scope.offset + i

def RecordView.byteTargets (scope : RecordView) : List AccessTarget :=
  (List.range scope.width).map fun i => .view (scope.firstView + i)

private def RecordView.startTrace (scope : RecordView) (owner : OwnerId)
    (handle : HandleId) : Program :=
  (List.range scope.width).flatMap fun i =>
    [.alias handle owner (scope.offset + i) scope.mode,
      .reserve (scope.firstView + i) handle scope.mode, .forget handle]

private def RecordView.stopTrace (scope : RecordView) : Program :=
  (List.range scope.width).map fun i => .release (scope.firstView + i)

private def freshHandle (state : State) : HandleId :=
  ((state.handles.map Prod.fst).max?).getD 0 + 1

private def freshView (state : State) : ViewId :=
  ((state.views.map View.id).max?).getD 0 + 1

def openView (record : RecordRef abi schema) (state : State)
    (path : List Nat) (mode : AccessMode) : Option (RecordView × State) := do
  let allocation ← state.allocation record.owner
  if allocation.bytes.length != record.layout.size then none else do
    let (offset, width) ← inferView record.layout path
    let scope : RecordView := ⟨path, mode, offset, width, freshView state⟩
    let opened ← Core.run state (scope.startTrace record.owner (freshHandle state))
    if checkAccessTargets opened record.owner mode scope.byteOffsets scope.byteTargets then
      return (scope, opened)
    else none

def closeView (scope : RecordView) (state : State) : Option State :=
  Core.run state scope.stopTrace

/-- Successful acquisition consists only of legal kernel alias/reserve/forget
steps and covers the inferred logical path and physical range. -/
theorem openView_sound {record : RecordRef abi schema} {state opened : State}
    {path : List Nat} {mode : AccessMode} {scope : RecordView}
    (result : openView record state path mode = some (scope, opened)) :
    scope.path = path ∧ scope.mode = mode ∧
      inferView record.layout path = some (scope.offset, scope.width) ∧
      Runs state (scope.startTrace record.owner (freshHandle state)) opened ∧
      AccessAllowed opened record.owner mode scope.byteOffsets scope.byteTargets := by
  simp only [openView, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.exists, Prod.mk.injEq, Option.ite_none_left_eq_some,
    Option.ite_none_right_eq_some, checkAccessTargets_correct] at result
  obtain ⟨_, _, _, offset, width, extent, _, executed, allowed, rfl, rfl⟩ := result
  exact ⟨rfl, rfl, extent, run_sound executed, allowed⟩

theorem openView_preserves_borrow_invariant {record : RecordRef abi schema} {state opened : State}
    {path : List Nat} {mode : AccessMode} {scope : RecordView}
    (result : openView record state path mode = some (scope, opened))
    (compatible : state.ViewsCompatible) : opened.ViewsCompatible :=
  (openView_sound result).2.2.2.1.views_compatible compatible

theorem closeView_sound {scope : RecordView} {state closed : State}
    (result : closeView scope state = some closed) :
    Runs state scope.stopTrace closed :=
  run_sound result

private def RecordView.target (scope : RecordView) (offset : Nat) : Option AccessTarget :=
  if scope.offset ≤ offset ∧ offset < scope.offset + scope.width then
    some (.view (scope.firstView + (offset - scope.offset)))
  else none

/-- Path containment is checked independently of byte containment. A view of
one packed flag never grants logical access to its sibling. -/
def RecordView.targets (scope : RecordView) (record : RecordRef abi schema)
    (path : List Nat) (mode : AccessMode) : Option (List AccessTarget) := do
  if scope.path.isPrefixOf path && decide (scope.mode.Allows mode) then
    let field ← resolveInteger record.conforms path
    field.byteOffsets.mapM scope.target
  else none

theorem RecordView.targets_scope {scope : RecordView} {record : RecordRef abi schema}
    {path : List Nat} {mode : AccessMode} {targets : List AccessTarget}
    (found : scope.targets record path mode = some targets) :
    scope.path <+: path ∧ scope.mode.Allows mode := by
  simp only [RecordView.targets, Option.ite_none_right_eq_some, Bool.and_eq_true,
    decide_eq_true_eq, List.isPrefixOf_iff_prefix] at found
  exact found.1

/-- A child uses the corresponding interval of the parent's existing byte
reservations. The runtime state stays put while the lexical authority narrows. -/
def reborrowView (parent : RecordView) (record : RecordRef abi schema)
    (state : State) (path : List Nat) (mode : AccessMode) : Option RecordView := do
  let (offset, width) ← inferView record.layout path
  if parent.path.isPrefixOf path && decide (parent.mode.Allows mode ∧
      parent.offset ≤ offset ∧ offset + width ≤ parent.offset + parent.width) then
    let child : RecordView := ⟨path, mode, offset, width,
      parent.firstView + (offset - parent.offset)⟩
    if checkAccessTargets state record.owner mode child.byteOffsets child.byteTargets then
      some child
    else none
  else none

theorem reborrowView_sound {parent child : RecordView} {record : RecordRef abi schema}
    {state : State} {path : List Nat} {mode : AccessMode}
    (borrowed : reborrowView parent record state path mode = some child) :
    child.path = path ∧ child.mode = mode ∧ parent.path <+: child.path ∧
    parent.mode.Allows child.mode ∧ parent.offset ≤ child.offset ∧
    child.offset + child.width ≤ parent.offset + parent.width ∧
    child.firstView = parent.firstView + (child.offset - parent.offset) ∧
    inferView record.layout path = some (child.offset, child.width) ∧
    AccessAllowed state record.owner mode child.byteOffsets child.byteTargets := by
  simp only [reborrowView, bind, Option.bind_eq_some_iff, Prod.exists,
    Option.ite_none_right_eq_some, Bool.and_eq_true, List.isPrefixOf_iff_prefix,
    decide_eq_true_eq, checkAccessTargets_correct, Option.some.injEq] at borrowed
  obtain ⟨offset, width, found, ⟨pathWithin, authority, lower, upper⟩, allowed, rfl⟩ := borrowed
  exact ⟨rfl, rfl, pathWithin, authority, lower, upper, rfl, found, allowed⟩

theorem reborrowView_reuses_target {parent child : RecordView} {record : RecordRef abi schema}
    {state : State} {path : List Nat} {mode : AccessMode} {offset : Nat}
    (borrowed : reborrowView parent record state path mode = some child)
    (inside : child.offset ≤ offset ∧ offset < child.offset + child.width) :
    child.target offset = parent.target offset := by
  obtain ⟨_, _, _, _, childLower, childUpper, first, _, _⟩ := reborrowView_sound borrowed
  have contained : parent.offset ≤ offset ∧ offset < parent.offset + parent.width := by omega
  simp only [RecordView.target, ite_eq_left inside, ite_eq_left contained, first]
  have same : parent.firstView + (child.offset - parent.offset) + (offset - child.offset) =
      parent.firstView + (offset - parent.offset) := by
    rw [Nat.add_assoc, Nat.add_comm (child.offset - parent.offset),
      Nat.sub_add_sub_cancel inside.1 childLower]
  rw [same]

private theorem run_startStep_views (s next : State) (owner : OwnerId)
    (handle : HandleId) (offset : Nat) (mode : AccessMode) (vid : ViewId)
    (hRun : Core.run s [.alias handle owner offset mode, .reserve vid handle mode, .forget handle] = some next) :
    ∀ v ∈ next.views, v ∈ s.views ∨ v.location = ⟨owner, offset⟩ := by
  simp only [Core.run, Option.bind_eq_some_iff, Option.some.injEq] at hRun
  obtain ⟨s1, h1, s2, h2, s3, h3, rfl⟩ := hRun
  have st1 := execute_sound h1
  have st2 := execute_sound h2
  have st3 := execute_sound h3
  cases st1 with
  | alias fresh live =>
    have hLookup : (s.addHandle handle ⟨⟨owner, offset⟩, mode⟩).handle handle =
        some ⟨⟨owner, offset⟩, mode⟩ := by
      simp [State.handle, State.addHandle]
    cases st2 with
    | reserve _ found _ _ _ =>
      have hSame := Option.some.inj (found.symm.trans hLookup)
      cases st3 with
      | forget _ =>
        intro v hv
        simp only [State.removeHandle, State.addView, State.addHandle, List.mem_cons] at hv
        rcases hv with rfl | hOld
        · right; rw [hSame]
        · left; exact hOld

private def startTraceSegment (owner : OwnerId) (handle : HandleId) (offset : Nat)
    (mode : AccessMode) (firstView : ViewId) (indices : List Nat) : Program :=
  indices.flatMap fun i =>
    [.alias handle owner (offset + i) mode,
      .reserve (firstView + i) handle mode, .forget handle]

private theorem run_startTraceSegment_views (indices : List Nat) (s next : State)
    (owner : OwnerId) (handle : HandleId) (offset : Nat) (mode : AccessMode) (firstView : ViewId)
    (hRun : Core.run s (startTraceSegment owner handle offset mode firstView indices) = some next) :
    ∀ v ∈ next.views, v ∈ s.views ∨
      (v.location.allocation = owner ∧ ∃ i ∈ indices, v.location.offset = offset + i) := by
  induction indices generalizing s with
  | nil =>
    simp [startTraceSegment, Core.run] at hRun
    subst hRun
    intro v hv
    exact Or.inl hv
  | cons i rest ih =>
    have hSeg : startTraceSegment owner handle offset mode firstView (i :: rest) =
        [.alias handle owner (offset + i) mode,
          .reserve (firstView + i) handle mode, .forget handle] ++
          startTraceSegment owner handle offset mode firstView rest := rfl
    rw [hSeg, Core.run_append, Option.bind_eq_some_iff] at hRun
    obtain ⟨mid, hStep, hRest⟩ := hRun
    intro v hv
    rcases ih mid hRest v hv with hInMid | ⟨hOwner, j, hjMem, hOff⟩
    · rcases run_startStep_views s mid owner handle (offset + i) mode (firstView + i) hStep v hInMid with hInS | hLoc
      · exact Or.inl hInS
      · exact Or.inr ⟨congrArg ByteLocation.allocation hLoc, i, List.mem_cons_self,
          congrArg ByteLocation.offset hLoc⟩
    · exact Or.inr ⟨hOwner, j, List.mem_cons_of_mem _ hjMem, hOff⟩

/-- Opening a `RecordView` only inserts views targeting bytes inside `scope.byteOffsets`
of `record.owner`; all pre-existing views from `state` remain unaffected. -/
theorem openView_views_subset {record : RecordRef abi schema} {state opened : State}
    {path : List Nat} {mode : AccessMode} {scope : RecordView}
    (result : openView record state path mode = some (scope, opened)) :
    ∀ v ∈ opened.views, v ∈ state.views ∨
      (v.location.allocation = record.owner ∧ v.location.offset ∈ scope.byteOffsets) := by
  simp only [openView, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.exists, Prod.mk.injEq, Option.ite_none_left_eq_some,
    Option.ite_none_right_eq_some] at result
  obtain ⟨_, _, _, offset, width, _, opened', executed, _, rfl, hOpenEq⟩ := result
  subst hOpenEq
  have hSeg : (RecordView.mk path mode offset width (freshView state)).startTrace
      record.owner (freshHandle state) =
      startTraceSegment record.owner (freshHandle state) offset mode (freshView state)
        (List.range width) := rfl
  rw [hSeg] at executed
  intro v hv
  rcases run_startTraceSegment_views (List.range width) state opened' record.owner
      (freshHandle state) offset mode (freshView state) executed v hv with hInS | ⟨hOwner, i, hiMem, hOff⟩
  · exact Or.inl hInS
  · exact Or.inr ⟨hOwner, List.mem_map.mpr ⟨i, hiMem, hOff.symm⟩⟩

end Aethel.AutomaticLayout
