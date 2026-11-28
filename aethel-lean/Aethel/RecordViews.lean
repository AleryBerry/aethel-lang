import Aethel.RecordRuntime
import Aethel.ByteLoans

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

def RecordView.startTrace (scope : RecordView) (owner : OwnerId)
    (handle : HandleId) : Program :=
  acquireViews handle ((List.range scope.width).map fun i =>
    ⟨scope.firstView + i, ⟨owner, scope.offset + i⟩, scope.mode⟩)

def RecordView.stopTrace (scope : RecordView) : Program :=
  releaseViews ((List.range scope.width).map fun i => scope.firstView + i)

def openLayoutView (owner : OwnerId) (layout : Layout) (state : State)
    (path : List Nat) (mode : AccessMode) : Option (RecordView × State) := do
  let allocation ← state.allocation owner
  if allocation.bytes.length != layout.size then none else do
    let (offset, width) ← inferView layout path
    let scope : RecordView := ⟨path, mode, offset, width, state.freshView⟩
    let opened ← Core.run state (scope.startTrace owner state.freshHandle)
    if checkAccessTargets opened owner mode scope.byteOffsets scope.byteTargets then
      return (scope, opened)
    else none

def openView (record : RecordRef abi schema) (state : State)
    (path : List Nat) (mode : AccessMode) : Option (RecordView × State) :=
  openLayoutView record.owner record.layout state path mode

def closeView (scope : RecordView) (state : State) : Option State :=
  Core.run state scope.stopTrace

/-- Successful acquisition consists only of legal kernel alias/reserve/forget
steps and covers the inferred logical path and physical range. -/
theorem openLayoutView_sound {owner : OwnerId} {layout : Layout} {state opened : State}
    {path : List Nat} {mode : AccessMode} {scope : RecordView}
    (result : openLayoutView owner layout state path mode = some (scope, opened)) :
    scope.path = path ∧ scope.mode = mode ∧
      inferView layout path = some (scope.offset, scope.width) ∧
      Runs state (scope.startTrace owner state.freshHandle) opened ∧
      AccessAllowed opened owner mode scope.byteOffsets scope.byteTargets := by
  simp only [openLayoutView, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.exists, Prod.mk.injEq, Option.ite_none_left_eq_some,
    Option.ite_none_right_eq_some, checkAccessTargets_correct] at result
  obtain ⟨_, _, _, offset, width, extent, _, executed, allowed, rfl, rfl⟩ := result
  exact ⟨rfl, rfl, extent, run_sound executed, allowed⟩

theorem openView_sound {record : RecordRef abi schema} {state opened : State}
    {path : List Nat} {mode : AccessMode} {scope : RecordView}
    (result : openView record state path mode = some (scope, opened)) :
    scope.path = path ∧ scope.mode = mode ∧
      inferView record.layout path = some (scope.offset, scope.width) ∧
      Runs state (scope.startTrace record.owner state.freshHandle) opened ∧
      AccessAllowed opened record.owner mode scope.byteOffsets scope.byteTargets :=
  openLayoutView_sound result

theorem openView_preserves_borrow_invariant {record : RecordRef abi schema} {state opened : State}
    {path : List Nat} {mode : AccessMode} {scope : RecordView}
    (result : openView record state path mode = some (scope, opened))
    (compatible : state.ViewsCompatible) : opened.ViewsCompatible :=
  (openView_sound result).2.2.2.1.views_compatible compatible

theorem closeView_sound {scope : RecordView} {state closed : State}
    (result : closeView scope state = some closed) :
    Runs state scope.stopTrace closed :=
  run_sound result

theorem openLayoutView_allocations {owner : OwnerId} {layout : Layout} {state opened : State}
    {path : List Nat} {mode : AccessMode} {scope : RecordView}
    (result : openLayoutView owner layout state path mode = some (scope, opened)) :
    opened.allocations = state.allocations := by
  rw [acquireViews_exact (openLayoutView_sound result).2.2.2.1]

private theorem releaseViews_allocations {ids : List ViewId} {state closed : State}
    (ran : Runs state (releaseViews ids) closed) : closed.allocations = state.allocations := by
  induction ids generalizing state with
  | nil => cases ran; rfl
  | cons _ _ ih =>
    cases ran with
    | cons step rest =>
      cases step
      simpa only [State.removeView] using ih rest

theorem closeView_allocations {scope : RecordView} {state closed : State}
    (result : closeView scope state = some closed) : closed.allocations = state.allocations :=
  releaseViews_allocations (closeView_sound result)

private def RecordView.target (scope : RecordView) (offset : Nat) : Option AccessTarget :=
  if scope.offset ≤ offset ∧ offset < scope.offset + scope.width then
    some (.view (scope.firstView + (offset - scope.offset)))
  else none

/-- Path containment is checked independently of byte containment. A view of
one packed flag never grants logical access to its sibling. -/
def RecordView.targetsFor (scope : RecordView) (path : List Nat) (mode : AccessMode)
    (offsets : List Nat) : Option (List AccessTarget) := do
  if scope.path.isPrefixOf path && decide (scope.mode.Allows mode) then
    offsets.mapM scope.target
  else none

theorem RecordView.targetsFor_scope {scope : RecordView} {path : List Nat} {mode : AccessMode}
    {offsets : List Nat} {targets : List AccessTarget}
    (found : scope.targetsFor path mode offsets = some targets) :
    scope.path <+: path ∧ scope.mode.Allows mode := by
  simp only [RecordView.targetsFor, Option.ite_none_right_eq_some, Bool.and_eq_true,
    decide_eq_true_eq, List.isPrefixOf_iff_prefix] at found
  exact found.1

def RecordView.targets (scope : RecordView) (record : RecordRef abi schema)
    (path : List Nat) (mode : AccessMode) : Option (List AccessTarget) := do
  let field ← resolveInteger record.conforms path
  scope.targetsFor path mode field.byteOffsets

theorem RecordView.targets_scope {scope : RecordView} {record : RecordRef abi schema}
    {path : List Nat} {mode : AccessMode} {targets : List AccessTarget}
    (found : scope.targets record path mode = some targets) :
    scope.path <+: path ∧ scope.mode.Allows mode := by
  obtain ⟨field, _, granted⟩ := Option.bind_eq_some_iff.mp found
  exact RecordView.targetsFor_scope granted

/-- A child uses the corresponding interval of the parent's existing byte
reservations. The runtime state stays put while the lexical authority narrows. -/
def reborrowLayoutView (parent : RecordView) (owner : OwnerId) (layout : Layout)
    (state : State) (path : List Nat) (mode : AccessMode) : Option RecordView := do
  let (offset, width) ← inferView layout path
  if parent.path.isPrefixOf path && decide (parent.mode.Allows mode ∧
      parent.offset ≤ offset ∧ offset + width ≤ parent.offset + parent.width) then
    let child : RecordView := ⟨path, mode, offset, width,
      parent.firstView + (offset - parent.offset)⟩
    if checkAccessTargets state owner mode child.byteOffsets child.byteTargets then
      some child
    else none
  else none

def reborrowView (parent : RecordView) (record : RecordRef abi schema)
    (state : State) (path : List Nat) (mode : AccessMode) : Option RecordView :=
  reborrowLayoutView parent record.owner record.layout state path mode

theorem reborrowLayoutView_sound {parent child : RecordView} {owner : OwnerId} {layout : Layout}
    {state : State} {path : List Nat} {mode : AccessMode}
    (borrowed : reborrowLayoutView parent owner layout state path mode = some child) :
    child.path = path ∧ child.mode = mode ∧ parent.path <+: child.path ∧
    parent.mode.Allows child.mode ∧ parent.offset ≤ child.offset ∧
    child.offset + child.width ≤ parent.offset + parent.width ∧
    child.firstView = parent.firstView + (child.offset - parent.offset) ∧
    inferView layout path = some (child.offset, child.width) ∧
    AccessAllowed state owner mode child.byteOffsets child.byteTargets := by
  simp only [reborrowLayoutView, bind, Option.bind_eq_some_iff, Prod.exists,
    Option.ite_none_right_eq_some, Bool.and_eq_true, List.isPrefixOf_iff_prefix,
    decide_eq_true_eq, checkAccessTargets_correct, Option.some.injEq] at borrowed
  obtain ⟨offset, width, found, ⟨pathWithin, authority, lower, upper⟩, allowed, rfl⟩ := borrowed
  exact ⟨rfl, rfl, pathWithin, authority, lower, upper, rfl, found, allowed⟩

theorem reborrowView_sound {parent child : RecordView} {record : RecordRef abi schema}
    {state : State} {path : List Nat} {mode : AccessMode}
    (borrowed : reborrowView parent record state path mode = some child) :
    child.path = path ∧ child.mode = mode ∧ parent.path <+: child.path ∧
    parent.mode.Allows child.mode ∧ parent.offset ≤ child.offset ∧
    child.offset + child.width ≤ parent.offset + parent.width ∧
    child.firstView = parent.firstView + (child.offset - parent.offset) ∧
    inferView record.layout path = some (child.offset, child.width) ∧
    AccessAllowed state record.owner mode child.byteOffsets child.byteTargets :=
  reborrowLayoutView_sound borrowed

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

/-- Opening a `RecordView` only inserts views targeting bytes inside `scope.byteOffsets`
of `record.owner`; all pre-existing views from `state` remain unaffected. -/
theorem openView_views_subset {record : RecordRef abi schema} {state opened : State}
    {path : List Nat} {mode : AccessMode} {scope : RecordView}
    (result : openView record state path mode = some (scope, opened)) :
    ∀ v ∈ opened.views, v ∈ state.views ∨
      (v.location.allocation = record.owner ∧ v.location.offset ∈ scope.byteOffsets) := by
  simp only [openView, openLayoutView, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.exists, Prod.mk.injEq, Option.ite_none_left_eq_some,
    Option.ite_none_right_eq_some] at result
  obtain ⟨_, _, _, offset, width, _, opened', executed, _, rfl, hOpenEq⟩ := result
  subst hOpenEq
  simp only [RecordView.startTrace] at executed
  have same := acquireViews_exact (run_sound executed)
  intro v hv
  rw [same] at hv
  simp only [List.mem_append, List.mem_reverse, List.mem_map] at hv
  rcases hv with ⟨i, chosen, rfl⟩ | previous
  · exact .inr ⟨rfl, List.mem_map.mpr ⟨i, chosen, rfl⟩⟩
  · exact .inl previous

end Aethel.AutomaticLayout
