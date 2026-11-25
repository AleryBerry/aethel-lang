import Aethel.RustFFI
import Aethel.ByteLoans

namespace Aethel.RustFFI

open Core

private def sliceCells (slices : List RustSliceSpec) : List (ByteLocation × AccessMode) :=
  slices.flatMap fun slice => slice.locations.map (·, slice.mode)

private def sliceViews (first : ViewId) (slices : List RustSliceSpec) : List View :=
  ((sliceCells slices).zipIdx first).map fun (cell, id) => ⟨id, cell.1, cell.2⟩

def rustCallViews (state : State) (slices : List RustSliceSpec) : List View :=
  sliceViews state.freshView slices

private def borrowedBytes (slices : List RustSliceSpec) : Nat :=
  (slices.map RustSliceSpec.byteLen).sum

private theorem rustCallViews_ids (state : State) (slices : List RustSliceSpec) :
    (rustCallViews state slices).map View.id = List.range' state.freshView (borrowedBytes slices) := by
  rw [rustCallViews, sliceViews, List.map_map]
  change ((sliceCells slices).zipIdx state.freshView).map Prod.snd = _
  simp [sliceCells, borrowedBytes, RustSliceSpec.locations, List.length_flatMap]

theorem rustCallViews_origin {state : State} {slices : List RustSliceSpec} {view : View}
    (granted : view ∈ rustCallViews state slices) :
    ∃ slice ∈ slices, view.location ∈ slice.locations ∧ view.mode = slice.mode := by
  obtain ⟨⟨⟨location, mode⟩, id⟩, indexed, rfl⟩ := List.mem_map.mp granted
  have contained := List.fst_mem_of_mem_zipIdx indexed
  obtain ⟨slice, supplied, bySlice⟩ := List.mem_flatMap.mp contained
  obtain ⟨byte, within, same⟩ := List.mem_map.mp bySlice
  cases same
  exact ⟨slice, supplied, within, rfl⟩

inductive BorrowedAction (loans : List View) : Instruction → Prop where
  | read : view ∈ loans → BorrowedAction loans (.readView view.id)
  | write : view ∈ loans → BorrowedAction loans (.writeView view.id value)

private def checkBorrowedAction (start limit : ViewId) : Instruction → Bool
  | .readView id | .writeView id _ => decide (start ≤ id ∧ id < limit)
  | _ => false

private theorem checkBorrowedAction_correct (state : State) (slices : List RustSliceSpec)
    (instruction : Instruction) :
    checkBorrowedAction state.freshView (state.freshView + borrowedBytes slices) instruction = true ↔
      BorrowedAction (rustCallViews state slices) instruction := by
  have idGranted (id : ViewId) :
      id ∈ (rustCallViews state slices).map View.id ↔
        state.freshView ≤ id ∧ id < state.freshView + borrowedBytes slices := by
    rw [rustCallViews_ids, List.mem_range'_1]
  constructor
  · intro checked
    cases instruction <;> simp [checkBorrowedAction, ← idGranted, List.mem_map] at checked
    case readView =>
      obtain ⟨view, granted, rfl⟩ := checked
      exact .read granted
    case writeView =>
      obtain ⟨view, granted, rfl⟩ := checked
      exact .write granted
  · intro admitted
    cases admitted with
    | read granted | write granted =>
      exact decide_eq_true (idGranted _ |>.mp (List.mem_map_of_mem granted))

def RustCallWrites (slices : List RustSliceSpec) (location : ByteLocation) : Prop :=
  ∃ slice ∈ slices, location ∈ slice.locations ∧ slice.mode = .exclusive

/-- Execute the finite operations exposed by a synchronous Rust adapter.
The ABI check handles representation and bounds, and actual byte
reservations enforce compatibility with every caller and sibling view. -/
def runRustBorrowedCall (state : State) (slices : List RustSliceSpec) (accesses : Program) : Option State := do
  let start := state.freshView
  let finish := start + borrowedBytes slices
  if slices.all (checkRustSliceAbi state) &&
      accesses.all (checkBorrowedAction start finish) then
    let loans := sliceViews start slices
    let opened ← run state (acquireViews state.freshHandle loans)
    let changed ← run opened accesses
    run changed (releaseViews (loans.reverse.map View.id))
  else none

def RustBorrowedExec (state : State) (slices : List RustSliceSpec)
    (accesses : Program) (final : State) : Prop :=
  let loans := rustCallViews state slices
  (∀ slice ∈ slices, RustSliceAbiValid state slice) ∧
  (∀ action ∈ accesses, BorrowedAction loans action) ∧
  ∃ opened changed, Runs state (acquireViews state.freshHandle loans) opened ∧
    Runs opened accesses changed ∧ Runs changed (releaseViews (loans.reverse.map View.id)) final

theorem runRustBorrowedCall_correct (state : State) (slices : List RustSliceSpec)
    (accesses : Program) (final : State) :
    runRustBorrowedCall state slices accesses = some final ↔ RustBorrowedExec state slices accesses final := by
  simp only [runRustBorrowedCall, RustBorrowedExec, Option.ite_none_right_eq_some, Bool.and_eq_true,
    List.all_eq_true, checkRustSliceAbi_correct, checkBorrowedAction_correct, bind,
    Option.bind_eq_some_iff, run_correct]
  constructor
  · rintro ⟨⟨abi, authorized⟩, opened, entered, changed, ran, left⟩
    exact ⟨abi, authorized, opened, changed, entered, ran, left⟩
  · rintro ⟨abi, authorized, opened, changed, entered, ran, left⟩
    exact ⟨⟨abi, authorized⟩, opened, entered, changed, ran, left⟩

private theorem borrowedAction_frames {state final : State} {loans : List View} {instruction : Instruction}
    (ran : Step state instruction final) (authorized : BorrowedAction loans instruction)
    (active : ∀ view ∈ loans, state.view view.id = some view) :
    final.resources = state.resources ∧
    ∀ location, (¬ ∃ view ∈ loans, view.location = location ∧ view.mode = .exclusive) →
      final.byte location = state.byte location := by
  cases authorized with
  | read granted =>
    cases ran
    exact ⟨rfl, fun _ _ => rfl⟩
  | write granted =>
    cases ran with
    | writeView found _ writable _ =>
      have same := Option.some.inj (found.symm.trans (active _ granted))
      subst same
      refine ⟨State.resources_store .., fun location outside => ?_⟩
      exact State.store_byte_other _ _ _ _ (fun same => outside
        ⟨_, granted, same, by simpa [AccessMode.Allows] using writable⟩)

private theorem borrowedActions_frame {state final : State} {loans : List View} {accesses : Program}
    (ran : Runs state accesses final) (authorized : ∀ instruction ∈ accesses, BorrowedAction loans instruction)
    (active : ∀ view ∈ loans, state.view view.id = some view) :
    final.resources = state.resources ∧
    ∀ location, (¬ ∃ view ∈ loans, view.location = location ∧ view.mode = .exclusive) →
      final.byte location = state.byte location := by
  induction ran with
  | nil => exact ⟨rfl, fun _ _ => rfl⟩
  | cons first rest ih =>
    have firstFrame := borrowedAction_frames first (authorized _ List.mem_cons_self) active
    have viewList := congrArg ResourceState.views firstFrame.1
    dsimp [State.resources] at viewList
    have remaining := ih (fun _ member => authorized _ (.tail _ member)) (fun _ member => by
      simpa only [State.view, viewList] using active _ member)
    exact ⟨remaining.1.trans firstFrame.1, fun location outside =>
      (remaining.2 location outside).trans (firstFrame.2 location outside)⟩

theorem RustBorrowedExec.restores_scope {state final : State} {slices : List RustSliceSpec} {accesses : Program}
    (ran : RustBorrowedExec state slices accesses final) (compatible : state.ViewsCompatible) :
    final.resources = state.resources ∧
    ∀ location, ¬ RustCallWrites slices location → final.byte location = state.byte location := by
  obtain ⟨_, authorized, opened, changed, entered, ran, released⟩ := ran
  have exactOpen := acquireViews_exact entered
  have active := entered.views_compatible compatible
  have effects := borrowedActions_frame ran authorized (fun view granted =>
    State.view_of_compatible active (by rw [exactOpen]; simp [granted]))
  have kept : changed.views = opened.views := congrArg ResourceState.views effects.1
  have exactClose := acquireViews_release entered kept
  have restored := Option.some.inj ((run_complete released).symm.trans (run_complete exactClose))
  subst final
  refine ⟨?_, fun location outside => ?_⟩
  · change { changed.resources with views := state.views } = state.resources
    rw [effects.1, exactOpen]
    rfl
  · change changed.byte location = state.byte location
    have untouched := effects.2 location fun ⟨view, granted, atByte, writable⟩ => by
      obtain ⟨slice, supplied, within, sameMode⟩ := rustCallViews_origin granted
      exact outside ⟨slice, supplied, atByte ▸ within, sameMode.symm.trans writable⟩
    simpa only [exactOpen, State.byte, State.allocation] using untouched

end Aethel.RustFFI
