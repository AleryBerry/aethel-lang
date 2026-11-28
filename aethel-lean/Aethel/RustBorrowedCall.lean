import Aethel.RustFFI
import Aethel.ByteLoans

namespace Aethel.RustFFI

open Core

private def sliceCells (slices : List RustSliceSpec) : List (ByteLocation × AccessMode) :=
  slices.flatMap fun slice => slice.locations.map (·, slice.mode)

private def sliceViews (first : ViewId) (slices : List RustSliceSpec) : List View :=
  indexedViews first (sliceCells slices)

def rustCallViews (state : State) (slices : List RustSliceSpec) : List View :=
  sliceViews state.freshView slices

private def borrowedBytes (slices : List RustSliceSpec) : Nat :=
  (slices.map RustSliceSpec.byteLen).sum

private theorem rustCallViews_ids (state : State) (slices : List RustSliceSpec) :
    (rustCallViews state slices).map View.id = List.range' state.freshView (borrowedBytes slices) := by
  rw [rustCallViews, sliceViews, indexedViews_ids]
  simp [sliceCells, borrowedBytes, RustSliceSpec.locations, List.length_flatMap]

private theorem sliceCells_origin {slices : List RustSliceSpec} {cell : ByteLocation × AccessMode}
    (present : cell ∈ sliceCells slices) :
    ∃ slice ∈ slices, cell.1 ∈ slice.locations ∧ cell.2 = slice.mode := by
  obtain ⟨slice, supplied, inSlice⟩ := List.mem_flatMap.mp present
  obtain ⟨byte, within, rfl⟩ := List.mem_map.mp inSlice
  exact ⟨slice, supplied, within, rfl⟩

theorem rustCallViews_origin {state : State} {slices : List RustSliceSpec} {view : View}
    (granted : view ∈ rustCallViews state slices) :
    ∃ slice ∈ slices, view.location ∈ slice.locations ∧ view.mode = slice.mode := by
  have cell := List.mem_map_of_mem (f := fun view : View => (view.location, view.mode)) granted
  rw [rustCallViews, sliceViews, indexedViews_cells] at cell
  exact sliceCells_origin cell

private theorem rustCallViews_covers {state : State} {slices : List RustSliceSpec}
    {slice : RustSliceSpec} {location : ByteLocation} (supplied : slice ∈ slices)
    (within : location ∈ slice.locations) :
    ∃ view ∈ rustCallViews state slices, view.location = location ∧ view.mode = slice.mode := by
  have cell : (location, slice.mode) ∈ sliceCells slices :=
    List.mem_flatMap.mpr ⟨slice, supplied, List.mem_map_of_mem within⟩
  rw [← indexedViews_cells state.freshView (sliceCells slices)] at cell
  obtain ⟨view, granted, same⟩ := List.mem_map.mp cell
  exact ⟨view, granted, congrArg Prod.fst same, congrArg Prod.snd same⟩

theorem rustBorrowPlan_of_acquired {state opened : State} {slices : List RustSliceSpec}
    (abi : ∀ slice ∈ slices, RustSliceAbiValid state slice)
    (entered : Runs state (acquireViews state.freshHandle (rustCallViews state slices)) opened) :
    checkRustBorrowPlan state slices = true := by
  obtain ⟨available, apart⟩ := acquireViews_permissions entered
  apply (checkRustBorrowPlan_correct state slices).mpr
  constructor
  · intro slice supplied
    apply (abi slice supplied).with_available
    intro location within
    obtain ⟨view, granted, atByte, mode⟩ :=
      rustCallViews_covers (state := state) supplied within
    simpa only [atByte, mode] using available view granted
  · have pairCells := (indexedViews_pairwise state.freshView (sliceCells slices)).mp apart
    have between := (List.pairwise_flatMap.mp pairCells).2
    apply between.imp
    intro left right compare location withinLeft withinRight
    exact (compare (location, left.mode) (List.mem_map_of_mem withinLeft)
      (location, right.mode) (List.mem_map_of_mem withinRight)).resolve_left (fun different => different rfl)

private theorem sliceCells_pairwise {slices : List RustSliceSpec}
    (compatible : slices.Pairwise RustSlicesCompatible) :
    (sliceCells slices).Pairwise (fun a b => a.1 ≠ b.1 ∨ a.2.Compatible b.2) := by
  unfold sliceCells
  apply List.pairwise_flatMap.mpr
  constructor
  · intro slice _
    simp only [RustSliceSpec.locations, List.pairwise_map]
    exact (List.nodup_range (n := slice.byteLen)).imp fun distinct => .inl fun same =>
      distinct (Nat.add_left_cancel (congrArg ByteLocation.offset same))
  · apply compatible.imp
    rintro first second apart _ inFirst _ inSecond
    obtain ⟨a, aMember, rfl⟩ := List.mem_map.mp inFirst
    obtain ⟨b, bMember, rfl⟩ := List.mem_map.mp inSecond
    by_cases same : a = b
    · subst b
      exact .inr (apart a aMember bMember)
    · exact .inl same

theorem checkRustBorrowPlan_acquires (state : State) (slices : List RustSliceSpec) :
    checkRustBorrowPlan state slices = true ↔
      (∀ slice ∈ slices, RustSliceAbiValid state slice) ∧
        ∃ opened, Runs state (acquireViews state.freshHandle (rustCallViews state slices)) opened := by
  constructor
  · intro accepted
    obtain ⟨valid, apart⟩ := (checkRustBorrowPlan_correct state slices).mp accepted
    refine ⟨fun slice supplied => (valid slice supplied).abi, ?_⟩
    apply acquireIndexedViews
    · intro cell granted
      obtain ⟨slice, supplied, within, _⟩ := sliceCells_origin granted
      exact (valid slice supplied).abi.byte_initialized within
    · intro cell granted
      obtain ⟨slice, supplied, within, mode⟩ := sliceCells_origin granted
      exact mode.symm ▸ (valid slice supplied).available within
    · exact sliceCells_pairwise apart
  · rintro ⟨abi, opened, entered⟩
    exact rustBorrowPlan_of_acquired abi entered

inductive RustViewAction (loans : List View) (writeAllowed : View → Prop) : Instruction → Prop where
  | read : view ∈ loans → RustViewAction loans writeAllowed (.readView view.id)
  | write : view ∈ loans → writeAllowed view → RustViewAction loans writeAllowed (.writeView view.id value)

abbrev BorrowedAction (loans : List View) := RustViewAction loans (fun _ => True)

def AuthorizedRustTrace (state : State) (slices : List RustSliceSpec) (accesses : Program) : Prop :=
  ∀ instruction ∈ accesses, RustViewAction (rustCallViews state slices) (fun view => view.mode = .exclusive) instruction

private theorem RustViewAction.borrowed {loans : List View} {writeAllowed : View → Prop} {instruction : Instruction}
    (permitted : RustViewAction loans writeAllowed instruction) : BorrowedAction loans instruction := by
  cases permitted with
  | read granted => exact .read granted
  | write granted _ => exact .write granted trivial

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
      exact .write granted trivial
  · intro admitted
    cases admitted with
    | read granted | write granted _ =>
      exact decide_eq_true (idGranted _ |>.mp (List.mem_map_of_mem granted))

def RustCallWrites (slices : List RustSliceSpec) (location : ByteLocation) : Prop :=
  ∃ slice ∈ slices, location ∈ slice.locations ∧ slice.mode = .exclusive

/-- Execute the finite operations exposed by a synchronous Rust adapter.
The ABI check handles representation and bounds, and actual byte
reservations enforce compatibility with every caller and sibling view. -/
def runRustBorrowedCall (state : State) (slices : List RustSliceSpec) (accesses : Program) : Option State := do
  let start := state.freshView
  let finish := start + borrowedBytes slices
  if checkRustBorrowPlan state slices &&
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
    List.all_eq_true, checkRustBorrowPlan_correct, checkBorrowedAction_correct, bind,
    Option.bind_eq_some_iff, run_correct]
  constructor
  · rintro ⟨⟨⟨valid, _⟩, authorized⟩, opened, entered, changed, ran, left⟩
    exact ⟨fun slice supplied => (valid slice supplied).abi, authorized, opened, changed, entered, ran, left⟩
  · rintro ⟨abi, authorized, opened, changed, entered, ran, left⟩
    have ready := (checkRustBorrowPlan_correct state slices).mp (rustBorrowPlan_of_acquired abi entered)
    exact ⟨⟨ready, authorized⟩, opened, entered, changed, ran, left⟩

theorem checkRustBorrowPlan_empty_trace {state : State} {slices : List RustSliceSpec}
    (checked : checkRustBorrowPlan state slices = true) :
    runRustBorrowedCall state slices [] = some state := by
  obtain ⟨abi, opened, entered⟩ := (checkRustBorrowPlan_acquires state slices).mp checked
  have restored := acquireViews_release (changed := opened) entered rfl
  have same : { opened with views := state.views } = state := by
    rw [acquireViews_exact entered]
  exact (runRustBorrowedCall_correct state slices [] state).mpr
    ⟨abi, by simp, opened, opened, entered, .nil, same ▸ restored⟩

private theorem borrowedAction_frames {state final : State} {loans : List View} {instruction : Instruction}
    (ran : Step state instruction final) (authorized : BorrowedAction loans instruction)
    (active : ∀ view ∈ loans, state.view view.id = some view) :
    RustViewAction loans (fun view => view.mode = .exclusive) instruction ∧ final.resources = state.resources ∧
    ∀ location, (¬ ∃ view ∈ loans, view.location = location ∧ view.mode = .exclusive) →
      final.byte location = state.byte location := by
  cases authorized with
  | read granted =>
    cases ran
    exact ⟨.read granted, rfl, fun _ _ => rfl⟩
  | write granted _ =>
    cases ran with
    | writeView found _ writable _ =>
      have same := Option.some.inj (found.symm.trans (active _ granted))
      subst same
      have exclusive := writable.resolve_left (by decide)
      exact ⟨.write granted exclusive, State.resources_store .., fun location outside =>
        State.store_byte_other _ _ location _ (fun same => outside ⟨_, granted, same, exclusive⟩)⟩

private theorem borrowedActions_frame {state final : State} {loans : List View} {accesses : Program}
    (ran : Runs state accesses final) (authorized : ∀ instruction ∈ accesses, BorrowedAction loans instruction)
    (active : ∀ view ∈ loans, state.view view.id = some view) :
    (∀ action ∈ accesses, RustViewAction loans (fun view => view.mode = .exclusive) action) ∧
    final.resources = state.resources ∧
    ∀ location, (¬ ∃ view ∈ loans, view.location = location ∧ view.mode = .exclusive) →
      final.byte location = state.byte location := by
  induction ran with
  | nil => exact ⟨by simp, rfl, fun _ _ => rfl⟩
  | cons first rest ih =>
    obtain ⟨firstAllowed, firstResources, firstFrame⟩ :=
      borrowedAction_frames first (authorized _ List.mem_cons_self) active
    have viewList := congrArg ResourceState.views firstResources
    dsimp [State.resources] at viewList
    obtain ⟨remainingAllowed, remainingResources, remainingFrame⟩ :=
      ih (fun _ member => authorized _ (.tail _ member)) (fun _ member => by
      simpa only [State.view, viewList] using active _ member)
    refine ⟨?_, remainingResources.trans firstResources, fun location outside =>
      (remainingFrame location outside).trans (firstFrame location outside)⟩
    intro action member
    rcases List.mem_cons.mp member with rfl | later
    · exact firstAllowed
    · exact remainingAllowed action later

private theorem borrowedActions_run {state : State} {loans : List View} {accesses : Program}
    (permitted : ∀ action ∈ accesses, RustViewAction loans (fun view => view.mode = .exclusive) action)
    (compatible : state.ViewsCompatible)
    (ready : ∀ view ∈ loans, view ∈ state.views ∧ ∃ value, state.byte view.location = some value) :
    ∃ final, Runs state accesses final ∧ final.resources = state.resources := by
  induction accesses generalizing state with
  | nil => exact ⟨state, .nil, rfl⟩
  | cons action rest ih =>
    have admitted := permitted action List.mem_cons_self
    have canStep : ∃ next, Step state action next := by
      cases admitted with
      | read granted =>
        obtain ⟨active, _, live⟩ := ready _ granted
        exact ⟨_, .readView (State.view_of_compatible compatible active) live
          (state.available_through_view compatible active (.inl rfl))⟩
      | write granted writable =>
        obtain ⟨active, _, live⟩ := ready _ granted
        have allowed : AccessMode.Allows _ .exclusive := .inr writable
        exact ⟨_, .writeView (State.view_of_compatible compatible active) live allowed
          (state.available_through_view compatible active allowed)⟩
    obtain ⟨next, stepped⟩ := canStep
    have preserved := (borrowedAction_frames stepped admitted.borrowed
      (fun view granted => State.view_of_compatible compatible (ready view granted).1)).2.1
    have viewList : next.views = state.views := congrArg ResourceState.views preserved
    have stillReady : ∀ view ∈ loans, view ∈ next.views ∧ ∃ value, next.byte view.location = some value := by
      intro view granted
      obtain ⟨active, _, live⟩ := ready view granted
      refine ⟨viewList.symm ▸ active, Option.isSome_iff_exists.mp ?_⟩
      rw [← State.resources_live, preserved, State.resources_live, live]
      rfl
    obtain ⟨final, ran, unchanged⟩ := ih (fun action member => permitted action (.tail _ member))
      (stepped.views_compatible compatible) stillReady
    exact ⟨final, .cons stepped ran, unchanged.trans preserved⟩

private theorem RustBorrowedExec.scope_and_trace {state final : State} {slices : List RustSliceSpec}
    {accesses : Program}
    (ran : RustBorrowedExec state slices accesses final) (compatible : state.ViewsCompatible) :
    AuthorizedRustTrace state slices accesses ∧ final.resources = state.resources ∧
    ∀ location, ¬ RustCallWrites slices location → final.byte location = state.byte location := by
  obtain ⟨_, authorized, opened, changed, entered, ran, released⟩ := ran
  have exactOpen := acquireViews_exact entered
  have active := entered.views_compatible compatible
  obtain ⟨permitted, resources, frame⟩ := borrowedActions_frame ran authorized (fun view granted =>
    State.view_of_compatible active (acquireViews_member entered granted))
  have kept : changed.views = opened.views := congrArg ResourceState.views resources
  have exactClose := acquireViews_release entered kept
  have restored := Option.some.inj ((run_complete released).symm.trans (run_complete exactClose))
  subst final
  refine ⟨permitted, ?_, fun location outside => ?_⟩
  · change { changed.resources with views := state.views } = state.resources
    rw [resources, exactOpen]
    rfl
  · change changed.byte location = state.byte location
    have untouched := frame location fun ⟨view, granted, atByte, writable⟩ => by
      obtain ⟨slice, supplied, within, sameMode⟩ := rustCallViews_origin granted
      exact outside ⟨slice, supplied, atByte ▸ within, sameMode.symm.trans writable⟩
    simpa only [exactOpen, State.byte, State.allocation] using untouched

theorem RustBorrowedExec.restores_scope {state final : State} {slices : List RustSliceSpec} {accesses : Program}
    (ran : RustBorrowedExec state slices accesses final) (compatible : state.ViewsCompatible) :
    final.resources = state.resources ∧
    ∀ location, ¬ RustCallWrites slices location → final.byte location = state.byte location :=
  (ran.scope_and_trace compatible).2

theorem RustBorrowedExec.trace {state final : State} {slices : List RustSliceSpec} {accesses : Program}
    (ran : RustBorrowedExec state slices accesses final) :
    ∃ instructions, Runs state instructions final := by
  obtain ⟨_, _, _, _, entered, accessed, released⟩ := ran
  exact ⟨_, entered.append (accessed.append released)⟩

/-- An adapter supplying a finite trace of authorized reads and writes can
complete every modeled access and return the caller's reservations. -/
theorem runRustBorrowedCall_total {state : State} {slices : List RustSliceSpec} {accesses : Program}
    (checked : checkRustBorrowPlan state slices = true) (compatible : state.ViewsCompatible)
    (permitted : AuthorizedRustTrace state slices accesses) :
    ∃ final, runRustBorrowedCall state slices accesses = some final ∧ final.resources = state.resources ∧
      ∀ location, ¬ RustCallWrites slices location → final.byte location = state.byte location := by
  obtain ⟨abi, opened, entered⟩ := (checkRustBorrowPlan_acquires state slices).mp checked
  have exactOpen := acquireViews_exact entered
  have ready : ∀ view ∈ rustCallViews state slices, view ∈ opened.views ∧
      ∃ value, opened.byte view.location = some value := by
    intro view granted
    obtain ⟨slice, supplied, within, _⟩ := rustCallViews_origin granted
    refine ⟨acquireViews_member entered granted, ?_⟩
    simpa only [exactOpen, State.byte, State.allocation] using (abi slice supplied).byte_initialized within
  obtain ⟨changed, ran, resources⟩ := borrowedActions_run permitted (entered.views_compatible compatible) ready
  have released := acquireViews_release entered (congrArg ResourceState.views resources)
  have completed : RustBorrowedExec state slices accesses _ :=
    ⟨abi, fun instruction member => (permitted instruction member).borrowed, opened, changed, entered, ran, released⟩
  exact ⟨_, (runRustBorrowedCall_correct ..).mpr completed, completed.restores_scope compatible⟩

theorem runRustBorrowedCall_succeeds_iff {state : State} {slices : List RustSliceSpec} {accesses : Program}
    (compatible : state.ViewsCompatible) :
    (∃ final, runRustBorrowedCall state slices accesses = some final) ↔
      checkRustBorrowPlan state slices = true ∧ AuthorizedRustTrace state slices accesses := by
  constructor
  · rintro ⟨final, computed⟩
    have completed := (runRustBorrowedCall_correct ..).mp computed
    have permitted := (completed.scope_and_trace compatible).1
    obtain ⟨abi, _, _, _, entered, _, _⟩ := completed
    exact ⟨rustBorrowPlan_of_acquired abi entered, permitted⟩
  · rintro ⟨plan, permitted⟩
    obtain ⟨final, ran, _⟩ := runRustBorrowedCall_total plan compatible permitted
    exact ⟨final, ran⟩

/-- A foreign access names a concrete argument and a byte within its slice.
It has no access to the caller's machine-generated view identities. -/
structure RustArgumentByte where
  argument : Nat
  byte : Nat
  deriving Repr, DecidableEq

def RustArgumentByte.Resolves (address : RustArgumentByte) (slices : List RustSliceSpec)
    (slice : RustSliceSpec) (ordinal : Nat) : Prop :=
  slices[address.argument]? = some slice ∧ address.byte < slice.byteLen ∧
    ordinal = ((slices.take address.argument).map RustSliceSpec.byteLen).sum + address.byte

private def resolveRustArgument (offset : Nat) : List RustSliceSpec → Nat → Option (RustSliceSpec × Nat)
  | [], _ => none
  | slice :: _, 0 => if offset < slice.byteLen then some (slice, offset) else none
  | slice :: rest, argument + 1 =>
    (resolveRustArgument offset rest argument).map fun (found, ordinal) => (found, slice.byteLen + ordinal)

private theorem resolveRustArgument_correct (slices : List RustSliceSpec) (address : RustArgumentByte)
    (slice : RustSliceSpec) (ordinal : Nat) :
    resolveRustArgument address.byte slices address.argument = some (slice, ordinal) ↔
      address.Resolves slices slice ordinal := by
  obtain ⟨argument, offset⟩ := address
  induction slices generalizing argument ordinal with
  | nil => simp [resolveRustArgument, RustArgumentByte.Resolves]
  | cons head rest ih =>
    cases argument with
    | zero =>
      simp [resolveRustArgument, RustArgumentByte.Resolves, Option.ite_none_right_eq_some,
        and_left_comm, eq_comm (a := offset)]
      rintro rfl rfl
      rfl
    | succ argument =>
      simp only [resolveRustArgument, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq,
        RustArgumentByte.Resolves, List.getElem?_cons_succ, List.take_succ_cons, List.map_cons,
        List.sum_cons]
      constructor
      · rintro ⟨found, previous, located, rfl, rfl⟩
        obtain ⟨declared, within, rfl⟩ := (ih previous argument).mp located
        exact ⟨declared, within, (Nat.add_assoc ..).symm⟩
      · rintro ⟨declared, within, rfl⟩
        exact ⟨slice, _, (ih _ argument).mpr ⟨declared, within, rfl⟩, rfl, (Nat.add_assoc ..).symm⟩

private theorem RustArgumentByte.Resolves.cell {slices : List RustSliceSpec}
    {address : RustArgumentByte} {slice : RustSliceSpec} {ordinal : Nat}
    (resolved : address.Resolves slices slice ordinal) :
    (sliceCells slices)[ordinal]? = some (⟨slice.owner, slice.byteOffset + address.byte⟩, slice.mode) := by
  obtain ⟨argument, offset⟩ := address
  induction slices generalizing argument ordinal with
  | nil => simp [RustArgumentByte.Resolves] at resolved
  | cons head rest ih =>
    cases argument with
    | zero =>
      obtain ⟨declared, within, rfl⟩ := resolved
      cases Option.some.inj declared
      have bound : offset < slice.locations.length := by simpa [RustSliceSpec.locations] using within
      rw [sliceCells, List.flatMap_cons, List.getElem?_append_left (by simpa using bound)]
      simp [RustSliceSpec.locations, List.getElem?_range within]
    | succ argument =>
      obtain ⟨declared, within, rfl⟩ := resolved
      have tail : (RustArgumentByte.mk argument offset).Resolves rest slice
          (((rest.take argument).map RustSliceSpec.byteLen).sum + offset) := ⟨declared, within, rfl⟩
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      rw [sliceCells, List.flatMap_cons, List.getElem?_append_right (by
        simp [RustSliceSpec.locations]
        omega)]
      rw [List.length_map, RustSliceSpec.locations, List.length_map, List.length_range,
        Nat.add_assoc, Nat.add_sub_cancel_left]
      exact ih argument tail

theorem RustArgumentByte.Resolves.loan {state : State} {slices : List RustSliceSpec}
    {address : RustArgumentByte} {slice : RustSliceSpec} {ordinal : Nat}
    (resolved : address.Resolves slices slice ordinal) :
    ⟨state.freshView + ordinal, ⟨slice.owner, slice.byteOffset + address.byte⟩, slice.mode⟩ ∈
      rustCallViews state slices := by
  apply List.mem_map.mpr
  exact ⟨((⟨slice.owner, slice.byteOffset + address.byte⟩, slice.mode), state.freshView + ordinal),
    List.mk_add_mem_zipIdx_iff_getElem?.mpr resolved.cell, rfl⟩

structure RustAdapterAccess where
  address : RustArgumentByte
  write : Option UInt8 := none
  deriving Repr, DecidableEq

def RustAdapterAccess.Lowers (slices : List RustSliceSpec) (start : ViewId)
    (access : RustAdapterAccess) (instruction : Instruction) : Prop :=
  ∃ slice ordinal, access.address.Resolves slices slice ordinal ∧
    match access.write with
    | none => instruction = .readView (start + ordinal)
    | some value => slice.mode = .exclusive ∧ instruction = .writeView (start + ordinal) value

def RustAdapterAccess.lower (slices : List RustSliceSpec) (start : ViewId)
    (access : RustAdapterAccess) : Option Instruction := do
  let (slice, ordinal) ← resolveRustArgument access.address.byte slices access.address.argument
  let id := start + ordinal
  match access.write with
  | none => pure (.readView id)
  | some value => if slice.mode = .exclusive then some (.writeView id value) else none

theorem RustAdapterAccess.lower_correct (slices : List RustSliceSpec) (start : ViewId)
    (access : RustAdapterAccess) (instruction : Instruction) :
    access.lower slices start = some instruction ↔ access.Lowers slices start instruction := by
  cases write : access.write <;>
    simp [lower, Lowers, bind, pure, Option.bind_eq_some_iff, Prod.exists,
      resolveRustArgument_correct, write, Option.ite_none_right_eq_some, eq_comm (b := instruction)]

theorem RustAdapterAccess.Lowers.authorized {state : State} {slices : List RustSliceSpec}
    {access : RustAdapterAccess} {instruction : Instruction}
    (lowered : access.Lowers slices state.freshView instruction) :
    RustViewAction (rustCallViews state slices) (fun view => view.mode = .exclusive) instruction := by
  obtain ⟨slice, ordinal, resolved, uses⟩ := lowered
  cases write : access.write
  · rw [write] at uses
    cases uses
    exact .read resolved.loan
  · rw [write] at uses
    obtain ⟨exclusive, rfl⟩ := uses
    exact .write resolved.loan exclusive

inductive RustAdapterTraceLowers (slices : List RustSliceSpec) (start : ViewId) :
    List RustAdapterAccess → Program → Prop where
  | nil : RustAdapterTraceLowers slices start [] []
  | cons : access.Lowers slices start instruction → RustAdapterTraceLowers slices start rest instructions →
      RustAdapterTraceLowers slices start (access :: rest) (instruction :: instructions)

def lowerRustAdapterTrace (slices : List RustSliceSpec) (start : ViewId)
    (trace : List RustAdapterAccess) : Option Program :=
  trace.mapM (RustAdapterAccess.lower slices start)

theorem lowerRustAdapterTrace_correct (slices : List RustSliceSpec) (start : ViewId)
    (trace : List RustAdapterAccess) (program : Program) :
    lowerRustAdapterTrace slices start trace = some program ↔ RustAdapterTraceLowers slices start trace program := by
  induction trace generalizing program with
  | nil =>
    constructor
    · intro computed
      obtain rfl := Option.some.inj computed
      exact .nil
    · intro lowered
      cases lowered
      rfl
  | cons head tail ih =>
    simp only [lowerRustAdapterTrace, List.mapM_cons, bind, pure, Option.bind_eq_some_iff,
      Option.some.injEq, RustAdapterAccess.lower_correct]
    constructor
    · rintro ⟨instruction, lowered, rest, computed, rfl⟩
      exact .cons lowered ((ih rest).mp computed)
    · intro lowered
      cases lowered with
      | cons first rest => exact ⟨_, first, _, (ih _).mpr rest, rfl⟩

theorem RustAdapterTraceLowers.authorized {state : State} {slices : List RustSliceSpec}
    {trace : List RustAdapterAccess} {program : Program}
    (lowered : RustAdapterTraceLowers slices state.freshView trace program) :
    AuthorizedRustTrace state slices program := by
  induction lowered with
  | nil => simp [AuthorizedRustTrace]
  | cons first _ ih =>
    intro instruction member
    rcases List.mem_cons.mp member with rfl | later
    · exact first.authorized
    · exact ih instruction later

def runRustAdapterTrace (state : State) (slices : List RustSliceSpec)
    (trace : List RustAdapterAccess) : Option State := do
  let program ← lowerRustAdapterTrace slices state.freshView trace
  runRustBorrowedCall state slices program

theorem runRustAdapterTrace_correct (state : State) (slices : List RustSliceSpec)
    (trace : List RustAdapterAccess) (final : State) :
    runRustAdapterTrace state slices trace = some final ↔
      ∃ program, RustAdapterTraceLowers slices state.freshView trace program ∧
        RustBorrowedExec state slices program final := by
  simp [runRustAdapterTrace, bind, Option.bind_eq_some_iff, lowerRustAdapterTrace_correct,
    runRustBorrowedCall_correct]

theorem runRustAdapterTrace_total {state : State} {slices : List RustSliceSpec}
    {trace : List RustAdapterAccess} {program : Program} (checked : checkRustBorrowPlan state slices = true)
    (compatible : state.ViewsCompatible) (lowered : RustAdapterTraceLowers slices state.freshView trace program) :
    ∃ final, runRustAdapterTrace state slices trace = some final ∧ final.resources = state.resources ∧
      ∀ location, ¬ RustCallWrites slices location → final.byte location = state.byte location := by
  obtain ⟨final, finished, restored, frame⟩ := runRustBorrowedCall_total checked compatible lowered.authorized
  exact ⟨final, (runRustAdapterTrace_correct ..).mpr
    ⟨program, lowered, (runRustBorrowedCall_correct ..).mp finished⟩, restored, frame⟩

end Aethel.RustFFI
