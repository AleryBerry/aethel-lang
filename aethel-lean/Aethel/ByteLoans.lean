import Aethel.ResourceCheck

namespace Aethel.Core

/-- Allocate initialized bytes and expose one distinct handle per offset. -/
def byteRegionEntry (owner : OwnerId) (bytes : List UInt8) : Program :=
  .alloc owner bytes :: (List.range bytes.length).map (fun offset => .alias offset owner offset .exclusive)

private theorem aliasRegion_exact (owner : OwnerId) (offsets : List Nat) {initial final : State}
    (ran : Core.run initial (offsets.map (fun i => .alias i owner i .exclusive)) = some final) :
    final.allocations = initial.allocations ∧ final.views = initial.views ∧
      ∀ offset, final.handle offset = if offset ∈ offsets then some ⟨⟨owner, offset⟩, .exclusive⟩
        else initial.handle offset := by
  induction offsets generalizing initial with
  | nil =>
    cases ran
    simp
  | cons offset rest ih =>
    simp only [List.map_cons, Core.run, Option.bind_eq_some_iff] at ran
    obtain ⟨middle, added, continued⟩ := ran
    obtain ⟨allocations, views, handles⟩ := ih continued
    cases execute_sound added
    refine ⟨allocations, views, fun field => ?_⟩
    rw [handles]
    by_cases later : field ∈ rest
    · simp [later]
    · by_cases same : offset = field
      · subst field
        simp [later, State.handle, State.addHandle]
      · simp [later, State.handle, State.addHandle, beq_false_of_ne same, Ne.symm same]

theorem byteRegionEntry_exact (owner : OwnerId) (bytes : List UInt8) {entered : State}
    (ran : Core.run {} (byteRegionEntry owner bytes) = some entered) :
    entered.allocations = [⟨owner, bytes⟩] ∧ entered.views = [] ∧
      ∀ offset, entered.handle offset = if offset < bytes.length then some ⟨⟨owner, offset⟩, .exclusive⟩ else none := by
  change (Core.execute {} (.alloc owner bytes)).bind
    (fun middle => Core.run middle ((List.range bytes.length).map (fun i => .alias i owner i .exclusive))) =
      some entered at ran
  obtain ⟨middle, allocated, rest⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨allocation, views, handles⟩ := aliasRegion_exact owner _ rest
  cases execute_sound allocated
  exact ⟨allocation, views, fun offset => by
    simpa [State.handle, State.addAllocation] using handles offset⟩

def View.acquire (view : View) (temporary : HandleId) : Program :=
  [.alias temporary view.location.allocation view.location.offset view.mode,
    .reserve view.id temporary view.mode, .forget temporary]

def acquireViews (temporary : HandleId) (views : List View) : Program :=
  views.flatMap fun view => view.acquire temporary

def releaseViews (views : List ViewId) : Program :=
  views.map .release

def State.freshHandle (state : State) : HandleId :=
  ((state.handles.map Prod.fst).max?).getD 0 + 1

def State.freshView (state : State) : ViewId :=
  ((state.views.map View.id).max?).getD 0 + 1

def indexedViews (first : ViewId) (cells : List (ByteLocation × AccessMode)) : List View :=
  (cells.zipIdx first).map fun (cell, id) => ⟨id, cell.1, cell.2⟩

theorem indexedViews_ids (first : ViewId) (cells : List (ByteLocation × AccessMode)) :
    (indexedViews first cells).map View.id = List.range' first cells.length := by
  rw [indexedViews, List.map_map]
  change (cells.zipIdx first).map Prod.snd = _
  exact List.zipIdx_map_snd first cells

theorem indexedViews_cells (first : ViewId) (cells : List (ByteLocation × AccessMode)) :
    (indexedViews first cells).map (fun view => (view.location, view.mode)) = cells := by
  rw [indexedViews, List.map_map]
  change (cells.zipIdx first).map Prod.fst = cells
  exact List.zipIdx_map_fst first cells

theorem indexedViews_pairwise (first : ViewId) (cells : List (ByteLocation × AccessMode)) :
    (indexedViews first cells).Pairwise (fun a b => a.location ≠ b.location ∨ a.mode.Compatible b.mode) ↔
      cells.Pairwise (fun a b => a.1 ≠ b.1 ∨ a.2.Compatible b.2) := by
  conv => rhs; rw [← indexedViews_cells first cells, List.pairwise_map]

private theorem find_none_above_ids {α : Type} {items : List α} {key : α → Nat} {id : Nat}
    (above : ((items.map key).max?).getD 0 < id) : items.find? (fun entry => key entry == id) = none := by
  apply List.find?_eq_none.mpr
  intro entry member
  intro matchesId
  have same := beq_iff_eq.mp matchesId
  have bounded := List.le_max?_getD_of_mem (k := 0) (List.mem_map_of_mem (f := key) member)
  omega

theorem State.freshHandle_absent (state : State) : state.handle state.freshHandle = none := by
  unfold State.handle
  rw [find_none_above_ids (key := Prod.fst) (by simp [State.freshHandle])]
  rfl

theorem State.view_absent_from_fresh (state : State) {id : ViewId}
    (bound : state.freshView ≤ id) : state.view id = none := by
  apply find_none_above_ids
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) bound

private theorem filter_not_found {α : Type} {entries : List α} {predicate : α → Bool}
    (absent : entries.find? predicate = none) :
    entries.filter (fun entry => !predicate entry) = entries := by
  apply List.filter_eq_self.mpr
  intro entry member
  simp [Bool.eq_false_iff.mpr (List.find?_eq_none.mp absent entry member)]

private theorem State.removeHandle_after_alias (state : State) (temporary : HandleId)
    (handle : Handle) (fresh : state.handle temporary = none) :
    (state.addHandle temporary handle).removeHandle temporary = state := by
  have reuse : state.handles.filter (fun entry => entry.1 != temporary) = state.handles :=
    filter_not_found (Option.map_eq_none_iff.mp fresh)
  cases state
  simp [State.addHandle, State.removeHandle, reuse]

private theorem State.removeView_after_acquire (state : State) (view : View)
    (fresh : state.view view.id = none) :
    (state.addView view).removeView view.id = state := by
  have retained : state.views.filter (fun old => old.id != view.id) = state.views :=
    filter_not_found fresh
  cases state
  simp [State.addView, State.removeView, retained]

theorem View.acquire_exact {state opened : State} {view : View} {temporary : HandleId}
    (ran : Runs state (view.acquire temporary) opened) :
    opened = state.addView view ∧ state.view view.id = none ∧ state.Available view.location view.mode none := by
  cases ran with
  | cons aliased tail =>
    cases aliased with
    | alias fresh _ =>
      cases tail with
      | cons reserved tail =>
        cases reserved with
        | reserve newId found _ _ available =>
          simp [State.handle, State.addHandle] at found
          subst found
          cases tail with
          | cons dropped tail =>
            cases dropped
            cases tail
            exact ⟨State.removeHandle_after_alias (state.addView view) temporary
              ⟨view.location, view.mode⟩ fresh, newId, available⟩

theorem acquireViews_exact {state opened : State} {views : List View} {temporary : HandleId}
    (ran : Runs state (acquireViews temporary views) opened) :
    opened = { state with views := views.reverse ++ state.views } := by
  induction views generalizing state with
  | nil => cases ran; rfl
  | cons view tail ih =>
    have computed := run_complete ran
    change run state (view.acquire temporary ++ acquireViews temporary tail) = some opened at computed
    rw [run_append, Option.bind_eq_some_iff] at computed
    obtain ⟨_, began, rest⟩ := computed
    obtain ⟨rfl, _⟩ := View.acquire_exact (run_sound began)
    rw [ih (run_sound rest)]
    simp [State.addView, List.reverse_cons, List.append_assoc]

theorem acquireViews_permissions {state opened : State} {views : List View} {temporary : HandleId}
    (ran : Runs state (acquireViews temporary views) opened) :
    (∀ view ∈ views, state.Available view.location view.mode none) ∧
      views.Pairwise (fun a b => a.location ≠ b.location ∨ a.mode.Compatible b.mode) := by
  induction views generalizing state with
  | nil => simp
  | cons view tail ih =>
    have computed := run_complete ran
    change run state (view.acquire temporary ++ acquireViews temporary tail) = some opened at computed
    rw [run_append, Option.bind_eq_some_iff] at computed
    obtain ⟨_, began, rest⟩ := computed
    obtain ⟨rfl, _, available⟩ := View.acquire_exact (run_sound began)
    obtain ⟨later, apart⟩ := ih (run_sound rest)
    constructor
    · intro requested member
      rcases List.mem_cons.mp member with rfl | fromTail
      · exact available
      · intro existing present
        exact later requested fromTail existing (List.mem_cons_of_mem _ present)
    · refine List.pairwise_cons.mpr ⟨fun requested member => ?_, apart⟩
      rcases later requested member view List.mem_cons_self with impossible | distinct | compatible
      · cases impossible
      · exact .inl (Ne.symm distinct)
      · exact .inr ⟨compatible.2, compatible.1⟩

private theorem View.acquire_of_available {state : State} {view : View} {temporary : HandleId}
    {byte : UInt8} (handleFresh : state.handle temporary = none) (viewFresh : state.view view.id = none)
    (live : state.byte view.location = some byte) (allowed : state.Available view.location view.mode none) :
    Runs state (view.acquire temporary) (state.addView view) := by
  let handle : Handle := ⟨view.location, view.mode⟩
  let aliased := state.addHandle temporary handle
  have found : aliased.handle temporary = some handle := by
    simp [aliased, State.handle, State.addHandle]
  have ownMode : handle.mode.Allows view.mode := by
    change view.mode.Allows view.mode
    cases view.mode <;> simp [AccessMode.Allows]
  have reserved : Step aliased (.reserve view.id temporary view.mode) (aliased.addView view) :=
    .reserve (s := aliased) viewFresh found live ownMode allowed
  have dropped : Step (aliased.addView view) (.forget temporary) (state.addView view) := by
    have restored := State.removeHandle_after_alias (state.addView view) temporary handle handleFresh
    exact restored ▸ Step.forget (s := aliased.addView view) found
  exact .cons (.alias handleFresh live) (.cons reserved (.cons dropped .nil))

theorem acquireViews_of_available {state : State} {views : List View} {temporary : HandleId}
    (handleFresh : state.handle temporary = none)
    (viewFresh : ∀ view ∈ views, state.view view.id = none)
    (live : ∀ view ∈ views, ∃ value, state.byte view.location = some value)
    (allowed : ∀ view ∈ views, state.Available view.location view.mode none)
    (distinct : (views.map View.id).Nodup)
    (apart : views.Pairwise (fun a b => a.location ≠ b.location ∨ a.mode.Compatible b.mode)) :
    ∃ opened, Runs state (acquireViews temporary views) opened := by
  induction views generalizing state with
  | nil => exact ⟨state, .nil⟩
  | cons view tail ih =>
    obtain ⟨_, byte⟩ := live view List.mem_cons_self
    have begins := View.acquire_of_available handleFresh (viewFresh view List.mem_cons_self)
      byte (allowed view List.mem_cons_self)
    obtain ⟨differentId, tailIds⟩ := List.nodup_cons.mp distinct
    obtain ⟨separate, tailApart⟩ := List.pairwise_cons.mp apart
    have freshLater : ∀ child ∈ tail, (state.addView view).view child.id = none := by
      intro child member
      have different : view.id ≠ child.id := fun same =>
        differentId (same ▸ List.mem_map_of_mem member)
      simpa [State.view, State.addView, beq_false_of_ne different] using viewFresh child (.tail _ member)
    have allowedLater : ∀ child ∈ tail, (state.addView view).Available child.location child.mode none := by
      intro child member existing present
      rcases List.mem_cons.mp present with rfl | previous
      · rcases separate child member with disjoint | shared
        · exact .inr (.inl (Ne.symm disjoint))
        · exact .inr (.inr ⟨shared.2, shared.1⟩)
      · exact allowed child (.tail _ member) existing previous
    obtain ⟨opened, remaining⟩ := ih (state := state.addView view) handleFresh freshLater
      (fun child member => live child (.tail _ member)) allowedLater tailIds tailApart
    exact ⟨opened, begins.append remaining⟩

theorem acquireIndexedViews {state : State} {cells : List (ByteLocation × AccessMode)}
    (live : ∀ cell ∈ cells, ∃ byte, state.byte cell.1 = some byte)
    (available : ∀ cell ∈ cells, state.Available cell.1 cell.2 none)
    (apart : cells.Pairwise (fun a b => a.1 ≠ b.1 ∨ a.2.Compatible b.2)) :
    ∃ opened, Runs state (acquireViews state.freshHandle (indexedViews state.freshView cells)) opened := by
  let loans := indexedViews state.freshView cells
  have memberCell (view : View) (present : view ∈ loans) : (view.location, view.mode) ∈ cells := by
    rw [← indexedViews_cells state.freshView cells]
    exact List.mem_map_of_mem present
  apply acquireViews_of_available state.freshHandle_absent
  · intro view present
    apply state.view_absent_from_fresh
    have memberId := List.mem_map_of_mem (f := View.id) present
    rw [indexedViews_ids] at memberId
    exact (List.mem_range'_1.mp memberId).1
  · exact fun view present => live _ (memberCell view present)
  · exact fun view present => available _ (memberCell view present)
  · rw [indexedViews_ids]
    exact List.nodup_range' _
  · exact (indexedViews_pairwise ..).mpr apart

theorem State.view_of_compatible {state : State} {view : View}
    (compatible : state.ViewsCompatible) (member : view ∈ state.views) :
    state.view view.id = some view := by
  unfold State.view
  unfold State.ViewsCompatible at compatible
  generalize state.views = views at compatible member ⊢
  induction views with
  | nil => contradiction
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | previous
    · simp
    · have ⟨separate, remaining⟩ := List.pairwise_cons.mp compatible
      simp [beq_eq_false_iff_ne.mpr (separate view previous).1, ih remaining previous]

theorem acquireViews_member {state opened : State} {views : List View} {temporary : HandleId}
    (ran : Runs state (acquireViews temporary views) opened) {view : View} (granted : view ∈ views) :
    view ∈ opened.views := by
  rw [acquireViews_exact ran]
  simp [granted]

theorem acquireViews_release {state opened changed : State} {views : List View} {temporary : HandleId}
    (ran : Runs state (acquireViews temporary views) opened) (kept : changed.views = opened.views) :
    Runs changed (releaseViews (views.reverse.map View.id)) { changed with views := state.views } := by
  induction views generalizing state with
  | nil =>
    cases ran
    cases changed
    simp_all [releaseViews]
    exact .nil
  | cons view tail ih =>
    have computed := run_complete ran
    change run state (view.acquire temporary ++ acquireViews temporary tail) = some opened at computed
    rw [run_append, Option.bind_eq_some_iff] at computed
    obtain ⟨middle, began, rest⟩ := computed
    obtain ⟨rfl, fresh, _⟩ := View.acquire_exact (run_sound began)
    have releaseTail := ih (run_sound rest)
    have restored := State.removeView_after_acquire { changed with views := state.views } view fresh
    have releaseHead : Step { changed with views := (state.addView view).views } (.release view.id)
        { changed with views := state.views } := by
      have found : ({ changed with views := (state.addView view).views } : State).view view.id = some view := by
        simp [State.view, State.addView]
      exact restored ▸ Step.release found
    simp only [List.reverse_cons, releaseViews, List.map_append, List.map_cons, List.map_nil]
    exact releaseTail.append (.cons releaseHead .nil)

end Aethel.Core
