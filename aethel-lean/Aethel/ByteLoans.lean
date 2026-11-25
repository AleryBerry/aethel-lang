import Aethel.ResourceCheck

namespace Aethel.Core

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
    opened = state.addView view ∧ state.view view.id = none := by
  cases ran with
  | cons aliased tail =>
    cases aliased with
    | alias fresh _ =>
      cases tail with
      | cons reserved tail =>
        cases reserved with
        | reserve newId found _ _ _ =>
          simp [State.handle, State.addHandle] at found
          subst found
          cases tail with
          | cons dropped tail =>
            cases dropped
            cases tail
            exact ⟨State.removeHandle_after_alias (state.addView view) temporary
              ⟨view.location, view.mode⟩ fresh, newId⟩

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
    obtain ⟨rfl, fresh⟩ := View.acquire_exact (run_sound began)
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
