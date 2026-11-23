import Aethel.RecordViews
import Aethel.RecordScopes

namespace Aethel.AutomaticLayout

open Core Structured

/-- A multi-path view bundles non-conflicting field reservations (e.g., `~>.{pos, vel}`)
without over-approximating to their common ancestor record. -/
structure MultiPathView where
  mode : AccessMode
  entries : List RecordView

def MultiPathView.paths (mv : MultiPathView) : List (List Nat) :=
  mv.entries.map RecordView.path

def MultiPathView.allByteOffsets (mv : MultiPathView) : List Nat :=
  mv.entries.flatMap RecordView.byteOffsets

private def openMultiViewEntries {abi : TargetIntegerABI} {schema : Schema}
    (record : RecordRef abi schema) (state : State) :
    List (List Nat) → AccessMode → Option (List RecordView × State)
  | [], _ => some ([], state)
  | p :: rest, mode => do
    let (rv, st1) ← openView record state p mode
    let (rvs, st2) ← openMultiViewEntries record st1 rest mode
    return (rv :: rvs, st2)

def openMultiView {abi : TargetIntegerABI} {schema : Schema}
    (record : RecordRef abi schema) (state : State)
    (paths : List (List Nat)) (mode : AccessMode) : Option (MultiPathView × State) := do
  let (entries, opened) ← openMultiViewEntries record state paths mode
  return (⟨mode, entries⟩, opened)

private def closeMultiViewEntries (state : State) : List RecordView → Option State
  | [] => some state
  | rv :: rest => do
    let st1 ← closeMultiViewEntries state rest
    closeView rv st1

def closeMultiView (mv : MultiPathView) (state : State) : Option State :=
  closeMultiViewEntries state mv.entries

private def findEntryTargets {abi : TargetIntegerABI} {schema : Schema}
    (record : RecordRef abi schema) (path : List Nat) (mode : AccessMode) :
    List RecordView → Option (List AccessTarget)
  | [] => none
  | rv :: rest =>
    match rv.targets record path mode with
    | some ts => some ts
    | none => findEntryTargets record path mode rest

def MultiPathView.targets {abi : TargetIntegerABI} {schema : Schema}
    (mv : MultiPathView) (record : RecordRef abi schema)
    (path : List Nat) (mode : AccessMode) : Option (List AccessTarget) :=
  findEntryTargets record path mode mv.entries

def pathsByteDisjoint (layout : Layout) (p1 p2 : List Nat) : Bool :=
  match inferView layout p1, inferView layout p2 with
  | some (o1, w1), some (o2, w2) =>
    decide (w1 = 0 ∨ w2 = 0 ∨ o1 + w1 ≤ o2 ∨ o2 + w2 ≤ o1)
  | _, _ => false

private theorem runs_append {s1 s2 s3 : State} {p1 p2 : Program}
    (h1 : Runs s1 p1 s2) (h2 : Runs s2 p2 s3) : Runs s1 (p1 ++ p2) s3 := by
  induction h1 with
  | nil => exact h2
  | cons first _ ih => exact .cons first (ih h2)

private theorem openMultiViewEntries_preserves_borrow_invariant
    {abi : TargetIntegerABI} {schema : Schema} {record : RecordRef abi schema}
    {paths : List (List Nat)} {mode : AccessMode} {state opened : State}
    {entries : List RecordView}
    (hOpen : openMultiViewEntries record state paths mode = some (entries, opened))
    (hCompat : state.ViewsCompatible) :
    opened.ViewsCompatible := by
  induction paths generalizing state entries with
  | nil =>
    cases hOpen
    exact hCompat
  | cons p rest ih =>
    simp only [openMultiViewEntries, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.exists, Prod.mk.injEq] at hOpen
    obtain ⟨rv, st1, hOne, rvs, st2, hRest, rfl, rfl⟩ := hOpen
    exact ih hRest (openView_preserves_borrow_invariant hOne hCompat)

theorem openMultiView_preserves_borrow_invariant
    {abi : TargetIntegerABI} {schema : Schema} {record : RecordRef abi schema}
    {paths : List (List Nat)} {mode : AccessMode} {state opened : State}
    {mv : MultiPathView}
    (hOpen : openMultiView record state paths mode = some (mv, opened))
    (hCompat : state.ViewsCompatible) :
    opened.ViewsCompatible := by
  simp only [openMultiView, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.exists, Prod.mk.injEq] at hOpen
  obtain ⟨entries, st, hEntries, rfl, rfl⟩ := hOpen
  exact openMultiViewEntries_preserves_borrow_invariant hEntries hCompat

private theorem openMultiViewEntries_paths
    {abi : TargetIntegerABI} {schema : Schema} {record : RecordRef abi schema}
    {paths : List (List Nat)} {mode : AccessMode} {state opened : State}
    {entries : List RecordView}
    (hOpen : openMultiViewEntries record state paths mode = some (entries, opened)) :
    entries.map RecordView.path = paths := by
  induction paths generalizing state entries with
  | nil =>
    cases hOpen
    rfl
  | cons p rest ih =>
    simp only [openMultiViewEntries, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.exists, Prod.mk.injEq] at hOpen
    obtain ⟨rv, st1, hOne, rvs, st2, hRest, rfl, rfl⟩ := hOpen
    have hp : rv.path = p := (openView_sound hOne).1
    simp [hp, ih hRest]

theorem openMultiView_paths
    {abi : TargetIntegerABI} {schema : Schema} {record : RecordRef abi schema}
    {paths : List (List Nat)} {mode : AccessMode} {state opened : State}
    {mv : MultiPathView}
    (hOpen : openMultiView record state paths mode = some (mv, opened)) :
    mv.paths = paths := by
  simp only [openMultiView, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.exists, Prod.mk.injEq] at hOpen
  obtain ⟨entries, st, hEntries, rfl, rfl⟩ := hOpen
  exact openMultiViewEntries_paths hEntries

private theorem openMultiViewEntries_runs
    {abi : TargetIntegerABI} {schema : Schema} {record : RecordRef abi schema}
    {paths : List (List Nat)} {mode : AccessMode} {state opened : State}
    {entries : List RecordView}
    (hOpen : openMultiViewEntries record state paths mode = some (entries, opened)) :
    ∃ prog, Runs state prog opened := by
  induction paths generalizing state entries with
  | nil =>
    cases hOpen
    exact ⟨[], .nil⟩
  | cons p rest ih =>
    simp only [openMultiViewEntries, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.exists, Prod.mk.injEq] at hOpen
    obtain ⟨rv, st1, hOne, rvs, st2, hRest, rfl, rfl⟩ := hOpen
    obtain ⟨pRest, hRunRest⟩ := ih hRest
    exact ⟨_, runs_append (openView_sound hOne).2.2.2.1 hRunRest⟩

theorem openMultiView_runs
    {abi : TargetIntegerABI} {schema : Schema} {record : RecordRef abi schema}
    {paths : List (List Nat)} {mode : AccessMode} {state opened : State}
    {mv : MultiPathView}
    (hOpen : openMultiView record state paths mode = some (mv, opened)) :
    ∃ prog, Runs state prog opened := by
  simp only [openMultiView, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.exists, Prod.mk.injEq] at hOpen
  obtain ⟨entries, st, hEntries, rfl, rfl⟩ := hOpen
  exact openMultiViewEntries_runs hEntries

private theorem closeMultiViewEntries_runs
    {entries : List RecordView} {state closed : State}
    (hClose : closeMultiViewEntries state entries = some closed) :
    ∃ prog, Runs state prog closed := by
  induction entries generalizing state closed with
  | nil =>
    cases hClose
    exact ⟨[], .nil⟩
  | cons rv rest ih =>
    simp only [closeMultiViewEntries, bind, Option.bind_eq_some_iff] at hClose
    obtain ⟨st1, hRest, hOne⟩ := hClose
    obtain ⟨pRest, hRunRest⟩ := ih hRest
    exact ⟨_, runs_append hRunRest (closeView_sound hOne)⟩

theorem closeMultiView_runs {mv : MultiPathView} {state closed : State}
    (hClose : closeMultiView mv state = some closed) :
    ∃ prog, Runs state prog closed :=
  closeMultiViewEntries_runs hClose

private theorem findEntryTargets_covered
    {abi : TargetIntegerABI} {schema : Schema} {record : RecordRef abi schema}
    {path : List Nat} {mode : AccessMode} {entries : List RecordView}
    {ts : List AccessTarget}
    (hFound : findEntryTargets record path mode entries = some ts) :
    ∃ rv ∈ entries, rv.targets record path mode = some ts ∧ rv.path <+: path ∧ rv.mode.Allows mode := by
  induction entries with
  | nil => simp [findEntryTargets] at hFound
  | cons rv rest ih =>
    simp only [findEntryTargets] at hFound
    cases hRv : rv.targets record path mode with
    | some ts' =>
      rw [hRv] at hFound
      cases hFound
      have hScope := RecordView.targets_scope hRv
      exact ⟨rv, List.mem_cons_self, hRv, hScope.1, hScope.2⟩
    | none =>
      rw [hRv] at hFound
      obtain ⟨rv', hMem, hTgt, hPfx, hAllow⟩ := ih hFound
      exact ⟨rv', List.mem_cons_of_mem _ hMem, hTgt, hPfx, hAllow⟩

theorem MultiPathView.targets_covered
    {abi : TargetIntegerABI} {schema : Schema} {mv : MultiPathView}
    {record : RecordRef abi schema} {path : List Nat} {mode : AccessMode}
    {ts : List AccessTarget}
    (hFound : mv.targets record path mode = some ts) :
    ∃ rv ∈ mv.entries, rv.targets record path mode = some ts ∧ rv.path <+: path ∧ rv.mode.Allows mode :=
  findEntryTargets_covered hFound

theorem pathsByteDisjoint_sound {layout : Layout} {p1 p2 : List Nat}
    {o1 w1 o2 w2 : Nat}
    (hDisj : pathsByteDisjoint layout p1 p2 = true)
    (h1 : inferView layout p1 = some (o1, w1))
    (h2 : inferView layout p2 = some (o2, w2)) :
    ∀ off, ¬ (o1 ≤ off ∧ off < o1 + w1 ∧ o2 ≤ off ∧ off < o2 + w2) := by
  simp only [pathsByteDisjoint, h1, h2, decide_eq_true_eq] at hDisj
  intro off ⟨h1Lo, h1Hi, h2Lo, h2Hi⟩
  omega

private theorem openMultiViewEntries_views_subset
    {abi : TargetIntegerABI} {schema : Schema} {record : RecordRef abi schema}
    {paths : List (List Nat)} {mode : AccessMode} {state opened : State}
    {entries : List RecordView}
    (hOpen : openMultiViewEntries record state paths mode = some (entries, opened)) :
    ∀ v ∈ opened.views, v ∈ state.views ∨
      ∃ p ∈ paths, ∃ o w, inferView record.layout p = some (o, w) ∧
        v.location.allocation = record.owner ∧ o ≤ v.location.offset ∧ v.location.offset < o + w := by
  induction paths generalizing state entries with
  | nil =>
    cases hOpen
    intro v hv
    exact Or.inl hv
  | cons p rest ih =>
    simp only [openMultiViewEntries, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.exists, Prod.mk.injEq] at hOpen
    obtain ⟨rv, st1, hOne, rvs, st2, hRest, rfl, rfl⟩ := hOpen
    intro v hv
    rcases ih hRest v hv with hInSt1 | ⟨p', hpMem, o', w', hInf', hOwn', hLo', hHi'⟩
    · rcases openView_views_subset hOne v hInSt1 with hInState | ⟨hOwn, hOffMem⟩
      · exact Or.inl hInState
      · obtain ⟨_, _, hInf, _, _⟩ := openView_sound hOne
        obtain ⟨i, hiRange, hiEq⟩ := List.mem_map.mp hOffMem
        rw [List.mem_range] at hiRange
        exact Or.inr ⟨p, List.mem_cons_self, rv.offset, rv.width, hInf, hOwn,
          by omega, by omega⟩
    · exact Or.inr ⟨p', List.mem_cons_of_mem _ hpMem, o', w', hInf', hOwn', hLo', hHi'⟩

theorem openMultiView_disjoint_sibling_available
    {abi : TargetIntegerABI} {schema : Schema} {record : RecordRef abi schema}
    {state opened : State} {paths : List (List Nat)} {mode : AccessMode}
    {mv : MultiPathView} {siblingPath : List Nat} {sibOff sibWidth : Nat}
    (hSib : inferView record.layout siblingPath = some (sibOff, sibWidth))
    (hDisj : ∀ p ∈ paths, pathsByteDisjoint record.layout p siblingPath = true)
    (hStateAvail : ∀ off, sibOff ≤ off → off < sibOff + sibWidth →
      state.Available ⟨record.owner, off⟩ .exclusive none)
    (hOpen : openMultiView record state paths mode = some (mv, opened)) :
    ∀ off, sibOff ≤ off → off < sibOff + sibWidth →
      opened.Available ⟨record.owner, off⟩ .exclusive none := by
  simp only [openMultiView, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.exists, Prod.mk.injEq] at hOpen
  obtain ⟨entries, st, hEntries, rfl, rfl⟩ := hOpen
  intro off hLo hHi v hv
  rcases openMultiViewEntries_views_subset hEntries v hv with hOld | ⟨p, hpMem, o, w, hInf, hOwn, hVLo, hVHi⟩
  · exact hStateAvail off hLo hHi v hOld
  · right; left
    intro hLocEq
    have hOffEq : off = v.location.offset := congrArg ByteLocation.offset hLocEq
    rw [← hOffEq] at hVLo hVHi
    exact pathsByteDisjoint_sound (hDisj p hpMem) hInf hSib off ⟨hVLo, hVHi, hLo, hHi⟩

end Aethel.AutomaticLayout
