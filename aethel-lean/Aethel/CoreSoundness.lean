import Aethel.Execution

namespace Aethel.Core

theorem execute_sound {s next : State} {instruction : Instruction}
    (h : execute s instruction = some next) : Step s instruction next := by
  cases instruction <;> simp only [execute, bind, Option.bind_eq_some_iff,
    Option.ite_none_left_eq_some, Option.ite_none_right_eq_some,
    Option.some.injEq, Bool.not_eq_true, Option.isSome_eq_false_iff] at h
  case alloc =>
    rcases h with ⟨fresh, rfl⟩
    exact .alloc fresh
  case alias =>
    rcases h with ⟨fresh, byte, live, rfl⟩
    exact .alias (Option.isNone_iff_eq_none.mp fresh) live
  case read =>
    rcases h with ⟨handle, found, value, live, available, rfl⟩
    exact .read found live available
  case write =>
    rcases h with ⟨handle, found, old, live, ⟨authority, available⟩, rfl⟩
    exact .write found live authority available
  case reserve =>
    rcases h with ⟨fresh, handle, found, byte, live, ⟨authority, available⟩, rfl⟩
    exact .reserve (Option.isNone_iff_eq_none.mp fresh) found live authority available
  case readView =>
    rcases h with ⟨view, found, value, live, available, rfl⟩
    exact .readView found live available
  case writeView =>
    rcases h with ⟨view, found, old, live, ⟨authority, available⟩, rfl⟩
    exact .writeView found live authority available
  case release =>
    rcases h with ⟨view, found, rfl⟩
    exact .release found
  case forget =>
    rcases h with ⟨handle, found, rfl⟩
    exact .forget found
  case destroy =>
    rcases h with ⟨allocation, found, unreserved, rfl⟩
    exact .destroy found unreserved

theorem execute_complete {s next : State} {instruction : Instruction}
    (h : Step s instruction next) : execute s instruction = some next := by
  cases h <;> simp_all [execute, bind]

theorem execute_correct (s next : State) (instruction : Instruction) :
    execute s instruction = some next ↔ Step s instruction next :=
  ⟨execute_sound, execute_complete⟩

theorem Step.deterministic {s a b : State} {instruction : Instruction}
    (ha : Step s instruction a) (hb : Step s instruction b) : a = b := by
  exact Option.some.inj ((execute_complete ha).symm.trans (execute_complete hb))

theorem run_sound {s final : State} {program : Program}
    (h : run s program = some final) : Runs s program final := by
  induction program generalizing s with
  | nil =>
    simp only [run, Option.some.injEq] at h
    exact h ▸ Runs.nil
  | cons instruction rest ih =>
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨middle, first, remaining⟩ := h
    exact .cons (execute_sound first) (ih remaining)

theorem run_complete {s final : State} {program : Program}
    (h : Runs s program final) : run s program = some final := by
  induction h with
  | nil => rfl
  | cons first rest ih =>
    rw [run, execute_complete first]
    exact ih

theorem run_correct (s final : State) (program : Program) :
    run s program = some final ↔ Runs s program final := ⟨run_sound, run_complete⟩

theorem checkClosed_sound {program : Program} {final : State}
    (h : checkClosed program = some final) : Runs {} program final ∧ final.views = [] := by
  simp only [checkClosed, bind, Option.bind_eq_some_iff,
    Option.ite_none_right_eq_some, Option.some.injEq, List.isEmpty_iff] at h
  obtain ⟨_, traced, closed, rfl⟩ := h
  exact ⟨run_sound traced, closed⟩

theorem Step.issued_mono {s next : State} {instruction : Instruction}
    (h : Step s instruction next) {owner : OwnerId} (ho : owner ∈ s.issued) :
    owner ∈ next.issued := by
  cases h <;> simp_all [State.addAllocation, State.addHandle, State.observe,
    State.store, State.addView, State.removeView, State.removeHandle, State.removeOwner]

theorem Runs.issued_mono {s final : State} {program : Program}
    (h : Runs s program final) {owner : OwnerId} (ho : owner ∈ s.issued) :
    owner ∈ final.issued := by
  induction h with
  | nil => exact ho
  | cons first rest ih =>
    exact ih (first.issued_mono ho)

theorem issued_owner_cannot_reallocate {s : State} {owner : OwnerId}
    (h : owner ∈ s.issued) (bytes : List UInt8) : execute s (.alloc owner bytes) = none := by
  simp [execute, h]

theorem State.removeOwner_allocation (s : State) (owner : OwnerId) :
    (s.removeOwner owner).allocation owner = none := by
  simp [State.removeOwner, State.allocation, List.find?_eq_none]

theorem State.removeOwner_invalidates {s : State} {owner : OwnerId}
    {handle : HandleId} {h : Handle}
    (found : (s.removeOwner owner).handle handle = some h) :
    h.location.allocation ≠ owner := by
  simp only [State.handle, State.removeOwner, Option.map_eq_some_iff] at found
  obtain ⟨entry, found, rfl⟩ := found
  have member := List.mem_of_find?_eq_some found
  exact of_decide_eq_true ((List.mem_filter.mp member).2)

theorem State.store_owners (s : State) (p : ByteLocation) (value : UInt8) :
    (s.store p value).allocations.map Allocation.owner = s.allocations.map Allocation.owner := by
  simp [State.store, List.map_map]

theorem run_append (s : State) (first rest : Program) :
    run s (first ++ rest) = (run s first).bind (fun middle => run middle rest) := by
  induction first generalizing s with
  | nil => rfl
  | cons instruction first ih =>
    simp [run, ih, Option.bind_assoc]

end Aethel.Core
