import Aethel.CorePermissions

namespace Aethel.Core

/-- Live allocation keys are unique and every key is permanently recorded. -/
def State.OwnersValid (s : State) : Prop :=
  (s.allocations.map Allocation.owner).Nodup ∧
    ∀ owner ∈ s.allocations.map Allocation.owner, owner ∈ s.issued

theorem State.empty_owners_valid : ({} : State).OwnersValid := by
  simp [State.OwnersValid]

theorem Step.owners_valid {s next : State} {instruction : Instruction}
    (h : Step s instruction next) (hs : s.OwnersValid) : next.OwnersValid := by
  cases h <;> try exact hs
  case write =>
    simpa [State.OwnersValid, State.store, List.map_map, Function.comp_def] using hs
  case writeView =>
    simpa [State.OwnersValid, State.store, List.map_map, Function.comp_def] using hs
  case alloc owner bytes fresh =>
    simp only [State.OwnersValid, State.addAllocation, List.map_cons, List.nodup_cons,
      List.mem_cons]
    grind [State.OwnersValid]
  case destroy allocation owner found unreserved =>
    simp only [State.OwnersValid, State.removeOwner]
    have hfilter := List.filter_map (f := Allocation.owner)
      (p := fun key => key != owner) (l := s.allocations)
    simp only [Function.comp_def] at hfilter
    rw [← hfilter]
    exact ⟨List.Pairwise.filter _ hs.1, fun key hk => hs.2 key (List.mem_filter.mp hk).1⟩

theorem Runs.owners_valid {s final : State} {program : Program}
    (h : Runs s program final) (valid : s.OwnersValid) : final.OwnersValid := by
  induction h with
  | nil => exact valid
  | cons first _ ih => exact ih (first.owners_valid valid)

theorem run_owners_valid {program : Program} {final : State}
    (h : run {} program = some final) : final.OwnersValid :=
  (run_sound h).owners_valid State.empty_owners_valid

end Aethel.Core
