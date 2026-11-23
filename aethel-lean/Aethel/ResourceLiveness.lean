import Aethel.ResourceCheck

namespace Aethel.Core

/-- Every handle and view retained in a state addresses a live byte. -/
def State.ReferencesLive (s : State) : Prop :=
  (∀ entry ∈ s.handles, s.resources.live entry.2.location = true) ∧
  (∀ view ∈ s.views, s.resources.live view.location = true)

theorem State.empty_references_live : ({} : State).ReferencesLive := by
  simp [State.ReferencesLive]

private theorem live_addAllocation (s : State) (owner : OwnerId) (bytes : List UInt8)
    (p : ByteLocation) (different : p.allocation ≠ owner) :
    (s.addAllocation owner bytes).resources.live p = s.resources.live p := by
  simp [ResourceState.live, ResourceState.extent, State.resources, State.addAllocation,
    Ne.symm different]

private theorem live_removeOwner (s : State) (owner : OwnerId) (p : ByteLocation)
    (different : p.allocation ≠ owner) :
    (s.removeOwner owner).resources.live p = s.resources.live p := by
  simp only [ResourceState.live, State.resources_extent, State.allocation, State.removeOwner,
    List.find?_filter]
  congr 3
  funext a
  by_cases same : a.owner = p.allocation <;> simp [same, different]

private theorem live_owner_issued (s : State) (valid : s.OwnersValid) (p : ByteLocation)
    (live : s.resources.live p = true) : p.allocation ∈ s.issued := by
  simp only [ResourceState.live, State.resources_extent, Option.any_eq_true,
    Option.map_eq_some_iff] at live
  obtain ⟨_, ⟨a, found, rfl⟩, _⟩ := live
  have same := List.find?_some found
  exact valid.2 _ (List.mem_map.mpr ⟨a, List.mem_of_find?_eq_some found, by simpa using same⟩)

private theorem references_store (s : State) (p : ByteLocation) (value : UInt8)
    (live : s.ReferencesLive) : (s.store p value).ReferencesLive :=
  ⟨fun h hh => by rw [State.resources_store]; exact live.1 h hh,
    fun v hv => by rw [State.resources_store]; exact live.2 v hv⟩

theorem Step.references_live {s next : State} {instruction : Instruction}
    (h : Step s instruction next) (owners : s.OwnersValid) (live : s.ReferencesLive) :
    next.ReferencesLive := by
  cases h <;> try exact live
  case write => exact references_store s _ _ live
  case writeView => exact references_store s _ _ live
  case release => exact ⟨live.1, fun v hv => live.2 v (List.mem_filter.mp hv).1⟩
  case forget => exact ⟨fun h hh => live.1 h (List.mem_filter.mp hh).1, live.2⟩
  case alias byte owner offset mode id _ found =>
    exact ⟨fun entry member => (List.mem_cons.mp member).elim
      (fun same => same ▸ (by simp [State.resources_live, found] :
        s.resources.live ⟨owner, offset⟩ = true)) (live.1 entry), live.2⟩
  case reserve h byte handle mode id _ _ _ found _ =>
    exact ⟨live.1, fun view member => (List.mem_cons.mp member).elim
      (fun same => (congrArg View.location same).symm ▸ (by simp [State.resources_live, found] :
        s.resources.live h.location = true)) (live.2 view)⟩
  case alloc owner bytes fresh =>
    exact ⟨fun entry member =>
      let valid := live.1 entry member
      have distinct : entry.2.location.allocation ≠ owner :=
        fun same => fresh (same ▸ live_owner_issued s owners _ valid)
      (live_addAllocation s owner bytes _ distinct).trans valid,
      fun view member =>
        let valid := live.2 view member
        have distinct : view.location.allocation ≠ owner :=
          fun same => fresh (same ▸ live_owner_issued s owners _ valid)
        (live_addAllocation s owner bytes _ distinct).trans valid⟩
  case destroy a owner found unreserved =>
    exact ⟨fun entry member =>
      let keep := List.mem_filter.mp member
      (live_removeOwner s owner _ (by simpa using keep.2)).trans (live.1 entry keep.1),
      fun view member =>
        (live_removeOwner s owner _ (unreserved view member)).trans (live.2 view member)⟩
  all_goals done

theorem Runs.references_live {s final : State} {program : Program}
    (trace : Runs s program final) (owners : s.OwnersValid) (live : s.ReferencesLive) :
    final.ReferencesLive := by
  induction trace with
  | nil => exact live
  | cons first _ ih => exact ih (first.owners_valid owners) (first.references_live owners live)

theorem verified_prefix_safe {first rest : Program}
    (verified : verifyResources (first ++ rest) = true) :
    ∃ middle final, Runs {} first middle ∧ Runs middle rest final ∧ final.views = [] ∧
      middle.OwnersValid ∧ middle.ReferencesLive ∧ middle.ViewsCompatible := by
  obtain ⟨final, traced, closed⟩ := (verifyResources_correct _).mp verified
  have executed := run_complete traced
  rw [run_append, Option.bind_eq_some_iff] at executed
  obtain ⟨middle, initial, remaining⟩ := executed
  have initialTrace := run_sound initial
  exact ⟨middle, final, initialTrace, run_sound remaining, closed,
    initialTrace.owners_valid State.empty_owners_valid,
    initialTrace.references_live State.empty_owners_valid State.empty_references_live,
    initialTrace.views_compatible State.empty_views_compatible⟩

end Aethel.Core
