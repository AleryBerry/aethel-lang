import Aethel.CoreSoundness

namespace Aethel.Core

def accessFootprint (p : ByteLocation) : AccessMode → Footprint
  | .shared => ⟨[p], []⟩
  | .exclusive => ⟨[p], [p]⟩

theorem accessFootprint_compatible (p q : ByteLocation) (a b : AccessMode) :
    (accessFootprint p a).Compatible (accessFootprint q b) ↔
      p ≠ q ∨ a.Compatible b := by
  cases a <;> cases b <;>
    simp [accessFootprint, Footprint.Compatible, AccessMode.Compatible, ne_comm]

theorem available_footprints {s : State} {p : ByteLocation} {mode : AccessMode}
    (h : s.Available p mode none) {v : View} (hv : v ∈ s.views) :
    (accessFootprint p mode).Compatible (accessFootprint v.location v.mode) := by
  apply (accessFootprint_compatible _ _ _ _).mpr
  simpa using h v hv

/-- Active reservations have unique IDs and compatible physical footprints. -/
def State.ViewsCompatible (s : State) : Prop :=
  s.views.Pairwise fun a b => a.id ≠ b.id ∧
    (accessFootprint a.location a.mode).Compatible (accessFootprint b.location b.mode)

theorem State.empty_views_compatible : ({} : State).ViewsCompatible := by
  simp [State.ViewsCompatible]

theorem Step.views_compatible {s next : State} {instruction : Instruction}
    (h : Step s instruction next) (hs : s.ViewsCompatible) : next.ViewsCompatible := by
  cases h <;> try exact hs
  case reserve h byte handle mode id authority fresh found live available =>
    apply List.Pairwise.cons _ hs
    intro v hv
    have distinct := (List.find?_eq_none.mp fresh) v hv
    exact ⟨by simpa [ne_comm] using distinct, available_footprints available hv⟩
  case release =>
    exact List.Pairwise.filter _ hs

theorem Runs.views_compatible {s final : State} {program : Program}
    (h : Runs s program final) (hs : s.ViewsCompatible) : final.ViewsCompatible := by
  induction h with
  | nil => exact hs
  | cons first rest ih => exact ih (first.views_compatible hs)

theorem run_views_compatible {program : Program} {final : State}
    (h : run {} program = some final) : final.ViewsCompatible := by
  exact (run_sound h).views_compatible State.empty_views_compatible

theorem accepted_prefix_views_compatible {first rest : Program} {final : State}
    (h : run {} (first ++ rest) = some final) :
    ∃ middle, run {} first = some middle ∧ middle.ViewsCompatible ∧
      run middle rest = some final := by
  rw [run_append, Option.bind_eq_some_iff] at h
  obtain ⟨middle, hfirst, hrest⟩ := h
  exact ⟨middle, hfirst, run_views_compatible hfirst, hrest⟩

end Aethel.Core
