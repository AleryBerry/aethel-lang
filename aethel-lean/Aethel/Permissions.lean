import Std

namespace Aethel

/-- Allocation identity plus byte offset: addresses in separate allocations differ. -/
structure ByteLocation where
  allocation : Nat
  offset : Nat
  deriving Repr, DecidableEq

structure Footprint where
  reads : List ByteLocation := []
  writes : List ByteLocation := []
  deriving Repr

def Footprint.Compatible (a b : Footprint) : Prop :=
  (∀ p, p ∈ a.writes → p ∉ b.reads ∧ p ∉ b.writes) ∧
  (∀ p, p ∈ b.writes → p ∉ a.reads ∧ p ∉ a.writes)

instance (a b : Footprint) : Decidable (a.Compatible b) :=
  inferInstanceAs (Decidable
    ((∀ p ∈ a.writes, p ∉ b.reads ∧ p ∉ b.writes) ∧
     (∀ p ∈ b.writes, p ∉ a.reads ∧ p ∉ a.writes)))

def Footprint.compatible (a b : Footprint) : Bool := decide (a.Compatible b)

theorem Footprint.compatible_correct (a b : Footprint) :
    a.compatible b = true ↔ a.Compatible b := by
  simp [compatible]

theorem Footprint.compatible_symm {a b : Footprint} (h : a.Compatible b) :
    b.Compatible a := by
  exact ⟨h.2, h.1⟩

/-- A masked setter reads and writes the containing byte, regardless of bit mask. -/
def packedSetterFootprint (p : ByteLocation) : Footprint := ⟨[p], [p]⟩

theorem packed_setters_conflict (p : ByteLocation) :
    ¬ (packedSetterFootprint p).Compatible (packedSetterFootprint p) := by
  simp [Footprint.Compatible, packedSetterFootprint]

theorem shared_readers_compatible (a b : List ByteLocation) :
    (Footprint.mk a []).Compatible (Footprint.mk b []) := by
  simp [Footprint.Compatible]

end Aethel
