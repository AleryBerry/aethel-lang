import Aethel.LayoutAlgebra

namespace Aethel

/-- A descriptor for a contiguous range of initialized scalar slots. Validity
here is spatial. The caller supplies allocation provenance and initialization
when relating this descriptor to a concrete allocation. -/
structure ScalarRange where
  base : Nat
  capacity : Nat
  offset : Nat
  count : Nat
  width : Nat
  alignment : Nat
  deriving Repr, DecidableEq

def ScalarRange.Valid (r : ScalarRange) (addressLimit sliceLimit : Nat) : Prop :=
  0 < r.width ∧ 0 < r.alignment ∧ r.width % r.alignment = 0 ∧
    r.offset + r.width * r.count ≤ r.capacity ∧
    r.base + r.capacity ≤ addressLimit ∧
    (r.base + r.offset) % r.alignment = 0 ∧ r.width * r.count ≤ sliceLimit

instance (r : ScalarRange) (addressLimit sliceLimit : Nat) :
    Decidable (r.Valid addressLimit sliceLimit) :=
  inferInstanceAs (Decidable (0 < r.width ∧ 0 < r.alignment ∧ r.width % r.alignment = 0 ∧
    r.offset + r.width * r.count ≤ r.capacity ∧
    r.base + r.capacity ≤ addressLimit ∧
    (r.base + r.offset) % r.alignment = 0 ∧ r.width * r.count ≤ sliceLimit))

def ScalarRange.check (r : ScalarRange) (addressLimit sliceLimit : Nat) : Bool :=
  decide (r.Valid addressLimit sliceLimit)

theorem ScalarRange.check_correct (r : ScalarRange) (addressLimit sliceLimit : Nat) :
    r.check addressLimit sliceLimit = true ↔ r.Valid addressLimit sliceLimit := by
  simp [check]

theorem ScalarRange.element_access {r : ScalarRange} {addressLimit sliceLimit index : Nat}
    (valid : r.Valid addressLimit sliceLimit) (inRange : index < r.count) :
    checkAccess r.capacity r.base (r.offset + r.width * index) r.width
      r.alignment addressLimit = true := by
  obtain ⟨width, align, stride, extent, limit, start, _⟩ := valid
  have within := Nat.mul_le_mul_left r.width (Nat.succ_le_of_lt inRange)
  simp only [Nat.mul_succ] at within
  have aligned : (r.base + (r.offset + r.width * index)) % r.alignment = 0 := by
    rw [← Nat.add_assoc, Nat.add_mod, Nat.mul_mod, stride, Nat.zero_mul, start]
    simp
  exact decide_eq_true ⟨width, align, by omega, limit, aligned⟩

end Aethel
