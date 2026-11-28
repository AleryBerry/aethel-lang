import Aethel.Permissions

namespace Aethel

/-- Initial byte-aligned record fragment. Bit layouts require separate accessors. -/
structure FieldPlacement where
  offset : Nat
  size : Nat
  alignment : Nat
  deriving Repr, DecidableEq

structure RecordLayout where
  size : Nat
  alignment : Nat
  fields : List FieldPlacement
  deriving Repr

def FieldPlacement.Valid (total : Nat) (f : FieldPlacement) : Prop :=
  0 < f.size ∧ 0 < f.alignment ∧
  f.offset % f.alignment = 0 ∧ f.offset + f.size ≤ total

def FieldPlacement.Separate (a b : FieldPlacement) : Prop :=
  a.offset + a.size ≤ b.offset ∨ b.offset + b.size ≤ a.offset

instance (total : Nat) (f : FieldPlacement) : Decidable (f.Valid total) :=
  inferInstanceAs (Decidable (0 < f.size ∧ 0 < f.alignment ∧
    f.offset % f.alignment = 0 ∧ f.offset + f.size ≤ total))

instance (a b : FieldPlacement) : Decidable (a.Separate b) :=
  inferInstanceAs (Decidable
    (a.offset + a.size ≤ b.offset ∨ b.offset + b.size ≤ a.offset))

/-- Alignment divisibility also guarantees alignment of fields in subsequent records. -/
def RecordLayout.Valid (r : RecordLayout) : Prop :=
  0 < r.alignment ∧ r.size % r.alignment = 0 ∧
  (∀ f ∈ r.fields, f.Valid r.size ∧ r.alignment % f.alignment = 0) ∧
  r.fields.Pairwise FieldPlacement.Separate

instance (r : RecordLayout) : Decidable r.Valid :=
  inferInstanceAs (Decidable (0 < r.alignment ∧ r.size % r.alignment = 0 ∧
    (∀ f ∈ r.fields, f.Valid r.size ∧ r.alignment % f.alignment = 0) ∧
    r.fields.Pairwise FieldPlacement.Separate))

def RecordLayout.check (r : RecordLayout) : Bool := decide r.Valid

theorem RecordLayout.check_correct (r : RecordLayout) : r.check = true ↔ r.Valid := by
  simp [check]

/-- Access validation includes the actual address, not just a layout descriptor. -/
def checkAccess (capacity base offset width alignment addressLimit : Nat) : Bool :=
  decide (0 < width ∧ 0 < alignment ∧ offset + width ≤ capacity ∧
    base + capacity ≤ addressLimit ∧ (base + offset) % alignment = 0)

theorem checkAccess_sound {capacity base offset width alignment addressLimit : Nat}
    (h : checkAccess capacity base offset width alignment addressLimit = true) :
    0 < width ∧ 0 < alignment ∧ offset + width ≤ capacity ∧
      base + capacity ≤ addressLimit ∧ (base + offset) % alignment = 0 := by
  simpa only [checkAccess, decide_eq_true_eq] using h

def padding (offset alignment : Nat) : Nat :=
  (alignment - offset % alignment) % alignment

def alignUp (offset alignment : Nat) : Nat := offset + padding offset alignment

/-- Concatenating two bounded codes, with the low code first, fits their combined width. -/
theorem concatCode_fits {low high lowWidth highWidth : Nat}
    (lowFits : low < 2 ^ lowWidth) (highFits : high < 2 ^ highWidth) :
    low + high * 2 ^ lowWidth < 2 ^ (lowWidth + highWidth) := by
  have bound := Nat.mul_le_mul_right (2 ^ lowWidth) (Nat.succ_le_of_lt highFits)
  rw [Nat.succ_mul] at bound
  rw [Nat.pow_add, Nat.mul_comm (2 ^ lowWidth)]
  omega

theorem concatCode_split {low high lowWidth : Nat} (lowFits : low < 2 ^ lowWidth) :
    (low + high * 2 ^ lowWidth) % 2 ^ lowWidth = low ∧
      (low + high * 2 ^ lowWidth) / 2 ^ lowWidth = high := by
  constructor
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt lowFits]
  · rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt lowFits, Nat.zero_add]

theorem padding_lt (offset : Nat) {alignment : Nat} (h : 0 < alignment) :
    padding offset alignment < alignment := by
  exact Nat.mod_lt _ h

theorem alignUp_aligned (offset : Nat) {alignment : Nat} (h : 0 < alignment) :
    alignUp offset alignment % alignment = 0 := by
  unfold alignUp padding
  rw [Nat.add_mod, Nat.mod_mod]
  by_cases hz : offset % alignment = 0
  · simp [hz]
  · have hm := Nat.mod_lt offset h
    have hs : alignment - offset % alignment < alignment := by omega
    rw [Nat.mod_eq_of_lt hs, Nat.add_sub_of_le (Nat.le_of_lt hm), Nat.mod_self]

/-- Minimal padding for one offset; this is not global record-layout optimality. -/
theorem padding_minimal (offset p : Nat) {alignment : Nat} (h : 0 < alignment)
    (hp : (offset + p) % alignment = 0) : padding offset alignment ≤ p := by
  by_cases hz : offset % alignment = 0
  · simp [padding, hz]
  · have hm := Nat.mod_lt offset h
    have hs : alignment - offset % alignment < alignment := by omega
    simp only [padding, Nat.mod_eq_of_lt hs]
    apply Classical.byContradiction
    intro hn
    have hsum : offset % alignment + p < alignment := by omega
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : p < alignment),
      Nat.mod_eq_of_lt hsum] at hp
    omega

end Aethel
