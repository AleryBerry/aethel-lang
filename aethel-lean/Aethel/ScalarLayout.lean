import Std

namespace Aethel

/-- A deliberately limited AoS/SoA lemma for fixed-size scalar slots. These
functions do not yet model byte allocations, tags, loans, or deallocation. -/
abbrev ScalarTable := Nat → Nat → Nat
abbrev SlotStore := Nat → Nat

def aosSlot (fieldCount element field : Nat) : Nat := element * fieldCount + field
def soaSlot (length element field : Nat) : Nat := field * length + element

def encodeAoS (table : ScalarTable) (fieldCount : Nat) : SlotStore :=
  fun address => table (address / fieldCount) (address % fieldCount)

def encodeSoA (table : ScalarTable) (length : Nat) : SlotStore :=
  fun address => table (address % length) (address / length)

theorem aos_read (table : ScalarTable) (fieldCount element field : Nat)
    (hf : field < fieldCount) :
    encodeAoS table fieldCount (aosSlot fieldCount element field) = table element field := by
  simp [encodeAoS, aosSlot, Nat.mul_comm element fieldCount,
    Nat.mul_add_div (Nat.zero_lt_of_lt hf), Nat.div_eq_of_lt hf, Nat.mod_eq_of_lt hf]

theorem soa_read (table : ScalarTable) (length element field : Nat)
    (hi : element < length) :
    encodeSoA table length (soaSlot length element field) = table element field := by
  simp [encodeSoA, soaSlot, Nat.mul_comm field length,
    Nat.mul_add_div (Nat.zero_lt_of_lt hi), Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]

theorem scalar_aos_soa_read_agreement (table : ScalarTable)
    (length fieldCount element field : Nat) (hi : element < length) (hf : field < fieldCount) :
    encodeAoS table fieldCount (aosSlot fieldCount element field) =
      encodeSoA table length (soaSlot length element field) := by
  rw [aos_read table fieldCount element field hf, soa_read table length element field hi]

theorem aosSlot_eq_iff (fieldCount i j f g : Nat) (hf : f < fieldCount) (hg : g < fieldCount) :
    aosSlot fieldCount i f = aosSlot fieldCount j g ↔ i = j ∧ f = g := by
  constructor
  · intro h
    have hi := congrArg (encodeAoS (fun row _ => row) fieldCount) h
    have hfield := congrArg (encodeAoS (fun _ column => column) fieldCount) h
    simp only [aos_read _ _ _ _ hf, aos_read _ _ _ _ hg] at hi hfield
    exact ⟨hi, hfield⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem soaSlot_eq_iff (length i j f g : Nat) (hi : i < length) (hj : j < length) :
    soaSlot length i f = soaSlot length j g ↔ i = j ∧ f = g := by
  constructor
  · intro h
    have hrow := congrArg (encodeSoA (fun row _ => row) length) h
    have hfield := congrArg (encodeSoA (fun _ column => column) length) h
    simp only [soa_read _ _ _ _ hi, soa_read _ _ _ _ hj] at hrow hfield
    exact ⟨hrow, hfield⟩
  · rintro ⟨rfl, rfl⟩; rfl

def writeSlot (store : SlotStore) (address value : Nat) : SlotStore :=
  fun location => if location = address then value else store location

def writeTable (table : ScalarTable) (element field value : Nat) : ScalarTable :=
  fun i f => if i = element ∧ f = field then value else table i f

theorem aos_write_observation (table : ScalarTable) (fieldCount i j f g value : Nat)
    (hf : f < fieldCount) (hg : g < fieldCount) :
    writeSlot (encodeAoS table fieldCount) (aosSlot fieldCount i f) value
      (aosSlot fieldCount j g) = writeTable table i f value j g := by
  simp [writeSlot, writeTable, aosSlot_eq_iff _ _ _ _ _ hg hf, aos_read _ _ _ _ hg]

theorem soa_write_observation (table : ScalarTable) (length i j f g value : Nat)
    (hi : i < length) (hj : j < length) :
    writeSlot (encodeSoA table length) (soaSlot length i f) value
      (soaSlot length j g) = writeTable table i f value j g := by
  simp [writeSlot, writeTable, soaSlot_eq_iff _ _ _ _ _ hj hi, soa_read _ _ _ _ hj]

def ScalarRepAoS (table : ScalarTable) (store : SlotStore) (length fieldCount : Nat) : Prop :=
  ∀ i, i < length → ∀ f, f < fieldCount → store (aosSlot fieldCount i f) = table i f

def ScalarRepSoA (table : ScalarTable) (store : SlotStore) (length fieldCount : Nat) : Prop :=
  ∀ i, i < length → ∀ f, f < fieldCount → store (soaSlot length i f) = table i f

theorem scalarRepAoS_init (table : ScalarTable) (length fieldCount : Nat) :
    ScalarRepAoS table (encodeAoS table fieldCount) length fieldCount := by
  exact fun _ _ _ hf => aos_read table _ _ _ hf

theorem scalarRepSoA_init (table : ScalarTable) (length fieldCount : Nat) :
    ScalarRepSoA table (encodeSoA table length) length fieldCount := by
  exact fun _ hi _ _ => soa_read table _ _ _ hi

theorem scalarRepAoS_write {table : ScalarTable} {store : SlotStore}
    {length fieldCount : Nat} (hrep : ScalarRepAoS table store length fieldCount)
    (i f value : Nat) (_hi : i < length) (hf : f < fieldCount) :
    ScalarRepAoS (writeTable table i f value)
      (writeSlot store (aosSlot fieldCount i f) value) length fieldCount := by
  intro j hj g hg
  simp [writeSlot, writeTable, aosSlot_eq_iff _ _ _ _ _ hg hf, hrep j hj g hg]

theorem scalarRepSoA_write {table : ScalarTable} {store : SlotStore}
    {length fieldCount : Nat} (hrep : ScalarRepSoA table store length fieldCount)
    (i f value : Nat) (hi : i < length) (_hf : f < fieldCount) :
    ScalarRepSoA (writeTable table i f value)
      (writeSlot store (soaSlot length i f) value) length fieldCount := by
  intro j hj g hg
  simp [writeSlot, writeTable, soaSlot_eq_iff _ _ _ _ _ hj hi, hrep j hj g hg]

/-- Corresponding scalar-slot updates preserve both representations of the
same logical table. Full byte/allocator/provenance refinement is a later gate. -/
theorem scalar_aos_soa_write_refinement {table : ScalarTable} {aos soa : SlotStore}
    {length fieldCount : Nat}
    (ha : ScalarRepAoS table aos length fieldCount)
    (hs : ScalarRepSoA table soa length fieldCount)
    (i f value : Nat) (hi : i < length) (hf : f < fieldCount) :
    ScalarRepAoS (writeTable table i f value)
      (writeSlot aos (aosSlot fieldCount i f) value) length fieldCount ∧
    ScalarRepSoA (writeTable table i f value)
      (writeSlot soa (soaSlot length i f) value) length fieldCount := by
  exact ⟨scalarRepAoS_write ha i f value hi hf, scalarRepSoA_write hs i f value hi hf⟩

end Aethel
