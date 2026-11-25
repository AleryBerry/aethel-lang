import Aethel.Machine
import Aethel.ResourceCheck
import Aethel.Disjointness
import Aethel.LayoutAlgebra
import Aethel.CacheLayout

namespace Aethel.RustFFI

open Aethel Aethel.Core Aethel.CacheLayout

/-!
## Synchronous Rust C-ABI Adapter Boundary (Phase 6B Lean Gate)

Establishes the safety contract for synchronous Rust FFI slices (`&[T]` / `&mut [T]`)
and opaque affine Rust-owned handles (`RustOwn`), matching `std::slice::from_raw_parts(_mut)`
and preventing unaligned/packed pointers, `isize::MAX` overflows, overlapping mutable
aliases, leaked call reservations, or double-drop / use-after-drop.
-/

def isizeMax64 : Nat := 2 ^ 63 - 1

structure RustSliceSpec where
  owner : OwnerId
  byteOffset : Nat
  len : Nat
  elemSize : Nat
  elemAlign : Nat
  mode : AccessMode
  isSubBytePacked : Bool := false
  deriving Repr, DecidableEq

def RustSliceSpec.byteLen (sl : RustSliceSpec) : Nat :=
  sl.len * sl.elemSize

def RustSliceSpec.locations (sl : RustSliceSpec) : List ByteLocation :=
  (List.range sl.byteLen).map fun i => ⟨sl.owner, sl.byteOffset + i⟩

private def checkRustSliceWhere (s : Core.State) (sl : RustSliceSpec) (permitted : Unit → Bool) : Bool :=
  !sl.isSubBytePacked &&
  decide (0 < sl.elemAlign) &&
  sl.elemAlign.isPowerOfTwo &&
  decide (sl.byteOffset % sl.elemAlign = 0) &&
  decide (sl.elemSize % sl.elemAlign = 0) &&
  decide (sl.byteLen ≤ isizeMax64) &&
  if sl.len = 0 then true
  else
    match s.allocation sl.owner with
    | none => false
    | some alloc =>
      decide (sl.byteOffset + sl.byteLen ≤ alloc.bytes.length) &&
      permitted ()

private def RustSliceContract (s : Core.State) (sl : RustSliceSpec) (permitted : Prop) : Prop :=
  sl.isSubBytePacked = false ∧
  0 < sl.elemAlign ∧
  sl.elemAlign.isPowerOfTwo = true ∧
  sl.byteOffset % sl.elemAlign = 0 ∧
  sl.elemSize % sl.elemAlign = 0 ∧
  sl.byteLen ≤ isizeMax64 ∧
  (sl.len = 0 ∨
    ∃ alloc, s.allocation sl.owner = some alloc ∧
      sl.byteOffset + sl.byteLen ≤ alloc.bytes.length ∧
      permitted)

def checkRustSlice (s : Core.State) (sl : RustSliceSpec) : Bool :=
  checkRustSliceWhere s sl fun _ => sl.locations.all fun loc => decide (s.Available loc sl.mode none)

/-- Independent mathematical Rust C-ABI slice validity contract. -/
def RustSliceValid (s : Core.State) (sl : RustSliceSpec) : Prop :=
  RustSliceContract s sl (∀ loc ∈ sl.locations, s.Available loc sl.mode none)

def checkRustSliceAbi (s : Core.State) (sl : RustSliceSpec) : Bool :=
  checkRustSliceWhere s sl fun _ => true

def RustSliceAbiValid (s : Core.State) (sl : RustSliceSpec) : Prop :=
  RustSliceContract s sl True

private theorem checkRustSliceWhere_correct (s : Core.State) (sl : RustSliceSpec)
    {test : Unit → Bool} {condition : Prop} (check : test () = true ↔ condition) :
    checkRustSliceWhere s sl test = true ↔ RustSliceContract s sl condition := by
  dsimp [checkRustSliceWhere, RustSliceContract]
  cases hLen : sl.len with
  | zero =>
    simp [and_assoc]
  | succ n =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, false_or]
    cases hAlloc : s.allocation sl.owner with
    | none =>
      simp
    | some alloc =>
      simp [and_assoc, check]

theorem checkRustSlice_correct (s : Core.State) (sl : RustSliceSpec) :
    checkRustSlice s sl = true ↔ RustSliceValid s sl :=
  checkRustSliceWhere_correct s sl (by simp [List.all_eq_true])

theorem checkRustSliceAbi_correct (s : Core.State) (sl : RustSliceSpec) :
    checkRustSliceAbi s sl = true ↔ RustSliceAbiValid s sl :=
  checkRustSliceWhere_correct s sl (by simp)

theorem rust_empty_slice_valid (s : Core.State) (owner : OwnerId)
    (offset elemSize elemAlign : Nat) (mode : AccessMode)
    (hAlignPos : 0 < elemAlign) (hPow2 : elemAlign.isPowerOfTwo = true)
    (hOffAlign : offset % elemAlign = 0) (hStride : elemSize % elemAlign = 0) :
    RustSliceValid s ⟨owner, offset, 0, elemSize, elemAlign, mode, false⟩ := by
  refine ⟨rfl, hAlignPos, hPow2, hOffAlign, hStride, ?_, Or.inl rfl⟩
  dsimp [RustSliceSpec.byteLen, isizeMax64]
  omega

def RustSliceSpec.interval (slice : RustSliceSpec) : Interval :=
  ⟨slice.byteOffset, slice.byteOffset + slice.byteLen⟩

theorem RustSliceSpec.mem_locations (slice : RustSliceSpec) (location : ByteLocation) :
    location ∈ slice.locations ↔ location.allocation = slice.owner ∧ slice.interval.Contains location.offset := by
  cases location with
  | mk owner offset =>
    simp only [RustSliceSpec.locations, List.mem_map, List.mem_range, RustSliceSpec.interval,
      Interval.Contains, ByteLocation.mk.injEq]
    constructor
    · rintro ⟨index, valid, rfl, rfl⟩
      exact ⟨rfl, by omega, by omega⟩
    · rintro ⟨rfl, lower, upper⟩
      exact ⟨offset - slice.byteOffset, by omega, rfl, by omega⟩

/-- Compare allocations and interval endpoints without enumerating the bytes. -/
def checkRustSlicePairCompatible (a b : RustSliceSpec) : Bool :=
  letI : Decidable (AccessMode.Compatible a.mode b.mode) :=
    inferInstanceAs (Decidable (a.mode = .shared ∧ b.mode = .shared))
  decide (a.owner ≠ b.owner) || a.interval.disjoint b.interval ||
    decide (AccessMode.Compatible a.mode b.mode)

def RustSlicesCompatible (a b : RustSliceSpec) : Prop :=
  ∀ loc ∈ a.locations, loc ∈ b.locations → AccessMode.Compatible a.mode b.mode

theorem checkRustSlicePairCompatible_correct (a b : RustSliceSpec) :
    checkRustSlicePairCompatible a b = true ↔ RustSlicesCompatible a b := by
  simp only [checkRustSlicePairCompatible, RustSlicesCompatible, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, Interval.disjoint_correct, RustSliceSpec.mem_locations]
  constructor
  · rintro ((separate | disjoint) | shared) location ⟨ownerA, inA⟩ ⟨ownerB, inB⟩
    · exact False.elim (separate (ownerA.symm.trans ownerB))
    · exact False.elim (disjoint location.offset ⟨inA, inB⟩)
    · exact shared
  · intro compatible
    by_cases same : a.owner = b.owner
    · by_cases shared : AccessMode.Compatible a.mode b.mode
      · exact .inr shared
      · exact .inl (.inr fun index ⟨inA, inB⟩ =>
          shared (compatible ⟨a.owner, index⟩ ⟨rfl, inA⟩ ⟨same, inB⟩))
    · exact .inl (.inl same)

theorem rust_disjoint_soa_columns_mut_compatible (owner : OwnerId) (length f1 f2 : Nat)
    (hNe : f1 ≠ f2) :
    RustSlicesCompatible
      ⟨owner, f1 * length, length, 1, 1, .exclusive, false⟩
      ⟨owner, f2 * length, length, 1, 1, .exclusive, false⟩ := by
  intro loc ha hb
  simp only [RustSliceSpec.locations, RustSliceSpec.byteLen, Nat.mul_one,
    List.mem_map, List.mem_range] at ha hb
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨j, hj, hEq⟩ := hb
  have hOff : f2 * length + j = f1 * length + i := congrArg ByteLocation.offset hEq
  rcases Nat.lt_or_gt_of_ne hNe with hLt | hGt
  · have hMul := Nat.mul_le_mul_right length (Nat.succ_le_of_lt hLt)
    simp only [Nat.succ_mul] at hMul
    omega
  · have hMul := Nat.mul_le_mul_right length (Nat.succ_le_of_lt hGt)
    simp only [Nat.succ_mul] at hMul
    omega

/-! ## Synchronous FFI Call View Bracket Restoration -/

def pushCallViews (s : Core.State) (vs : List Core.View) : Core.State :=
  { s with views := vs ++ s.views }

def popCallViews (s : Core.State) (ids : List ViewId) : Core.State :=
  { s with views := s.views.filter fun v => !(ids.contains v.id) }

theorem rustCall_restores_views (s : Core.State) (vs : List Core.View)
    (hFresh : ∀ v ∈ vs, s.view v.id = none) :
    popCallViews (pushCallViews s vs) (vs.map Core.View.id) = s := by
  cases s with
  | mk allocs handles views issued obs =>
    dsimp [popCallViews, pushCallViews]
    congr 1
    rw [List.filter_append]
    have hNewNil : vs.filter (fun v => !((vs.map Core.View.id).contains v.id)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro v hv
      simp
      exact ⟨v, hv, rfl⟩
    have hOldSame : views.filter (fun v => !((vs.map Core.View.id).contains v.id)) = views := by
      rw [List.filter_eq_self]
      intro w hw
      simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, List.contains_iff_mem, List.mem_map,
        not_exists, not_and]
      intro v hv hEq
      have hNone := hFresh v hv
      have hBad := List.find?_eq_none.mp hNone w hw
      simp [hEq] at hBad
    rw [hNewNil, hOldSame, List.nil_append]

/-! ## Opaque Affine Rust-Owned Handle (`RustOwn`) Lifecycle -/

inductive RustOwnStatus where
  | alive
  | dropped
  deriving Repr, DecidableEq

inductive RustOwnAction where
  | useHandle
  | dropHandle
  deriving Repr, DecidableEq

def rustOwnStep (st : RustOwnStatus) : RustOwnAction → Option RustOwnStatus
  | .useHandle => match st with | .alive => some .alive | .dropped => none
  | .dropHandle => match st with | .alive => some .dropped | .dropped => none

theorem rustOwn_no_double_drop :
    rustOwnStep .dropped .dropHandle = none := rfl

theorem rustOwn_no_use_after_drop :
    rustOwnStep .dropped .useHandle = none := rfl

theorem rustOwn_drop_consumes :
    rustOwnStep .alive .dropHandle = some .dropped ∧
    rustOwnStep .dropped .dropHandle = none ∧
    rustOwnStep .dropped .useHandle = none :=
  ⟨rfl, rfl, rfl⟩

/-! ## Negative Rust FFI Counterexamples -/

theorem rust_packed_subbyte_slice_rejected (s : Core.State) :
    checkRustSlice s ⟨0, 0, 4, 1, 1, .shared, true⟩ = false := by
  simp [checkRustSlice, checkRustSliceWhere]

theorem rust_unaligned_slice_rejected (s : Core.State) :
    checkRustSlice s ⟨0, 3, 2, 4, 4, .shared, false⟩ = false := by
  simp [checkRustSlice, checkRustSliceWhere]

theorem rust_overlapping_mut_slices_rejected :
    checkRustSlicePairCompatible
      ⟨0, 0, 4, 1, 1, .exclusive, false⟩
      ⟨0, 2, 4, 1, 1, .exclusive, false⟩ = false := by
  decide

end Aethel.RustFFI
