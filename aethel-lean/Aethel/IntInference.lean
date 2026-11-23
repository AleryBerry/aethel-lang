import Aethel.IntegerTypes
import Aethel.AutomaticLayout

namespace Aethel.IntInference

open Aethel

/-! ## Exact Bit-Width Calculation & Minimality -/

private def bitLengthAux : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 0
  | fuel + 1, n + 1 => bitLengthAux fuel ((n + 1) / 2) + 1

/-- Exact number of bits required to represent natural number `n` in unsigned binary (`bitLength 0 = 0`). -/
def bitLength (n : Nat) : Nat :=
  bitLengthAux n n

private theorem lt_two_pow_bitLengthAux :
    ∀ fuel n : Nat, n ≤ fuel → n < 2 ^ bitLengthAux fuel n
  | 0, 0, _ => by simp [bitLengthAux]
  | 0, n + 1, h => by omega
  | _ + 1, 0, _ => by simp [bitLengthAux]
  | fuel + 1, n + 1, h => by
    have hDivLe : (n + 1) / 2 ≤ fuel := by omega
    have hSub := lt_two_pow_bitLengthAux fuel ((n + 1) / 2) hDivLe
    simp only [bitLengthAux, Nat.pow_succ]
    omega

theorem lt_two_pow_bitLength (n : Nat) : n < 2 ^ bitLength n :=
  lt_two_pow_bitLengthAux n n (Nat.le_refl n)

private theorem bitLengthAux_le_of_lt_two_pow :
    ∀ w fuel n : Nat, n < 2 ^ w → bitLengthAux fuel n ≤ w
  | _, 0, _, _ => by simp [bitLengthAux]
  | _, _ + 1, 0, _ => by simp [bitLengthAux]
  | 0, _ + 1, n + 1, h => by simp at h
  | w + 1, fuel + 1, n + 1, h => by
    have hDiv : (n + 1) / 2 < 2 ^ w := by
      rw [Nat.pow_succ] at h
      omega
    have ih := bitLengthAux_le_of_lt_two_pow w fuel ((n + 1) / 2) hDiv
    simp only [bitLengthAux]
    omega

theorem bitLength_le_of_lt_two_pow {n w : Nat} (h : n < 2 ^ w) : bitLength n ≤ w :=
  bitLengthAux_le_of_lt_two_pow w n n h

/-- Minimum positive unsigned bit width (`≥ 1`) holding natural number `n`. -/
def minUnsignedBits (n : Nat) : Nat :=
  max 1 (bitLength n)

theorem minUnsignedBits_pos (n : Nat) : 0 < minUnsignedBits n := by
  unfold minUnsignedBits
  omega

theorem lt_two_pow_minUnsignedBits (n : Nat) : n < 2 ^ minUnsignedBits n := by
  have hLe : bitLength n ≤ minUnsignedBits n := Nat.le_max_right 1 _
  have hPow : 2 ^ bitLength n ≤ 2 ^ minUnsignedBits n :=
    Nat.pow_le_pow_right (by decide) hLe
  exact Nat.lt_of_lt_of_le (lt_two_pow_bitLength n) hPow

theorem minUnsignedBits_minimal {n w : Nat} (hw : 0 < w) (hLt : n < 2 ^ w) :
    minUnsignedBits n ≤ w := by
  have hBit : bitLength n ≤ w := bitLength_le_of_lt_two_pow hLt
  unfold minUnsignedBits
  omega

/-- Unsigned magnitude governing two's complement signed bit requirement over `[lo, hi]`. -/
def signedMagnitude (lo hi : Int) : Nat :=
  max (if lo < 0 then (-lo - 1).toNat else 0) (if 0 ≤ hi then hi.toNat else 0)

/-- Minimum signed bit width (`≥ 1`) accommodating every integer in `[lo, hi]`. -/
def minSignedBits (lo hi : Int) : Nat :=
  bitLength (signedMagnitude lo hi) + 1

theorem minSignedBits_pos (lo hi : Int) : 0 < minSignedBits lo hi := by
  unfold minSignedBits
  omega

theorem minSignedBits_fits {lo hi : Int} :
    let w := minSignedBits lo hi;
    -(2 : Int) ^ (w - 1) ≤ lo ∧ hi < (2 : Int) ^ (w - 1) := by
  dsimp only [minSignedBits]
  simp only [Nat.add_sub_cancel]
  have hMag := lt_two_pow_bitLength (signedMagnitude lo hi)
  have hLeftNat : (if lo < 0 then (-lo - 1).toNat else 0) < 2 ^ bitLength (signedMagnitude lo hi) :=
    Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hMag
  have hRightNat : (if 0 ≤ hi then hi.toNat else 0) < 2 ^ bitLength (signedMagnitude lo hi) :=
    Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hMag
  have hCastPow : ((2 ^ bitLength (signedMagnitude lo hi) : Nat) : Int) =
      (2 : Int) ^ bitLength (signedMagnitude lo hi) := by
    rw [Int.natCast_pow]; rfl
  constructor
  · by_cases hLo : lo < 0
    · simp only [hLo, ↓reduceIte] at hLeftNat
      have hInt : ((-lo - 1).toNat : Int) < (2 : Int) ^ bitLength (signedMagnitude lo hi) := by
        simpa [hCastPow] using Int.ofNat_lt.mpr hLeftNat
      omega
    · have hPowNonneg : (0 : Int) ≤ (2 : Int) ^ bitLength (signedMagnitude lo hi) := by
        rw [← hCastPow]
        exact Int.natCast_nonneg _
      omega
  · by_cases hHi : 0 ≤ hi
    · simp only [hHi, ↓reduceIte] at hRightNat
      have hInt : (hi.toNat : Int) < (2 : Int) ^ bitLength (signedMagnitude lo hi) := by
        simpa [hCastPow] using Int.ofNat_lt.mpr hRightNat
      omega
    · have hPowPos : (0 : Int) < (2 : Int) ^ bitLength (signedMagnitude lo hi) := by
        rw [← hCastPow]
        exact Int.ofNat_lt.mpr (Nat.two_pow_pos _)
      omega

theorem minSignedBits_minimal {lo hi : Int} {w : Nat} (hw : 0 < w)
    (hLow : -(2 : Int) ^ (w - 1) ≤ lo) (hHigh : hi < (2 : Int) ^ (w - 1)) :
    minSignedBits lo hi ≤ w := by
  have hPowPosNat : 0 < 2 ^ (w - 1) := Nat.two_pow_pos (w - 1)
  have hCastPow : ((2 ^ (w - 1) : Nat) : Int) = (2 : Int) ^ (w - 1) := by
    rw [Int.natCast_pow]; rfl
  have hLeft : (if lo < 0 then (-lo - 1).toNat else 0) < 2 ^ (w - 1) := by
    by_cases hLo : lo < 0
    · simp only [hLo, ↓reduceIte]
      apply Int.ofNat_lt.mp
      rw [hCastPow]
      omega
    · simp only [hLo, ↓reduceIte]
      exact hPowPosNat
  have hRight : (if 0 ≤ hi then hi.toNat else 0) < 2 ^ (w - 1) := by
    by_cases hHi : 0 ≤ hi
    · simp only [hHi, ↓reduceIte]
      apply Int.ofNat_lt.mp
      rw [hCastPow]
      omega
    · simp only [hHi, ↓reduceIte]
      exact hPowPosNat
  have hMag : signedMagnitude lo hi < 2 ^ (w - 1) := by
    unfold signedMagnitude
    omega
  have hBit : bitLength (signedMagnitude lo hi) ≤ w - 1 :=
    bitLength_le_of_lt_two_pow hMag
  unfold minSignedBits
  omega

/-! ## Closed Integer Ranges & Universal Bit-Optimal Type Synthesis -/

/-- Non-empty closed mathematical integer interval `[lo, hi]`. -/
structure IntRange where
  lo : Int
  hi : Int
  valid : lo ≤ hi
  deriving Repr, DecidableEq

def IntRange.Contains (r : IntRange) (x : Int) : Prop :=
  r.lo ≤ x ∧ x ≤ r.hi

theorem IntRange.lo_mem (r : IntRange) : r.Contains r.lo :=
  ⟨Int.le_refl _, r.valid⟩

theorem IntRange.hi_mem (r : IntRange) : r.Contains r.hi :=
  ⟨r.valid, Int.le_refl _⟩

def IntRange.minValue (ty : IntegerType) : Int :=
  match ty with
  | .unsigned _ => 0
  | .signed w => -(2 : Int) ^ (w.bits - 1)

def IntRange.maxValue (ty : IntegerType) : Int :=
  match ty with
  | .unsigned w => (2 : Int) ^ w.bits - 1
  | .signed w => (2 : Int) ^ (w.bits - 1) - 1

theorem IntRange.minValue_le_maxValue (ty : IntegerType) :
    IntRange.minValue ty ≤ IntRange.maxValue ty := by
  cases ty with
  | unsigned w =>
    have hPow : (1 : Int) ≤ (2 : Int) ^ w.bits := by
      have hNat : 1 ≤ 2 ^ w.bits := Nat.two_pow_pos w.bits
      have hCast := Int.ofNat_le.mpr hNat
      simpa [Int.natCast_pow] using hCast
    dsimp only [minValue, maxValue]
    omega
  | signed w =>
    have hPow : (1 : Int) ≤ (2 : Int) ^ (w.bits - 1) := by
      have hNat : 1 ≤ 2 ^ (w.bits - 1) := Nat.two_pow_pos (w.bits - 1)
      have hCast := Int.ofNat_le.mpr hNat
      simpa [Int.natCast_pow] using hCast
    dsimp only [minValue, maxValue]
    omega

/-- Exact mathematical value range of any `IntegerType` (`u1..u65535`, `i1..i65535`). -/
def IntRange.ofType (ty : IntegerType) : IntRange :=
  ⟨IntRange.minValue ty, IntRange.maxValue ty, IntRange.minValue_le_maxValue ty⟩

theorem IntRange.ofType_contains_iff (ty : IntegerType) (x : Int) :
    (IntRange.ofType ty).Contains x ↔ ty.Fits x := by
  cases ty with
  | unsigned w =>
    simp only [IntRange.ofType, IntRange.Contains, IntRange.minValue, IntRange.maxValue,
      IntegerType.Fits]
    omega
  | signed w =>
    simp only [IntRange.ofType, IntRange.Contains, IntRange.minValue, IntRange.maxValue,
      IntegerType.Fits]
    omega

def IntRange.fitsType (r : IntRange) (ty : IntegerType) : Bool :=
  decide (ty.Fits r.lo ∧ ty.Fits r.hi)

theorem IntRange.fitsType_sound {r : IntRange} {ty : IntegerType}
    (h : r.fitsType ty = true) : ∀ x, r.Contains x → ty.Fits x := by
  have ⟨hLo, hHi⟩ := of_decide_eq_true h
  intro x hx
  have hLower : IntRange.minValue ty ≤ r.lo := ((ofType_contains_iff ty r.lo).mpr hLo).1
  have hUpper : r.hi ≤ IntRange.maxValue ty := ((ofType_contains_iff ty r.hi).mpr hHi).2
  apply (ofType_contains_iff ty x).mp
  exact ⟨Int.le_trans hLower hx.1, Int.le_trans hx.2 hUpper⟩

theorem IntRange.fitsType_iff (r : IntRange) (ty : IntegerType) :
    r.fitsType ty = true ↔ (∀ x, r.Contains x → ty.Fits x) := by
  constructor
  · exact r.fitsType_sound
  · intro hAll
    unfold fitsType
    exact decide_eq_true ⟨hAll r.lo r.lo_mem, hAll r.hi r.hi_mem⟩

/-- Synthesize the minimum-bit-width `IntegerType` capable of storing every integer in `r`. -/
def inferIntegerType (r : IntRange) : Option IntegerType :=
  if 0 ≤ r.lo then
    (IntegerWidth.ofNat? (minUnsignedBits r.hi.toNat)).map .unsigned
  else
    (IntegerWidth.ofNat? (minSignedBits r.lo r.hi)).map .signed

theorem inferIntegerType_fits {r : IntRange} {ty : IntegerType}
    (h : inferIntegerType r = some ty) : ∀ x, r.Contains x → ty.Fits x := by
  unfold inferIntegerType at h
  split at h
  · rename_i hNonneg
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨w, hOf, rfl⟩ := h
    have hwBits : w.bits = minUnsignedBits r.hi.toNat :=
      IntegerWidth.ofNat?_some_iff.mp hOf
    have hHiLt : r.hi < (2 : Int) ^ w.bits := by
      have hNat := lt_two_pow_minUnsignedBits r.hi.toNat
      have hInt := Int.ofNat_lt.mpr hNat
      rw [← hwBits] at hInt
      have hHiNonneg : 0 ≤ r.hi := Int.le_trans hNonneg r.valid
      have hToNat : (r.hi.toNat : Int) = r.hi := Int.toNat_of_nonneg hHiNonneg
      have hPow : ((2 ^ w.bits : Nat) : Int) = (2 : Int) ^ w.bits := by
        rw [Int.natCast_pow]; rfl
      rw [hToNat, hPow] at hInt
      exact hInt
    intro x hx
    simp only [IntegerType.Fits]
    exact ⟨Int.le_trans hNonneg hx.1, Int.lt_of_le_of_lt hx.2 hHiLt⟩
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨w, hOf, rfl⟩ := h
    have hwBits : w.bits = minSignedBits r.lo r.hi :=
      IntegerWidth.ofNat?_some_iff.mp hOf
    have ⟨hLow, hHigh⟩ := minSignedBits_fits (lo := r.lo) (hi := r.hi)
    rw [← hwBits] at hLow hHigh
    intro x hx
    simp only [IntegerType.Fits]
    exact ⟨Int.le_trans hLow hx.1, Int.lt_of_le_of_lt hx.2 hHigh⟩

/-- Optimality theorem: any inferred `IntegerType` uses at most as many bits as *any*
other `IntegerType` (signed or unsigned) that covers the same interval `r`. -/
theorem inferIntegerType_minimal {r : IntRange} {ty : IntegerType}
    (h : inferIntegerType r = some ty) (other : IntegerType)
    (hOther : ∀ x, r.Contains x → other.Fits x) :
    ty.bits ≤ other.bits := by
  unfold inferIntegerType at h
  split at h
  · rename_i hNonneg
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨w, hOf, rfl⟩ := h
    have hwBits : w.bits = minUnsignedBits r.hi.toNat :=
      IntegerWidth.ofNat?_some_iff.mp hOf
    change w.bits ≤ other.bits
    rw [hwBits]
    have hHiFits := hOther r.hi r.hi_mem
    cases other with
    | unsigned w2 =>
      simp only [IntegerType.Fits] at hHiFits
      have hCast : (r.hi.toNat : Int) = r.hi := Int.toNat_of_nonneg (Int.le_trans hNonneg r.valid)
      have hPow : ((2 ^ w2.bits : Nat) : Int) = (2 : Int) ^ w2.bits := by
        rw [Int.natCast_pow]; rfl
      have hNat : r.hi.toNat < 2 ^ w2.bits :=
        Int.ofNat_lt.mp (by rw [hCast, hPow]; exact hHiFits.2)
      exact minUnsignedBits_minimal w2.pos hNat
    | signed w2 =>
      simp only [IntegerType.Fits] at hHiFits
      have hCast : (r.hi.toNat : Int) = r.hi := Int.toNat_of_nonneg (Int.le_trans hNonneg r.valid)
      have hPow : ((2 ^ (w2.bits - 1) : Nat) : Int) = (2 : Int) ^ (w2.bits - 1) := by
        rw [Int.natCast_pow]; rfl
      have hNat : r.hi.toNat < 2 ^ (w2.bits - 1) :=
        Int.ofNat_lt.mp (by rw [hCast, hPow]; exact hHiFits.2)
      have hBit : bitLength r.hi.toNat ≤ w2.bits - 1 := bitLength_le_of_lt_two_pow hNat
      have hPos : 0 < w2.bits := w2.pos
      dsimp only [minUnsignedBits, IntegerType.bits, IntegerType.width]
      omega
  · rename_i hNotNonneg
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨w, hOf, rfl⟩ := h
    have hwBits : w.bits = minSignedBits r.lo r.hi :=
      IntegerWidth.ofNat?_some_iff.mp hOf
    change w.bits ≤ other.bits
    rw [hwBits]
    have hLoFits := hOther r.lo r.lo_mem
    have hHiFits := hOther r.hi r.hi_mem
    cases other with
    | unsigned w2 =>
      simp only [IntegerType.Fits] at hLoFits
      exact False.elim (hNotNonneg hLoFits.1)
    | signed w2 =>
      simp only [IntegerType.Fits] at hLoFits hHiFits
      exact minSignedBits_minimal w2.pos hLoFits.1 hHiFits.2

/-! ## Interval Arithmetic & Branch Narrowing -/

def IntRange.singleton (c : Int) : IntRange :=
  ⟨c, c, Int.le_refl c⟩

theorem IntRange.singleton_sound (c : Int) : (IntRange.singleton c).Contains c :=
  ⟨Int.le_refl c, Int.le_refl c⟩

def IntRange.add (a b : IntRange) : IntRange :=
  ⟨a.lo + b.lo, a.hi + b.hi, Int.add_le_add a.valid b.valid⟩

theorem IntRange.add_sound {a b : IntRange} {x y : Int}
    (hx : a.Contains x) (hy : b.Contains y) : (a.add b).Contains (x + y) :=
  ⟨Int.add_le_add hx.1 hy.1, Int.add_le_add hx.2 hy.2⟩

def IntRange.neg (a : IntRange) : IntRange :=
  ⟨-a.hi, -a.lo, Int.neg_le_neg a.valid⟩

theorem IntRange.neg_sound {a : IntRange} {x : Int}
    (hx : a.Contains x) : a.neg.Contains (-x) :=
  ⟨Int.neg_le_neg hx.2, Int.neg_le_neg hx.1⟩

def IntRange.sub (a b : IntRange) : IntRange :=
  ⟨a.lo - b.hi, a.hi - b.lo, by have := a.valid; have := b.valid; omega⟩

theorem IntRange.sub_sound {a b : IntRange} {x y : Int}
    (hx : a.Contains x) (hy : b.Contains y) : (a.sub b).Contains (x - y) := by
  simp only [Contains, sub]
  exact ⟨by have := hx.1; have := hy.2; omega, by have := hx.2; have := hy.1; omega⟩

private def min4 (a b c d : Int) : Int :=
  min (min a b) (min c d)

private def max4 (a b c d : Int) : Int :=
  max (max a b) (max c d)

private theorem min4_le_max4 (a b c d : Int) : min4 a b c d ≤ max4 a b c d := by
  unfold min4 max4
  omega

private theorem mul_endpoint_bounds {x y lo hi : Int} (hy : lo ≤ y ∧ y ≤ hi) :
    min (x * lo) (x * hi) ≤ x * y ∧ x * y ≤ max (x * lo) (x * hi) := by
  by_cases hx : 0 ≤ x
  · have hL := Int.mul_le_mul_of_nonneg_left hy.1 hx
    have hR := Int.mul_le_mul_of_nonneg_left hy.2 hx
    omega
  · have hxNeg : x ≤ 0 := by omega
    have hL := Int.mul_le_mul_of_nonpos_left hxNeg hy.2
    have hR := Int.mul_le_mul_of_nonpos_left hxNeg hy.1
    omega

private theorem endpoint_mul_bounds {x lo hi y : Int} (hx : lo ≤ x ∧ x ≤ hi) :
    min (lo * y) (hi * y) ≤ x * y ∧ x * y ≤ max (lo * y) (hi * y) := by
  by_cases hy : 0 ≤ y
  · have hL := Int.mul_le_mul_of_nonneg_right hx.1 hy
    have hR := Int.mul_le_mul_of_nonneg_right hx.2 hy
    omega
  · have hyNeg : y ≤ 0 := by omega
    have hL := Int.mul_le_mul_of_nonpos_right hx.2 hyNeg
    have hR := Int.mul_le_mul_of_nonpos_right hx.1 hyNeg
    omega

def IntRange.mul (a b : IntRange) : IntRange :=
  ⟨ min4 (a.lo * b.lo) (a.lo * b.hi) (a.hi * b.lo) (a.hi * b.hi)
  , max4 (a.lo * b.lo) (a.lo * b.hi) (a.hi * b.lo) (a.hi * b.hi)
  , min4_le_max4 _ _ _ _ ⟩

theorem IntRange.mul_sound {a b : IntRange} {x y : Int}
    (hx : a.Contains x) (hy : b.Contains y) : (a.mul b).Contains (x * y) := by
  have h1 := mul_endpoint_bounds (x := x) hy
  have hLo := endpoint_mul_bounds (y := b.lo) hx
  have hHi := endpoint_mul_bounds (y := b.hi) hx
  simp only [Contains, mul, min4, max4]
  constructor <;> omega

def IntRange.join (a b : IntRange) : IntRange :=
  ⟨min a.lo b.lo, max a.hi b.hi, by have := a.valid; have := b.valid; omega⟩

theorem IntRange.join_left {a b : IntRange} {x : Int}
    (hx : a.Contains x) : (a.join b).Contains x := by
  simp only [Contains, join]
  exact ⟨by have := hx.1; omega, by have := hx.2; omega⟩

theorem IntRange.join_right {a b : IntRange} {x : Int}
    (hx : b.Contains x) : (a.join b).Contains x := by
  simp only [Contains, join]
  exact ⟨by have := hx.1; omega, by have := hx.2; omega⟩

def IntRange.narrowUpper? (r : IntRange) (bound : Int) : Option IntRange :=
  if h : r.lo ≤ min r.hi bound then some ⟨r.lo, min r.hi bound, h⟩ else none

theorem IntRange.narrowUpper_sound {r narrowed : IntRange} {bound x : Int}
    (hNarrow : r.narrowUpper? bound = some narrowed)
    (hx : r.Contains x) (hLe : x ≤ bound) : narrowed.Contains x := by
  unfold narrowUpper? at hNarrow
  split at hNarrow
  · simp only [Option.some.injEq] at hNarrow
    subst hNarrow
    simp only [Contains]
    exact ⟨hx.1, by have := hx.2; omega⟩
  · contradiction

def IntRange.narrowLower? (r : IntRange) (bound : Int) : Option IntRange :=
  if h : max r.lo bound ≤ r.hi then some ⟨max r.lo bound, r.hi, h⟩ else none

theorem IntRange.narrowLower_sound {r narrowed : IntRange} {bound x : Int}
    (hNarrow : r.narrowLower? bound = some narrowed)
    (hx : r.Contains x) (hGe : bound ≤ x) : narrowed.Contains x := by
  unfold narrowLower? at hNarrow
  split at hNarrow
  · simp only [Option.some.injEq] at hNarrow
    subst hNarrow
    simp only [Contains]
    exact ⟨by have := hx.1; omega, hx.2⟩
  · contradiction

/-! ## Total Saturating, Explicit Wrapping & Fallible Checked Arithmetic -/

/-- Clamp any mathematical integer to the exact bounds of `ty` (semantics for `+|`, `-|`, `*|` casts). -/
def clampToType (ty : IntegerType) (x : Int) : Int :=
  max (IntRange.minValue ty) (min (IntRange.maxValue ty) x)

theorem clampToType_fits (ty : IntegerType) (x : Int) :
    ty.Fits (clampToType ty x) := by
  have hMinMax := IntRange.minValue_le_maxValue ty
  apply (IntRange.ofType_contains_iff ty _).mp
  simp only [clampToType, IntRange.ofType, IntRange.Contains]
  constructor <;> omega

theorem clampToType_id_of_fits {ty : IntegerType} {x : Int} (h : ty.Fits x) :
    clampToType ty x = x := by
  have hx := (IntRange.ofType_contains_iff ty x).mpr h
  simp only [IntRange.ofType, IntRange.Contains] at hx
  simp only [clampToType]
  omega

/-- Wrap any mathematical integer modulo `2^bits` into `ty`'s range (semantics for `+%`, `-%`, `*%`). -/
def wrapToType (ty : IntegerType) (x : Int) : Int :=
  match ty with
  | .unsigned w => x % (2 : Int) ^ w.bits
  | .signed w => x.bmod (2 ^ w.bits)

theorem wrapToType_fits (ty : IntegerType) (x : Int) :
    ty.Fits (wrapToType ty x) := by
  cases ty with
  | unsigned w =>
    have hPowPos : (0 : Int) < (2 : Int) ^ w.bits := by
      have hNat := Nat.two_pow_pos w.bits
      have hCast := Int.ofNat_lt.mpr hNat
      simpa [Int.natCast_pow] using hCast
    exact ⟨Int.emod_nonneg _ (Int.ne_of_gt hPowPos), Int.emod_lt_of_pos _ hPowPos⟩
  | signed w =>
    unfold wrapToType IntegerType.Fits
    have hwEq : w.bits = (w.bits - 1) + 1 := (Nat.sub_add_cancel w.pos).symm
    have hModNatPos : 0 < 2 ^ w.bits := Nat.two_pow_pos w.bits
    have hModEq : 2 ^ w.bits = 2 * 2 ^ (w.bits - 1) := by
      calc
        2 ^ w.bits = 2 ^ ((w.bits - 1) + 1) := by rw [← hwEq]
        _ = 2 ^ (w.bits - 1) * 2 := Nat.pow_succ _ _
        _ = 2 * 2 ^ (w.bits - 1) := Nat.mul_comm _ _
    have hModCast : ((2 ^ w.bits : Nat) : Int) = 2 * ((2 ^ (w.bits - 1) : Nat) : Int) := by
      rw [hModEq, Int.natCast_mul]; rfl
    have hNatCast : ((2 ^ (w.bits - 1) : Nat) : Int) = (2 : Int) ^ (w.bits - 1) := by
      rw [Int.natCast_pow]; rfl
    have hLow := Int.le_bmod hModNatPos (x := x)
    have hHigh := Int.bmod_lt hModNatPos (x := x)
    dsimp only [wrapToType, IntegerType.Fits]
    omega

/-- Checked runtime arithmetic returning `Option Int` (`none` iff result overflows `ty`). -/
def checkedValue (ty : IntegerType) (x : Int) : Option Int :=
  if ty.Fits x then some x else none

def checkedAdd (ty : IntegerType) (a b : Int) : Option Int := checkedValue ty (a + b)
def checkedSub (ty : IntegerType) (a b : Int) : Option Int := checkedValue ty (a - b)
def checkedMul (ty : IntegerType) (a b : Int) : Option Int := checkedValue ty (a * b)

theorem checkedAdd_sound (ty : IntegerType) (a b : Int) :
    (∀ res, checkedAdd ty a b = some res → ty.Fits res ∧ res = a + b) ∧
    (checkedAdd ty a b = none ↔ ¬ ty.Fits (a + b)) := by
  unfold checkedAdd checkedValue
  by_cases h : ty.Fits (a + b) <;> simp [h]

theorem checkedSub_sound (ty : IntegerType) (a b : Int) :
    (∀ res, checkedSub ty a b = some res → ty.Fits res ∧ res = a - b) ∧
    (checkedSub ty a b = none ↔ ¬ ty.Fits (a - b)) := by
  unfold checkedSub checkedValue
  by_cases h : ty.Fits (a - b) <;> simp [h]

theorem checkedMul_sound (ty : IntegerType) (a b : Int) :
    (∀ res, checkedMul ty a b = some res → ty.Fits res ∧ res = a * b) ∧
    (checkedMul ty a b = none ↔ ¬ ty.Fits (a * b)) := by
  unfold checkedMul checkedValue
  by_cases h : ty.Fits (a * b) <;> simp [h]

/-! ## Compile-Time Overflow-Free Expression Checker & Automatic Inference -/

inductive IntExpr where
  | const (value : Int)
  | var (id : Nat)
  | add (left right : IntExpr)
  | sub (left right : IntExpr)
  | mul (left right : IntExpr)
  | neg (inner : IntExpr)
  | checkedCast (target : IntegerType) (inner : IntExpr)
  | satCast (target : IntegerType) (inner : IntExpr)
  | wrapCast (target : IntegerType) (inner : IntExpr)
  deriving Repr, DecidableEq

/-- Exact operational semantics of integer expressions. `checkedCast` evaluates the underlying
integer directly because static verification forbids runtime overflow. -/
def IntExpr.eval (ρ : Nat → Int) : IntExpr → Int
  | .const c => c
  | .var id => ρ id
  | .add l r => l.eval ρ + r.eval ρ
  | .sub l r => l.eval ρ - r.eval ρ
  | .mul l r => l.eval ρ * r.eval ρ
  | .neg e => -(e.eval ρ)
  | .checkedCast _ e => e.eval ρ
  | .satCast target e => clampToType target (e.eval ρ)
  | .wrapCast target e => wrapToType target (e.eval ρ)

/-- Independent semantic invariant asserting that no unchecked overflow occurs anywhere in `e`. -/
def IntExpr.NoOverflow (ρ : Nat → Int) : IntExpr → Prop
  | .const _ | .var _ => True
  | .add l r | .sub l r | .mul l r => l.NoOverflow ρ ∧ r.NoOverflow ρ
  | .neg e | .satCast _ e | .wrapCast _ e => e.NoOverflow ρ
  | .checkedCast target e => e.NoOverflow ρ ∧ target.Fits (e.eval ρ)

def EnvValid (Γ : Nat → Option IntRange) (ρ : Nat → Int) : Prop :=
  ∀ id r, Γ id = some r → r.Contains (ρ id)

def EnvValid.ofTypes (Δ : Nat → Option IntegerType) : Nat → Option IntRange :=
  fun id => (Δ id).map IntRange.ofType

theorem EnvValid.ofTypes_sound {Δ : Nat → Option IntegerType} {ρ : Nat → Int}
    (h : ∀ id ty, Δ id = some ty → ty.Fits (ρ id)) :
    EnvValid (EnvValid.ofTypes Δ) ρ := by
  intro id r hr
  simp only [ofTypes, Option.map_eq_some_iff] at hr
  obtain ⟨ty, hTy, rfl⟩ := hr
  exact (IntRange.ofType_contains_iff ty (ρ id)).mpr (h id ty hTy)

inductive OverflowError where
  | unboundVar (id : Nat)
  | potentialOverflow (target : IntegerType) (actualLo actualHi : Int)
  | widthExceeded (lo hi : Int)
  deriving Repr, DecidableEq

/-- Compile-time range analyzer: rejects every expression that could possibly overflow any
target annotation, while propagating exact mathematical intervals for unannotated subexpressions. -/
def checkExpr (Γ : Nat → Option IntRange) : IntExpr → Except OverflowError IntRange
  | .const c => .ok (IntRange.singleton c)
  | .var id =>
    match Γ id with
    | some r => .ok r
    | none => .error (.unboundVar id)
  | .add l r => return (← checkExpr Γ l).add (← checkExpr Γ r)
  | .sub l r => return (← checkExpr Γ l).sub (← checkExpr Γ r)
  | .mul l r => return (← checkExpr Γ l).mul (← checkExpr Γ r)
  | .neg e => return (← checkExpr Γ e).neg
  | .checkedCast target e => do
    let r ← checkExpr Γ e
    if r.fitsType target then
      return r
    else
      .error (.potentialOverflow target r.lo r.hi)
  | .satCast target e => do
    let _ ← checkExpr Γ e
    return IntRange.ofType target
  | .wrapCast target e => do
    let _ ← checkExpr Γ e
    return IntRange.ofType target

/-- Infer both the exact propagated interval and the bit-minimal `IntegerType` for any
overflow-free expression. -/
def inferExprType (Γ : Nat → Option IntRange) (e : IntExpr) :
    Except OverflowError (IntRange × IntegerType) := do
  let r ← checkExpr Γ e
  match inferIntegerType r with
  | some ty => .ok (r, ty)
  | none => .error (.widthExceeded r.lo r.hi)

theorem checkExpr_sound {Γ : Nat → Option IntRange} {ρ : Nat → Int}
    {e : IntExpr} {r : IntRange} (hEnv : EnvValid Γ ρ)
    (hCheck : checkExpr Γ e = .ok r) :
    r.Contains (e.eval ρ) ∧ e.NoOverflow ρ := by
  induction e generalizing r with
  | const c =>
    cases hCheck
    exact ⟨IntRange.singleton_sound c, trivial⟩
  | var id =>
    unfold checkExpr at hCheck
    cases hLookup : Γ id with
    | none => simp [hLookup] at hCheck
    | some range =>
      simp only [hLookup, Except.ok.injEq] at hCheck
      rcases hCheck with rfl
      exact ⟨hEnv id _ hLookup, trivial⟩
  | add l rExpr ihl ihr =>
    simp only [checkExpr, bind, Except.bind] at hCheck
    cases hl : checkExpr Γ l with
    | error err => simp [hl] at hCheck
    | ok rl =>
      cases hr : checkExpr Γ rExpr with
      | error err => simp [hl, hr] at hCheck
      | ok rr =>
        simp only [hl, hr, pure, Except.pure, Except.ok.injEq] at hCheck
        subst hCheck
        obtain ⟨hlC, hlN⟩ := ihl hl
        obtain ⟨hrC, hrN⟩ := ihr hr
        exact ⟨rl.add_sound hlC hrC, ⟨hlN, hrN⟩⟩
  | sub l rExpr ihl ihr =>
    simp only [checkExpr, bind, Except.bind] at hCheck
    cases hl : checkExpr Γ l with
    | error err => simp [hl] at hCheck
    | ok rl =>
      cases hr : checkExpr Γ rExpr with
      | error err => simp [hl, hr] at hCheck
      | ok rr =>
        simp only [hl, hr, pure, Except.pure, Except.ok.injEq] at hCheck
        subst hCheck
        obtain ⟨hlC, hlN⟩ := ihl hl
        obtain ⟨hrC, hrN⟩ := ihr hr
        exact ⟨rl.sub_sound hlC hrC, ⟨hlN, hrN⟩⟩
  | mul l rExpr ihl ihr =>
    simp only [checkExpr, bind, Except.bind] at hCheck
    cases hl : checkExpr Γ l with
    | error err => simp [hl] at hCheck
    | ok rl =>
      cases hr : checkExpr Γ rExpr with
      | error err => simp [hl, hr] at hCheck
      | ok rr =>
        simp only [hl, hr, pure, Except.pure, Except.ok.injEq] at hCheck
        subst hCheck
        obtain ⟨hlC, hlN⟩ := ihl hl
        obtain ⟨hrC, hrN⟩ := ihr hr
        exact ⟨rl.mul_sound hlC hrC, ⟨hlN, hrN⟩⟩
  | neg inner ih =>
    simp only [checkExpr, bind, Except.bind] at hCheck
    cases hi : checkExpr Γ inner with
    | error err => simp [hi] at hCheck
    | ok ri =>
      simp only [hi, pure, Except.pure, Except.ok.injEq] at hCheck
      subst hCheck
      obtain ⟨hC, hN⟩ := ih hi
      exact ⟨ri.neg_sound hC, hN⟩
  | checkedCast target inner ih =>
    simp only [checkExpr, bind, Except.bind] at hCheck
    cases hi : checkExpr Γ inner with
    | error err => simp [hi] at hCheck
    | ok ri =>
      simp only [hi] at hCheck
      by_cases hFit : ri.fitsType target = true
      · simp only [hFit, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hCheck
        subst hCheck
        obtain ⟨hC, hN⟩ := ih hi
        exact ⟨hC, ⟨hN, ri.fitsType_sound hFit _ hC⟩⟩
      · simp [hFit] at hCheck
  | satCast target inner ih =>
    simp only [checkExpr, bind, Except.bind] at hCheck
    cases hi : checkExpr Γ inner with
    | error err => simp [hi] at hCheck
    | ok ri =>
      simp only [hi, pure, Except.pure, Except.ok.injEq] at hCheck
      subst hCheck
      obtain ⟨_, hN⟩ := ih hi
      exact ⟨(IntRange.ofType_contains_iff target _).mpr (clampToType_fits target _), hN⟩
  | wrapCast target inner ih =>
    simp only [checkExpr, bind, Except.bind] at hCheck
    cases hi : checkExpr Γ inner with
    | error err => simp [hi] at hCheck
    | ok ri =>
      simp only [hi, pure, Except.pure, Except.ok.injEq] at hCheck
      subst hCheck
      obtain ⟨_, hN⟩ := ih hi
      exact ⟨(IntRange.ofType_contains_iff target _).mpr (wrapToType_fits target _), hN⟩

theorem inferExprType_sound {Γ : Nat → Option IntRange} {ρ : Nat → Int}
    {e : IntExpr} {r : IntRange} {ty : IntegerType}
    (hEnv : EnvValid Γ ρ) (hInfer : inferExprType Γ e = .ok (r, ty)) :
    r.Contains (e.eval ρ) ∧
    e.NoOverflow ρ ∧
    ty.Fits (e.eval ρ) ∧
    (∀ other : IntegerType, (∀ x, r.Contains x → other.Fits x) → ty.bits ≤ other.bits) := by
  simp only [inferExprType, bind, Except.bind] at hInfer
  cases hCheck : checkExpr Γ e with
  | error err => simp [hCheck] at hInfer
  | ok range =>
    simp only [hCheck] at hInfer
    cases hTy : inferIntegerType range with
    | none => simp [hTy] at hInfer
    | some inferred =>
      simp only [hTy, Except.ok.injEq, Prod.mk.injEq] at hInfer
      obtain ⟨rfl, rfl⟩ := hInfer
      obtain ⟨hContains, hNoOv⟩ := checkExpr_sound hEnv hCheck
      exact ⟨hContains, hNoOv, inferIntegerType_fits hTy _ hContains,
        inferIntegerType_minimal hTy⟩

/-! ## Named Proved Examples & Overflow Counterexamples -/

private def envI7I7 : Nat → Option IntRange :=
  EnvValid.ofTypes fun
    | 0 | 1 => some (.signed .w7)
    | _ => none

theorem i7_add_infers_i8 :
    (inferExprType envI7I7 (.add (.var 0) (.var 1))).map Prod.snd = .ok (.signed .w8) := by
  rfl

private def envU3U4 : Nat → Option IntRange :=
  EnvValid.ofTypes fun
    | 0 => some (.unsigned .w3)
    | 1 => some (.unsigned .w4)
    | _ => none

theorem u3_mul_u4_infers_u7 :
    (inferExprType envU3U4 (.mul (.var 0) (.var 1))).map Prod.snd = .ok (.unsigned .w7) := by
  rfl

private def envU8U8 : Nat → Option IntRange :=
  EnvValid.ofTypes fun
    | 0 | 1 => some (.unsigned .w8)
    | _ => none

theorem u8_add_overflow_rejected :
    (checkExpr envU8U8 (.checkedCast (.unsigned .w8) (.add (.var 0) (.var 1)))) =
      .error (.potentialOverflow (.unsigned .w8) 0 510) := by
  rfl

theorem i7_sub_underflow_rejected :
    (checkExpr envI7I7 (.checkedCast (.signed .w7) (.sub (.var 0) (.var 1)))) =
      .error (.potentialOverflow (.signed .w7) (-127) 127) := by
  rfl

private def envGuardedU8 : Nat → Option IntRange
  | 0 => some ⟨0, 100, by decide⟩
  | 1 => some ⟨0, 150, by decide⟩
  | _ => none

theorem guarded_u8_add_accepted :
    checkExpr envGuardedU8 (.checkedCast (.unsigned .w8) (.add (.var 0) (.var 1))) =
      .ok ⟨0, 250, by decide⟩ := by
  rfl

theorem i24_natural_slot_aligned :
    TargetIntegerABI.natural.slot (.signed .w24) = ⟨4, 4⟩ := by
  decide

end Aethel.IntInference
