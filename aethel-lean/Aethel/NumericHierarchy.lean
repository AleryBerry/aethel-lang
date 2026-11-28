import Aethel.IntInference
import Aethel.CategoricalTraits

namespace Aethel.NumericHierarchy

open Aethel
open Aethel.IntInference
open Aethel.CategoricalTraits

/-!
## Lossless Numeric Widening, Field-Path Guards, & Algebraic Numeric Hierarchy

1. **Lossless Numeric Widening**: `NumericTy` (`intRange`, `f32`, `f64`) with
   independent semantic preservation predicate `LosslessWidens`, executable checker
   `checkLosslessWiden` (proved sound and complete), and least-upper-bound `joinNumericTy`.
2. **Field-Path Range Narrowing**: `FieldRangeEnv` tracking narrowed `IntRange`s on
   pure `root.field` paths under branch guards (`p.a < 2000`), updated on field writes
   and invalidated on whole-root mutation/borrows.
3. **Algebraic Numeric Trait Hierarchy**: `FromIntTrait`, `SemiringTrait` (with forgetful
   functors to `MonoidTrait`), `RingTrait`, `FieldTrait`, and verified `intRingTrait`.
-/

/-! ### Part 1: Lossless Numeric Widening -/

inductive NumericTy where
  | intRange (r : IntRange)
  | f32
  | f64
  deriving Repr, DecidableEq

/-- Exact IEEE-754 binary32 contiguous integer representability bound (`2^24`). -/
def f32ExactIntLimit : Int := 16777216

/-- Exact IEEE-754 binary64 contiguous integer representability bound (`2^53`). -/
def f64ExactIntLimit : Int := 9007199254740992

/-- Independent mathematical specification of lossless numeric widening. -/
def LosslessWidens : NumericTy → NumericTy → Prop
  | .intRange r1, .intRange r2 => ∀ v : Int, r1.Contains v → r2.Contains v
  | .intRange r1, .f32 => ∀ v : Int, r1.Contains v → -f32ExactIntLimit ≤ v ∧ v ≤ f32ExactIntLimit
  | .intRange r1, .f64 => ∀ v : Int, r1.Contains v → -f64ExactIntLimit ≤ v ∧ v ≤ f64ExactIntLimit
  | .f32, .f32 => True
  | .f32, .f64 => True
  | .f64, .f64 => True
  | _, _ => False

theorem LosslessWidens_refl (t : NumericTy) : LosslessWidens t t := by
  cases t with
  | intRange r => exact fun _ hv => hv
  | f32 => trivial
  | f64 => trivial

theorem LosslessWidens_trans {a b c : NumericTy}
    (hab : LosslessWidens a b) (hbc : LosslessWidens b c) : LosslessWidens a c := by
  cases a <;> cases b <;> cases c <;> simp only [LosslessWidens] at hab hbc ⊢
  · exact fun v hv => hbc v (hab v hv)
  · exact fun v hv => hbc v (hab v hv)
  · exact fun v hv => hbc v (hab v hv)
  · exact hab
  · exact fun v hv =>
      let ⟨h1, h2⟩ := hab v hv
      by unfold f32ExactIntLimit at h1 h2; unfold f64ExactIntLimit; omega
  · exact hab

/-- Executable checker for lossless numeric widening. -/
def checkLosslessWiden : NumericTy → NumericTy → Bool
  | .intRange r1, .intRange r2 => decide (r2.lo ≤ r1.lo ∧ r1.hi ≤ r2.hi)
  | .intRange r1, .f32 => decide (-f32ExactIntLimit ≤ r1.lo ∧ r1.hi ≤ f32ExactIntLimit)
  | .intRange r1, .f64 => decide (-f64ExactIntLimit ≤ r1.lo ∧ r1.hi ≤ f64ExactIntLimit)
  | .f32, .f32 => true
  | .f32, .f64 => true
  | .f64, .f64 => true
  | _, _ => false

theorem checkLosslessWiden_sound {src dst : NumericTy}
    (h : checkLosslessWiden src dst = true) : LosslessWidens src dst := by
  cases src <;> cases dst <;> simp only [checkLosslessWiden, LosslessWidens] at h ⊢
  · have ⟨hLo, hHi⟩ := of_decide_eq_true h
    intro v hv
    exact ⟨Int.le_trans hLo hv.1, Int.le_trans hv.2 hHi⟩
  · have ⟨hLo, hHi⟩ := of_decide_eq_true h
    intro v hv
    exact ⟨Int.le_trans hLo hv.1, Int.le_trans hv.2 hHi⟩
  · have ⟨hLo, hHi⟩ := of_decide_eq_true h
    intro v hv
    exact ⟨Int.le_trans hLo hv.1, Int.le_trans hv.2 hHi⟩
  · trivial
  · trivial
  · trivial
  all_goals contradiction

theorem checkLosslessWiden_complete {src dst : NumericTy}
    (h : LosslessWidens src dst) : checkLosslessWiden src dst = true := by
  cases src <;> cases dst <;> simp only [checkLosslessWiden, LosslessWidens] at h ⊢
  · exact decide_eq_true ⟨(h _ (IntRange.lo_mem _)).1, (h _ (IntRange.hi_mem _)).2⟩
  · exact decide_eq_true ⟨(h _ (IntRange.lo_mem _)).1, (h _ (IntRange.hi_mem _)).2⟩
  · exact decide_eq_true ⟨(h _ (IntRange.lo_mem _)).1, (h _ (IntRange.hi_mem _)).2⟩

/-- Least-upper-bound join of two numeric types under lossless widening. -/
def joinNumericTy : NumericTy → NumericTy → Option NumericTy
  | .intRange r1, .intRange r2 => some (.intRange (r1.join r2))
  | .f32, .f32 => some .f32
  | .f32, .f64 => some .f64
  | .f64, .f32 => some .f64
  | .f64, .f64 => some .f64
  | .f32, .intRange r =>
    if checkLosslessWiden (.intRange r) .f32 then some .f32
    else if checkLosslessWiden (.intRange r) .f64 then some .f64
    else none
  | .intRange r, .f32 =>
    if checkLosslessWiden (.intRange r) .f32 then some .f32
    else if checkLosslessWiden (.intRange r) .f64 then some .f64
    else none
  | .f64, .intRange r =>
    if checkLosslessWiden (.intRange r) .f64 then some .f64 else none
  | .intRange r, .f64 =>
    if checkLosslessWiden (.intRange r) .f64 then some .f64 else none

theorem joinNumericTy_sound {a b m : NumericTy}
    (h : joinNumericTy a b = some m) : LosslessWidens a m ∧ LosslessWidens b m := by
  cases a <;> cases b <;> simp only [joinNumericTy] at h
  · cases h
    exact ⟨fun _ hv => ⟨Int.le_trans (Int.min_le_left _ _) hv.1, Int.le_trans hv.2 (Int.le_max_left _ _)⟩,
           fun _ hv => ⟨Int.le_trans (Int.min_le_right _ _) hv.1, Int.le_trans hv.2 (Int.le_max_right _ _)⟩⟩
  · rename_i r
    by_cases h32 : checkLosslessWiden (.intRange r) .f32 = true
    · simp only [h32, ↓reduceIte, Option.some.injEq] at h
      subst m
      exact ⟨checkLosslessWiden_sound h32, trivial⟩
    · by_cases h64 : checkLosslessWiden (.intRange r) .f64 = true
      · simp only [h32, Bool.false_eq_true, ↓reduceIte, h64, Option.some.injEq] at h
        subst m
        exact ⟨checkLosslessWiden_sound h64, trivial⟩
      · simp [h32, h64] at h
  · rename_i r
    by_cases h64 : checkLosslessWiden (.intRange r) .f64 = true
    · simp only [h64, ↓reduceIte, Option.some.injEq] at h
      subst m
      exact ⟨checkLosslessWiden_sound h64, trivial⟩
    · simp [h64] at h
  · rename_i r
    by_cases h32 : checkLosslessWiden (.intRange r) .f32 = true
    · simp only [h32, ↓reduceIte, Option.some.injEq] at h
      subst m
      exact ⟨trivial, checkLosslessWiden_sound h32⟩
    · by_cases h64 : checkLosslessWiden (.intRange r) .f64 = true
      · simp only [h32, Bool.false_eq_true, ↓reduceIte, h64, Option.some.injEq] at h
        subst m
        exact ⟨trivial, checkLosslessWiden_sound h64⟩
      · simp [h32, h64] at h
  · cases h; exact ⟨trivial, trivial⟩
  · cases h; exact ⟨trivial, trivial⟩
  · rename_i r
    by_cases h64 : checkLosslessWiden (.intRange r) .f64 = true
    · simp only [h64, ↓reduceIte, Option.some.injEq] at h
      subst m
      exact ⟨trivial, checkLosslessWiden_sound h64⟩
    · simp [h64] at h
  · cases h; exact ⟨trivial, trivial⟩
  · cases h; exact ⟨trivial, trivial⟩

/-! #### Named Positive & Negative Widening Theorems -/

private def u8Type : IntegerType := .unsigned ⟨8, by decide, by decide⟩
private def u12Type : IntegerType := .unsigned ⟨12, by decide, by decide⟩
private def u16Type : IntegerType := .unsigned ⟨16, by decide, by decide⟩
private def u24Type : IntegerType := .unsigned ⟨24, by decide, by decide⟩
private def u25Type : IntegerType := .unsigned ⟨25, by decide, by decide⟩
private def u32Type : IntegerType := .unsigned ⟨32, by decide, by decide⟩
private def u54Type : IntegerType := .unsigned ⟨54, by decide, by decide⟩

theorem u8_to_u32_lossless :
    LosslessWidens (.intRange (IntRange.ofType u8Type)) (.intRange (IntRange.ofType u32Type)) :=
  checkLosslessWiden_sound (by decide)

theorem u16_to_f32_lossless :
    LosslessWidens (.intRange (IntRange.ofType u16Type)) .f32 :=
  checkLosslessWiden_sound (by decide)

theorem u24_to_f32_lossless :
    LosslessWidens (.intRange (IntRange.ofType u24Type)) .f32 :=
  checkLosslessWiden_sound (by decide)

theorem u25_to_f32_rejected :
    ¬ LosslessWidens (.intRange (IntRange.ofType u25Type)) .f32 := by
  intro h
  have hFalse : checkLosslessWiden (.intRange (IntRange.ofType u25Type)) .f32 = true :=
    checkLosslessWiden_complete h
  revert hFalse
  decide

theorem u32_to_f64_lossless :
    LosslessWidens (.intRange (IntRange.ofType u32Type)) .f64 :=
  checkLosslessWiden_sound (by decide)

theorem u54_to_f64_rejected :
    ¬ LosslessWidens (.intRange (IntRange.ofType u54Type)) .f64 := by
  intro h
  have hFalse : checkLosslessWiden (.intRange (IntRange.ofType u54Type)) .f64 = true :=
    checkLosslessWiden_complete h
  revert hFalse
  decide

theorem f32_to_f64_lossless : LosslessWidens .f32 .f64 := by
  trivial

theorem f64_to_f32_rejected : ¬ LosslessWidens .f64 .f32 := by
  intro h
  exact h

/-! ### Part 2: Field-Path Range Narrowing -/

abbrev FieldPathKey := String × String
abbrev FieldValuation := FieldPathKey → Int
abbrev FieldRangeEnv := List (FieldPathKey × IntRange)

def EnvSound (env : FieldRangeEnv) (val : FieldValuation) : Prop :=
  ∀ p r, (p, r) ∈ env → r.Contains (val p)

def lookupFieldRange (env : FieldRangeEnv) (p : FieldPathKey) : Option IntRange :=
  match env with
  | [] => none
  | (k, r) :: rest => if k == p then some r else lookupFieldRange rest p

theorem lookupFieldRange_sound {env : FieldRangeEnv} {val : FieldValuation}
    {p : FieldPathKey} {r : IntRange}
    (hEnv : EnvSound env val) (hFound : lookupFieldRange env p = some r) :
    r.Contains (val p) := by
  induction env with
  | nil => simp [lookupFieldRange] at hFound
  | cons entry rest ih =>
    obtain ⟨k, rk⟩ := entry
    simp only [lookupFieldRange] at hFound
    by_cases hk : k == p
    · simp only [hk, ↓reduceIte, Option.some.injEq] at hFound
      subst hFound
      have hp : k = p := beq_iff_eq.mp hk
      subst hp
      exact hEnv k rk (List.mem_cons_self ..)
    · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hFound
      exact ih (fun p' r' hm => hEnv p' r' (List.mem_cons_of_mem _ hm)) hFound

def setFieldRange (env : FieldRangeEnv) (p : FieldPathKey) (r : IntRange) : FieldRangeEnv :=
  (p, r) :: env.filter (fun entry => entry.1 != p)

theorem setFieldRange_sound {env : FieldRangeEnv} {val : FieldValuation}
    {p : FieldPathKey} {r : IntRange}
    (hEnv : EnvSound env val) (hVal : r.Contains (val p)) :
    EnvSound (setFieldRange env p r) val := by
  intro q rq hMem
  simp only [setFieldRange, List.mem_cons, List.mem_filter] at hMem
  rcases hMem with hEq | ⟨hOld, _⟩
  · cases hEq
    exact hVal
  · exact hEnv q rq hOld

def invalidateRoot (env : FieldRangeEnv) (root : String) : FieldRangeEnv :=
  env.filter (fun entry => entry.1.1 != root)

theorem invalidateRoot_sound {env : FieldRangeEnv} {val : FieldValuation} {root : String}
    (hEnv : EnvSound env val) :
    EnvSound (invalidateRoot env root) val := by
  intro q rq hMem
  simp only [invalidateRoot, List.mem_filter] at hMem
  exact hEnv q rq hMem.1

def narrowFieldLt (env : FieldRangeEnv) (p : FieldPathKey) (base : IntRange) (bound : Int) :
    Option FieldRangeEnv :=
  let cur := (lookupFieldRange env p).getD base
  (cur.narrowUpper? (bound - 1)).map (setFieldRange env p)

theorem narrowFieldLt_sound {env : FieldRangeEnv} {val : FieldValuation}
    {p : FieldPathKey} {base : IntRange} {bound : Int} {env' : FieldRangeEnv}
    (hEnv : EnvSound env val) (hBase : base.Contains (val p))
    (hGuard : val p < bound)
    (hNarrow : narrowFieldLt env p base bound = some env') :
    EnvSound env' val := by
  unfold narrowFieldLt at hNarrow
  simp only [Option.map_eq_some_iff] at hNarrow
  obtain ⟨r', hUpper, rfl⟩ := hNarrow
  have hCurContains : ((lookupFieldRange env p).getD base).Contains (val p) := by
    cases hLk : lookupFieldRange env p with
    | none => simpa [hLk] using hBase
    | some r => exact lookupFieldRange_sound hEnv hLk
  have hR' : r'.Contains (val p) :=
    IntRange.narrowUpper_sound hUpper hCurContains (by omega)
  exact setFieldRange_sound hEnv hR'

theorem guarded_u12_field_add_assign_accepted :
    ∃ rNarrow rSum : IntRange,
      (IntRange.ofType u12Type).narrowUpper? 1999 = some rNarrow ∧
      rSum = IntRange.add rNarrow (IntRange.singleton 24) ∧
      rSum.fitsType u12Type = true := by
  have hNarrow : (IntRange.ofType u12Type).narrowUpper? 1999 = some ⟨0, 1999, by decide⟩ := by
    decide
  refine ⟨⟨0, 1999, by decide⟩, IntRange.add ⟨0, 1999, by decide⟩ (IntRange.singleton 24), hNarrow, rfl, ?_⟩
  decide

theorem unguarded_u12_field_add_assign_rejected :
    (IntRange.add (IntRange.ofType u12Type) (IntRange.singleton 24)).fitsType u12Type = false := by
  decide

/-! ### Part 3: Algebraic Numeric Trait Hierarchy -/

structure FromIntTrait (α : Type) where
  fromInt : Int → α

structure SemiringTrait (α : Type) extends FromIntTrait α where
  zero : α
  one : α
  add : α → α → α
  mul : α → α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  zero_add : ∀ x : α, add zero x = x
  add_zero : ∀ x : α, add x zero = x
  add_comm : ∀ x y : α, add x y = add y x
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  one_mul : ∀ x : α, mul one x = x
  mul_one : ∀ x : α, mul x one = x
  left_distrib : ∀ x y z : α, mul x (add y z) = add (mul x y) (mul x z)
  right_distrib : ∀ x y z : α, mul (add x y) z = add (mul x z) (mul y z)
  zero_mul : ∀ x : α, mul zero x = zero
  mul_zero : ∀ x : α, mul x zero = zero

/-- Forgetful functor synthesizing an additive `MonoidTrait` from any `SemiringTrait`. -/
def SemiringTrait.toAddMonoid {α : Type} (s : SemiringTrait α) : MonoidTrait α where
  combine := s.add
  assoc := s.add_assoc
  empty := s.zero
  left_id := s.zero_add
  right_id := s.add_zero

/-- Forgetful functor synthesizing a multiplicative `MonoidTrait` from any `SemiringTrait`. -/
def SemiringTrait.toMulMonoid {α : Type} (s : SemiringTrait α) : MonoidTrait α where
  combine := s.mul
  assoc := s.mul_assoc
  empty := s.one
  left_id := s.one_mul
  right_id := s.mul_one

structure RingTrait (α : Type) extends SemiringTrait α where
  neg : α → α
  sub : α → α → α
  add_left_neg : ∀ x : α, add (neg x) x = zero
  sub_eq_add_neg : ∀ x y : α, sub x y = add x (neg y)

structure FieldTrait (α : Type) extends RingTrait α where
  mul_comm : ∀ x y : α, mul x y = mul y x
  inv : α → α
  div : α → α → α
  zero_ne_one : zero ≠ one
  mul_inv_cancel : ∀ x : α, x ≠ zero → mul x (inv x) = one
  div_eq_mul_inv : ∀ x y : α, div x y = mul x (inv y)

def intRingTrait : RingTrait Int where
  fromInt := id
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  add_comm := Int.add_comm
  mul_assoc := Int.mul_assoc
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  neg := (- ·)
  sub := (· - ·)
  add_left_neg := Int.add_left_neg
  sub_eq_add_neg := fun _ _ => Int.sub_eq_add_neg

theorem intRing_fromInt_add (a b : Int) :
    intRingTrait.fromInt (a + b) = intRingTrait.add (intRingTrait.fromInt a) (intRingTrait.fromInt b) :=
  rfl

theorem intRing_fromInt_mul (a b : Int) :
    intRingTrait.fromInt (a * b) = intRingTrait.mul (intRingTrait.fromInt a) (intRingTrait.fromInt b) :=
  rfl

end Aethel.NumericHierarchy
