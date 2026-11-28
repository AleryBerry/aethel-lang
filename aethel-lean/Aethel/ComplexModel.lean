import Aethel.NumericHierarchy

namespace Aethel.ComplexModel

open Aethel.NumericHierarchy

/-!
## Complex Numbers over Commutative Rings and Anisotropic Fields

1. `Complex α` with componentwise addition/subtraction, bilinear multiplication,
   conjugation, and squared norm over any commutative `RingTrait α`.
2. `Complex.ringTrait`, `Complex.mul_comm`, `Complex.i_sq_eq_neg_one`,
   `Complex.conj_involutive`, `Complex.conj_add`, `Complex.conj_mul`, and
   `Complex.mul_conj_eq_normSq`.
3. `Complex.fieldTrait` over any anisotropic `FieldTrait α` (`a² + b² = 0 → a = 0 ∧ b = 0`),
   plus counterexample `f2_complex_has_zero_divisor` over `𝔽₂` (`Bool`) showing why the
   anisotropic condition is required.
-/

@[ext]
structure Complex (α : Type) where
  re : α
  im : α
  deriving Repr, DecidableEq

namespace Complex

/-! ### Helper Ring Lemmas -/

section RingHelpers

variable {α : Type} (R : RingTrait α)

private theorem add_right_neg (x : α) : R.add x (R.neg x) = R.zero := by
  rw [R.add_comm, R.add_left_neg]

private theorem add_left_cancel {a b c : α} (h : R.add a b = R.add a c) : b = c := by
  have h1 : R.add (R.neg a) (R.add a b) = R.add (R.neg a) (R.add a c) := by rw [h]
  rw [← R.add_assoc, ← R.add_assoc, R.add_left_neg, R.zero_add, R.zero_add] at h1
  exact h1

private theorem neg_eq_of_add_eq_zero {a b : α} (h : R.add a b = R.zero) : R.neg a = b := by
  apply add_left_cancel R (a := a)
  rw [add_right_neg R, h]

private theorem neg_zero : R.neg R.zero = R.zero :=
  neg_eq_of_add_eq_zero R (R.zero_add R.zero)

private theorem neg_neg (x : α) : R.neg (R.neg x) = x :=
  neg_eq_of_add_eq_zero R (R.add_left_neg x)

private theorem neg_add (x y : α) : R.neg (R.add x y) = R.add (R.neg x) (R.neg y) := by
  apply neg_eq_of_add_eq_zero R
  calc
    R.add (R.add x y) (R.add (R.neg x) (R.neg y))
      = R.add (R.add x (R.add y (R.neg y))) (R.neg x) := by
          rw [R.add_assoc, R.add_assoc, R.add_comm (R.neg x) (R.neg y), ← R.add_assoc y (R.neg y)]
    _ = R.add x (R.neg x) := by rw [add_right_neg R, R.add_zero]
    _ = R.zero := add_right_neg R x

private theorem mul_neg (x y : α) : R.mul x (R.neg y) = R.neg (R.mul x y) := by
  symm
  apply neg_eq_of_add_eq_zero R
  rw [← R.left_distrib, add_right_neg R, R.mul_zero]

private theorem neg_mul (x y : α) : R.mul (R.neg x) y = R.neg (R.mul x y) := by
  symm
  apply neg_eq_of_add_eq_zero R
  rw [← R.right_distrib, add_right_neg R, R.zero_mul]

private theorem add4_swap23 (a b c d : α) :
    R.add (R.add a b) (R.add c d) = R.add (R.add a c) (R.add b d) := by
  rw [R.add_assoc a b, ← R.add_assoc b c d, R.add_comm b c, R.add_assoc c b d, ← R.add_assoc a c]

private theorem add_sub_neg_assoc (a b c d : α) :
    R.add (R.add a (R.neg b)) (R.neg (R.add c d)) =
      R.add (R.add a (R.neg c)) (R.neg (R.add b d)) := by
  rw [neg_add R, neg_add R, add4_swap23 R]

private theorem add_sub_swap_inner (a b c d : α) :
    R.add a (R.neg (R.add b (R.add c (R.neg d)))) =
      R.add (R.add a d) (R.neg (R.add b c)) := by
  rw [neg_add R, neg_add R, neg_neg R, R.add_comm (R.neg c) d,
    ← R.add_assoc (R.neg b) d (R.neg c), R.add_comm (R.neg b) d,
    R.add_assoc d (R.neg b) (R.neg c), ← R.add_assoc a d, ← neg_add R]

/-! ### Complex Ring Operations & Laws -/

def zero : Complex α := ⟨R.zero, R.zero⟩
def one : Complex α := ⟨R.one, R.zero⟩
def iUnit : Complex α := ⟨R.zero, R.one⟩
def fromInt (n : Int) : Complex α := ⟨R.fromInt n, R.zero⟩

def add (z w : Complex α) : Complex α := ⟨R.add z.re w.re, R.add z.im w.im⟩
def neg (z : Complex α) : Complex α := ⟨R.neg z.re, R.neg z.im⟩
def sub (z w : Complex α) : Complex α := ⟨R.sub z.re w.re, R.sub z.im w.im⟩

def mul (z w : Complex α) : Complex α :=
  ⟨R.sub (R.mul z.re w.re) (R.mul z.im w.im),
   R.add (R.mul z.re w.im) (R.mul z.im w.re)⟩

def conj (z : Complex α) : Complex α := ⟨z.re, R.neg z.im⟩

def normSq (z : Complex α) : α := R.add (R.mul z.re z.re) (R.mul z.im z.im)

theorem add_assoc_law (x y z : Complex α) :
    add R (add R x y) z = add R x (add R y z) := by
  ext <;> simp [add, R.add_assoc]

theorem zero_add_law (x : Complex α) : add R (zero R) x = x := by
  ext <;> simp [add, zero, R.zero_add]

theorem add_zero_law (x : Complex α) : add R x (zero R) = x := by
  ext <;> simp [add, zero, R.add_zero]

theorem add_comm_law (x y : Complex α) : add R x y = add R y x := by
  ext <;> simp [add, R.add_comm]

theorem one_mul_law (x : Complex α) : mul R (one R) x = x := by
  ext <;> simp [mul, one, R.one_mul, R.zero_mul, R.sub_eq_add_neg, neg_zero R, R.add_zero]

theorem mul_one_law (x : Complex α) : mul R x (one R) = x := by
  ext <;> simp [mul, one, R.mul_one, R.mul_zero, R.sub_eq_add_neg, neg_zero R, R.add_zero, R.zero_add]

theorem zero_mul_law (x : Complex α) : mul R (zero R) x = zero R := by
  ext <;> simp [mul, zero, R.zero_mul, R.sub_eq_add_neg, neg_zero R, R.add_zero]

theorem mul_zero_law (x : Complex α) : mul R x (zero R) = zero R := by
  ext <;> simp [mul, zero, R.mul_zero, R.sub_eq_add_neg, neg_zero R, R.add_zero]

theorem add_left_neg_law (x : Complex α) : add R (neg R x) x = zero R := by
  ext <;> simp [add, neg, zero, R.add_left_neg]

theorem sub_eq_add_neg_law (x y : Complex α) : sub R x y = add R x (neg R y) := by
  ext <;> simp [sub, add, neg, R.sub_eq_add_neg]

theorem mul_assoc_law (x y z : Complex α) :
    mul R (mul R x y) z = mul R x (mul R y z) := by
  ext
  · simp only [mul, R.sub_eq_add_neg, R.left_distrib, R.right_distrib, R.mul_assoc,
      mul_neg R, neg_mul R]
    rw [add_sub_neg_assoc R, R.add_comm (R.mul x.im (R.mul y.re z.im)) (R.mul x.im (R.mul y.im z.re))]
  · simp only [mul, R.sub_eq_add_neg, R.left_distrib, R.right_distrib, R.mul_assoc,
      mul_neg R, neg_mul R]
    rw [add4_swap23 R, R.add_comm (R.neg (R.mul x.im (R.mul y.im z.im))) (R.mul x.im (R.mul y.re z.re))]

theorem left_distrib_law (x y z : Complex α) :
    mul R x (add R y z) = add R (mul R x y) (mul R x z) := by
  ext
  · simp only [mul, add, R.sub_eq_add_neg, R.left_distrib, neg_add R]
    rw [R.add_assoc, R.add_comm (R.mul x.re z.re) (R.add (R.neg (R.mul x.im y.im)) (R.neg (R.mul x.im z.im))),
      R.add_assoc, R.add_comm (R.neg (R.mul x.im z.im)) (R.mul x.re z.re), ← R.add_assoc, ← R.add_assoc]
  · simp only [mul, add, R.left_distrib]
    rw [R.add_assoc, R.add_comm (R.mul x.re z.im) (R.add (R.mul x.im y.re) (R.mul x.im z.re)),
      R.add_assoc, R.add_comm (R.mul x.im z.re) (R.mul x.re z.im), ← R.add_assoc, ← R.add_assoc]

theorem right_distrib_law (x y z : Complex α) :
    mul R (add R x y) z = add R (mul R x z) (mul R y z) := by
  ext
  · simp only [mul, add, R.sub_eq_add_neg, R.right_distrib, neg_add R]
    rw [R.add_assoc, R.add_comm (R.mul y.re z.re) (R.add (R.neg (R.mul x.im z.im)) (R.neg (R.mul y.im z.im))),
      R.add_assoc, R.add_comm (R.neg (R.mul y.im z.im)) (R.mul y.re z.re), ← R.add_assoc, ← R.add_assoc]
  · simp only [mul, add, R.right_distrib]
    rw [R.add_assoc, R.add_comm (R.mul y.re z.im) (R.add (R.mul x.im z.re) (R.mul y.im z.re)),
      R.add_assoc, R.add_comm (R.mul y.im z.re) (R.mul y.re z.im), ← R.add_assoc, ← R.add_assoc]

def ringTrait : RingTrait (Complex α) where
  fromInt := fromInt R
  zero := zero R
  one := one R
  add := add R
  mul := mul R
  add_assoc := add_assoc_law R
  zero_add := zero_add_law R
  add_zero := add_zero_law R
  add_comm := add_comm_law R
  mul_assoc := mul_assoc_law R
  one_mul := one_mul_law R
  mul_one := mul_one_law R
  left_distrib := left_distrib_law R
  right_distrib := right_distrib_law R
  zero_mul := zero_mul_law R
  mul_zero := mul_zero_law R
  neg := neg R
  sub := sub R
  add_left_neg := add_left_neg_law R
  sub_eq_add_neg := sub_eq_add_neg_law R

theorem mul_comm_law (hComm : ∀ x y : α, R.mul x y = R.mul y x) (x y : Complex α) :
    mul R x y = mul R y x := by
  ext
  · simp [mul, hComm]
  · simp [mul, hComm, R.add_comm]

theorem i_sq_eq_neg_one : mul R (iUnit R) (iUnit R) = neg R (one R) := by
  ext <;> simp [mul, iUnit, one, neg, R.zero_mul, R.mul_zero, R.one_mul, R.sub_eq_add_neg, R.zero_add, neg_zero R]

theorem conj_involutive (z : Complex α) : conj R (conj R z) = z := by
  ext <;> simp [conj, neg_neg R]

theorem conj_add (z w : Complex α) : conj R (add R z w) = add R (conj R z) (conj R w) := by
  ext <;> simp [conj, add, neg_add R]

theorem conj_mul (z w : Complex α) : conj R (mul R z w) = mul R (conj R z) (conj R w) := by
  ext
  · simp [conj, mul, R.sub_eq_add_neg, neg_mul R, mul_neg R, neg_neg R]
  · simp [conj, mul, neg_add R, mul_neg R, neg_mul R]

theorem mul_conj_eq_normSq (hComm : ∀ x y : α, R.mul x y = R.mul y x) (z : Complex α) :
    mul R z (conj R z) = ⟨normSq R z, R.zero⟩ := by
  ext
  · simp [mul, conj, normSq, R.sub_eq_add_neg, mul_neg R, neg_neg R]
  · simp [mul, conj, mul_neg R, hComm z.re z.im, R.add_left_neg]

end RingHelpers

/-! ### Complex Field over Anisotropic Fields -/

section FieldHelpers

variable {α : Type} (F : FieldTrait α)

private theorem field_mul_one_inv (x : α) (hx : x ≠ F.zero) : F.mul (F.inv x) x = F.one := by
  rw [F.mul_comm, F.mul_inv_cancel x hx]

private theorem field_div_self (x : α) (hx : x ≠ F.zero) : F.div x x = F.one := by
  rw [F.div_eq_mul_inv, F.mul_inv_cancel x hx]

def inv (z : Complex α) : Complex α :=
  let d := normSq F.toRingTrait z
  ⟨F.div z.re d, F.div (F.neg z.im) d⟩

def div (z w : Complex α) : Complex α :=
  mul F.toRingTrait z (inv F w)

theorem zero_ne_one_law : zero F.toRingTrait ≠ one F.toRingTrait := by
  intro h
  have hRe : F.zero = F.one := congrArg Complex.re h
  exact F.zero_ne_one hRe

theorem mul_inv_cancel_law
    (hAniso : ∀ a b : α, F.add (F.mul a a) (F.mul b b) = F.zero → a = F.zero ∧ b = F.zero)
    (z : Complex α) (hz : z ≠ zero F.toRingTrait) :
    mul F.toRingTrait z (inv F z) = one F.toRingTrait := by
  let R := F.toRingTrait
  let d := normSq R z
  have hdNe : d ≠ F.zero := by
    intro hdZero
    have hPair := hAniso z.re z.im hdZero
    apply hz
    ext
    · exact hPair.1
    · exact hPair.2
  ext
  · simp only [mul, inv, one, normSq, F.sub_eq_add_neg, F.div_eq_mul_inv]
    rw [← F.mul_assoc z.re z.re, ← F.mul_assoc z.im (F.neg z.im)]
    rw [mul_neg F.toRingTrait, neg_mul F.toRingTrait, neg_neg F.toRingTrait]
    rw [← F.right_distrib]
    exact F.mul_inv_cancel _ hdNe
  · simp only [mul, inv, one, normSq, F.div_eq_mul_inv]
    rw [← F.mul_assoc z.re (F.neg z.im), ← F.mul_assoc z.im z.re]
    rw [mul_neg F.toRingTrait, F.mul_comm z.im z.re, ← F.right_distrib, F.add_left_neg, F.zero_mul]

def fieldTrait
    (hAniso : ∀ a b : α, F.add (F.mul a a) (F.mul b b) = F.zero → a = F.zero ∧ b = F.zero) :
    FieldTrait (Complex α) where
  toRingTrait := ringTrait F.toRingTrait
  mul_comm := mul_comm_law F.toRingTrait F.mul_comm
  inv := inv F
  div := div F
  zero_ne_one := zero_ne_one_law F
  mul_inv_cancel := mul_inv_cancel_law F hAniso
  div_eq_mul_inv := fun _ _ => rfl

end FieldHelpers

/-! ### Negative Counterexample: `𝔽₂` (`Bool`) is not anisotropic, so `Complex(𝔽₂)` has zero divisors -/

private def boolFieldTrait : FieldTrait Bool where
  fromInt n := n % 2 != 0
  zero := false
  one := true
  add := xor
  mul := and
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  left_distrib := by decide
  right_distrib := by decide
  zero_mul := by decide
  mul_zero := by decide
  neg := id
  sub := xor
  add_left_neg := by decide
  sub_eq_add_neg := by decide
  mul_comm := by decide
  inv := id
  div := and
  zero_ne_one := by decide
  mul_inv_cancel := by decide
  div_eq_mul_inv := by decide

theorem f2_complex_has_zero_divisor :
    let z : Complex Bool := ⟨true, true⟩
    z ≠ zero boolFieldTrait.toRingTrait ∧
    mul boolFieldTrait.toRingTrait z z = zero boolFieldTrait.toRingTrait := by
  decide

end Complex

end Aethel.ComplexModel
