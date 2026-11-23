import Std

namespace Aethel.LawAutoProver

/-!
## Tier 2 — Automated Symbolic Decision & Proof Synthesis Engine

Translates quantitative and relational constitutional laws over natural numbers into a
checked AST, normalizes expressions into canonical multi-variable linear forms, proves
equalities/inequalities/implications structurally, and searches for symbolic counterexamples.
-/

inductive LawExpr where
  | var (id : Nat)
  | const (n : Nat)
  | add (a b : LawExpr)
  | sub (a b : LawExpr)
  | mulConst (c : Nat) (e : LawExpr)
  | min (a b : LawExpr)
  | max (a b : LawExpr)
  deriving Repr, DecidableEq

inductive LawProp where
  | tt
  | ff
  | eq (a b : LawExpr)
  | ne (a b : LawExpr)
  | le (a b : LawExpr)
  | lt (a b : LawExpr)
  | not (p : LawProp)
  | and (p q : LawProp)
  | or (p q : LawProp)
  | imp (p q : LawProp)
  deriving Repr, DecidableEq

def LawExpr.eval (env : Nat → Nat) : LawExpr → Nat
  | .var id => env id
  | .const n => n
  | .add a b => a.eval env + b.eval env
  | .sub a b => a.eval env - b.eval env
  | .mulConst c e => c * e.eval env
  | .min a b => Nat.min (a.eval env) (b.eval env)
  | .max a b => Nat.max (a.eval env) (b.eval env)

/-- Independent mathematical semantics of symbolic constitutional laws. -/
def LawProp.Holds (env : Nat → Nat) : LawProp → Prop
  | .tt => True
  | .ff => False
  | .eq a b => a.eval env = b.eval env
  | .ne a b => a.eval env ≠ b.eval env
  | .le a b => a.eval env ≤ b.eval env
  | .lt a b => a.eval env < b.eval env
  | .not p => ¬ p.Holds env
  | .and p q => p.Holds env ∧ q.Holds env
  | .or p q => p.Holds env ∨ q.Holds env
  | .imp p q => p.Holds env → q.Holds env

def LawProp.evalBool (env : Nat → Nat) : LawProp → Bool
  | .tt => true
  | .ff => false
  | .eq a b => decide (a.eval env = b.eval env)
  | .ne a b => decide (a.eval env ≠ b.eval env)
  | .le a b => decide (a.eval env ≤ b.eval env)
  | .lt a b => decide (a.eval env < b.eval env)
  | .not p => !p.evalBool env
  | .and p q => p.evalBool env && q.evalBool env
  | .or p q => p.evalBool env || q.evalBool env
  | .imp p q => !p.evalBool env || q.evalBool env

theorem LawProp.evalBool_eq_true_iff (env : Nat → Nat) (p : LawProp) :
    p.evalBool env = true ↔ p.Holds env := by
  induction p with
  | tt => simp [evalBool, Holds]
  | ff => simp [evalBool, Holds]
  | eq a b => simp [evalBool, Holds]
  | ne a b => simp [evalBool, Holds]
  | le a b => simp [evalBool, Holds]
  | lt a b => simp [evalBool, Holds]
  | not p ih => simp only [evalBool, Holds, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, ih]
  | and p q ihp ihq => simp [evalBool, Holds, ihp, ihq]
  | or p q ihp ihq => simp [evalBool, Holds, ihp, ihq]
  | imp p q ihp ihq =>
    simp only [evalBool, Holds, Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff,
      ne_eq, ihp, ihq]
    by_cases hp : p.Holds env <;> simp [hp]

theorem LawProp.evalBool_eq_false_iff (env : Nat → Nat) (p : LawProp) :
    p.evalBool env = false ↔ ¬ p.Holds env := by
  rw [Bool.eq_false_iff, ne_eq, LawProp.evalBool_eq_true_iff]

/-- Canonical multi-variable linear form `const + Σ (c_i * x_{v_i})` sorted by `v_i`. -/
structure LinearForm where
  const : Nat
  terms : List (Nat × Nat)
  deriving Repr, DecidableEq

def evalTerms (env : Nat → Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (v, c) :: rest => c * env v + evalTerms env rest

def LinearForm.eval (env : Nat → Nat) (lf : LinearForm) : Nat :=
  lf.const + evalTerms env lf.terms

def insertTerm (v : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, xs => xs
  | c + 1, [] => [(v, c + 1)]
  | c + 1, (v', c') :: rest =>
    if v < v' then (v, c + 1) :: (v', c') :: rest
    else if v = v' then (v', (c + 1) + c') :: rest
    else (v', c') :: insertTerm v (c + 1) rest

theorem evalTerms_insertTerm (env : Nat → Nat) (v c : Nat) (xs : List (Nat × Nat)) :
    evalTerms env (insertTerm v c xs) = c * env v + evalTerms env xs := by
  cases c with
  | zero => simp [insertTerm]
  | succ c =>
    induction xs with
    | nil => simp [insertTerm, evalTerms]
    | cons p rest ih =>
      obtain ⟨v', c'⟩ := p
      dsimp [insertTerm]
      by_cases hLt : v < v'
      · simp [hLt, evalTerms]
      · by_cases hEq : v = v'
        · subst hEq
          simp only [hLt, ↓reduceIte, evalTerms]
          rw [Nat.add_mul]
          omega
        · simp only [hLt, hEq, ↓reduceIte, evalTerms]
          rw [ih]
          omega

def mergeTerms : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | [], ys => ys
  | (v, c) :: xs, ys => mergeTerms xs (insertTerm v c ys)

theorem evalTerms_mergeTerms (env : Nat → Nat) (xs ys : List (Nat × Nat)) :
    evalTerms env (mergeTerms xs ys) = evalTerms env xs + evalTerms env ys := by
  induction xs generalizing ys with
  | nil => simp [mergeTerms, evalTerms]
  | cons p xs ih =>
    obtain ⟨v, c⟩ := p
    simp only [mergeTerms, ih, evalTerms_insertTerm, evalTerms]
    omega

def scaleTerms : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, _ => []
  | _, [] => []
  | c + 1, (v, k) :: rest => (v, (c + 1) * k) :: scaleTerms (c + 1) rest

theorem evalTerms_scaleTerms (env : Nat → Nat) (c : Nat) (xs : List (Nat × Nat)) :
    evalTerms env (scaleTerms c xs) = c * evalTerms env xs := by
  cases c with
  | zero => simp [scaleTerms, evalTerms]
  | succ c =>
    induction xs with
    | nil => simp [scaleTerms, evalTerms]
    | cons p rest ih =>
      obtain ⟨v, k⟩ := p
      simp only [scaleTerms, evalTerms, ih, Nat.mul_add, Nat.mul_assoc]

def LinearForm.add (a b : LinearForm) : LinearForm :=
  ⟨a.const + b.const, mergeTerms a.terms b.terms⟩

def LinearForm.scale (c : Nat) (lf : LinearForm) : LinearForm :=
  ⟨c * lf.const, scaleTerms c lf.terms⟩

def LawExpr.toLinear : LawExpr → Option LinearForm
  | .const n => some ⟨n, []⟩
  | .var v => some ⟨0, [(v, 1)]⟩
  | .add a b => do
    let la ← a.toLinear
    let lb ← b.toLinear
    return la.add lb
  | .mulConst 0 _ => some ⟨0, []⟩
  | .mulConst c e => (e.toLinear).map (·.scale c)
  | _ => none

theorem LawExpr.toLinear_sound (env : Nat → Nat) {e : LawExpr} {lf : LinearForm}
    (hLin : e.toLinear = some lf) :
    lf.eval env = e.eval env := by
  induction e generalizing lf with
  | const n =>
    simp only [toLinear, Option.some.injEq] at hLin
    subst hLin
    simp [LinearForm.eval, evalTerms, eval]
  | var v =>
    simp only [toLinear, Option.some.injEq] at hLin
    subst hLin
    simp [LinearForm.eval, evalTerms, eval]
  | add a b iha ihb =>
    simp only [toLinear, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hLin
    obtain ⟨la, ha, lb, hb, rfl⟩ := hLin
    simp only [LinearForm.eval, LinearForm.add, evalTerms_mergeTerms, eval]
    have haE := iha ha
    have hbE := ihb hb
    simp only [LinearForm.eval] at haE hbE
    omega
  | mulConst c e ihe =>
    cases c with
    | zero =>
      simp only [toLinear, Option.some.injEq] at hLin
      subst hLin
      simp [LinearForm.eval, evalTerms, eval]
    | succ c =>
      simp only [toLinear, Option.map_eq_some_iff] at hLin
      obtain ⟨le, hle, rfl⟩ := hLin
      simp only [LinearForm.eval, LinearForm.scale, evalTerms_scaleTerms, eval]
      have hE := ihe hle
      simp only [LinearForm.eval] at hE
      rw [← hE, Nat.mul_add]
  | sub _ _ => cases hLin
  | min _ _ => cases hLin
  | max _ _ => cases hLin

/-- Structural comparison on sorted `Nat × Nat` coefficient lists: verifies pointwise
term-by-term dominance `xs ≤ ys` while structurally decreasing on `ys`. -/
def termsSubLe (xs : List (Nat × Nat)) : List (Nat × Nat) → Bool
  | [] => xs.isEmpty
  | (v2, c2) :: ys' =>
    match xs with
    | [] => true
    | (v1, c1) :: xs' =>
      if v1 == v2 then decide (c1 ≤ c2) && termsSubLe xs' ys'
      else if v2 < v1 then termsSubLe xs ys'
      else false

theorem termsSubLe_sound (env : Nat → Nat) (xs ys : List (Nat × Nat))
    (h : termsSubLe xs ys = true) :
    evalTerms env xs ≤ evalTerms env ys := by
  induction ys generalizing xs with
  | nil =>
    cases xs with
    | nil => simp [evalTerms]
    | cons _ _ => simp [termsSubLe] at h
  | cons p2 ys' ih =>
    obtain ⟨v2, c2⟩ := p2
    cases xs with
    | nil => simp [evalTerms]
    | cons p1 xs' =>
      obtain ⟨v1, c1⟩ := p1
      dsimp [termsSubLe] at h
      by_cases hEq : v1 = v2
      · subst hEq
        simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
        have hRest := ih xs' h.2
        have hCoeff : c1 * env v1 ≤ c2 * env v1 := Nat.mul_le_mul_right (env v1) h.1
        simp only [evalTerms]
        omega
      · have hBeqFalse : (v1 == v2) = false := beq_false_of_ne hEq
        simp only [hBeqFalse, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hLt : v2 < v1
        · simp only [hLt, ↓reduceIte] at h
          have hRest := ih ((v1, c1) :: xs') h
          simp only [evalTerms] at hRest ⊢
          omega
        · simp only [hLt, ↓reduceIte] at h
          cases h

private def normAdd (x y : LawExpr) : LawExpr :=
  match x, y with
  | .const a, .const b => .const (a + b)
  | .const 0, b => b
  | a, .const 0 => a
  | a, b => .add a b

private theorem normAdd_eval (env : Nat → Nat) (x y : LawExpr) :
    (normAdd x y).eval env = x.eval env + y.eval env := by
  cases x with
  | const a =>
    cases a <;> cases y <;> simp [normAdd, LawExpr.eval]
  | _ =>
    cases y with
    | const b => cases b <;> simp [normAdd, LawExpr.eval]
    | _ => rfl

private def normSub (x y : LawExpr) : LawExpr :=
  if x == y then .const 0
  else match x, y with
  | .const a, .const b => .const (a - b)
  | .const 0, _ => .const 0
  | a, .const 0 => a
  | a, b => .sub a b

private theorem normSub_eval (env : Nat → Nat) (x y : LawExpr) :
    (normSub x y).eval env = x.eval env - y.eval env := by
  dsimp [normSub]
  by_cases hEq : (x == y) = true
  · have hEq' := beq_iff_eq.mp hEq
    subst hEq'
    simp [LawExpr.eval]
  · simp only [hEq]
    cases x with
    | const a =>
      cases y with
      | const b => rfl
      | _ => cases a <;> simp [LawExpr.eval]
    | _ =>
      cases y with
      | const b => cases b <;> simp [LawExpr.eval]
      | _ => rfl

private def normMul (c : Nat) (x : LawExpr) : LawExpr :=
  match c, x with
  | 0, _ => .const 0
  | 1, a => a
  | k, .const n => .const (k * n)
  | k, a => .mulConst k a

private theorem normMul_eval (env : Nat → Nat) (c : Nat) (x : LawExpr) :
    (normMul c x).eval env = c * x.eval env := by
  cases c with
  | zero => simp [normMul, LawExpr.eval]
  | succ c =>
    cases c with
    | zero => simp [normMul]
    | succ c =>
      cases x <;> simp [normMul, LawExpr.eval]

private def normMin (x y : LawExpr) : LawExpr :=
  if x == y then x
  else match x, y with
  | .const a, .const b => .const (Nat.min a b)
  | a, b => .min a b

private theorem normMin_eval (env : Nat → Nat) (x y : LawExpr) :
    (normMin x y).eval env = Nat.min (x.eval env) (y.eval env) := by
  dsimp [normMin]
  by_cases hEq : (x == y) = true
  · have hEq' := beq_iff_eq.mp hEq
    subst hEq'
    simp
  · simp only [hEq]
    cases x <;> cases y <;> rfl

private def normMax (x y : LawExpr) : LawExpr :=
  if x == y then x
  else match x, y with
  | .const a, .const b => .const (Nat.max a b)
  | a, b => .max a b

private theorem normMax_eval (env : Nat → Nat) (x y : LawExpr) :
    (normMax x y).eval env = Nat.max (x.eval env) (y.eval env) := by
  dsimp [normMax]
  by_cases hEq : (x == y) = true
  · have hEq' := beq_iff_eq.mp hEq
    subst hEq'
    simp
  · simp only [hEq]
    cases x <;> cases y <;> rfl

def normalizeExpr : LawExpr → LawExpr
  | .var id => .var id
  | .const n => .const n
  | .add a b => normAdd (normalizeExpr a) (normalizeExpr b)
  | .sub a b => normSub (normalizeExpr a) (normalizeExpr b)
  | .mulConst c e => normMul c (normalizeExpr e)
  | .min a b => normMin (normalizeExpr a) (normalizeExpr b)
  | .max a b => normMax (normalizeExpr a) (normalizeExpr b)

theorem normalizeExpr_sound (env : Nat → Nat) (e : LawExpr) :
    (normalizeExpr e).eval env = e.eval env := by
  induction e with
  | var _ => rfl
  | const _ => rfl
  | add a b iha ihb => simp [normalizeExpr, normAdd_eval, LawExpr.eval, iha, ihb]
  | sub a b iha ihb => simp [normalizeExpr, normSub_eval, LawExpr.eval, iha, ihb]
  | mulConst c e ihe => simp [normalizeExpr, normMul_eval, LawExpr.eval, ihe]
  | min a b iha ihb => simp [normalizeExpr, normMin_eval, LawExpr.eval, iha, ihb]
  | max a b iha ihb => simp [normalizeExpr, normMax_eval, LawExpr.eval, iha, ihb]

def hypImpliesLe (a b : LawExpr) : LawProp → Bool
  | .le x y => x == a && y == b
  | .lt x y => x == a && y == b
  | .eq x y => (x == a && y == b) || (y == a && x == b)
  | _ => false

theorem hypImpliesLe_sound (env : Nat → Nat) {a b : LawExpr} {h : LawProp}
    (hMatch : hypImpliesLe a b h = true) (hHolds : h.Holds env) :
    a.eval env ≤ b.eval env := by
  cases h with
  | le x y =>
    simp only [hypImpliesLe, Bool.and_eq_true, beq_iff_eq] at hMatch
    rcases hMatch with ⟨rfl, rfl⟩
    exact hHolds
  | lt x y =>
    simp only [hypImpliesLe, Bool.and_eq_true, beq_iff_eq] at hMatch
    rcases hMatch with ⟨rfl, rfl⟩
    exact Nat.le_of_lt hHolds
  | eq x y =>
    simp only [hypImpliesLe, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hMatch
    rcases hMatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Nat.le_of_eq hHolds
    · exact Nat.le_of_eq hHolds.symm
  | _ => cases hMatch

def linearLe (a b : LawExpr) : Bool :=
  match a.toLinear, b.toLinear with
  | some la, some lb => decide (la.const ≤ lb.const) && termsSubLe la.terms lb.terms
  | _, _ => false

theorem linearLe_sound (env : Nat → Nat) {a b : LawExpr}
    (hLin : linearLe a b = true) :
    a.eval env ≤ b.eval env := by
  dsimp [linearLe] at hLin
  cases ha : a.toLinear with
  | none => simp [ha] at hLin
  | some la =>
    cases hb : b.toLinear with
    | none => simp [ha, hb] at hLin
    | some lb =>
      simp only [ha, hb, Bool.and_eq_true, decide_eq_true_eq] at hLin
      have haE := LawExpr.toLinear_sound env ha
      have hbE := LawExpr.toLinear_sound env hb
      have hTerms := termsSubLe_sound env la.terms lb.terms hLin.2
      simp only [LinearForm.eval] at haE hbE
      omega

def hypImpliesEq (a b : LawExpr) : LawProp → Bool
  | .eq x y => (x == a && y == b) || (y == a && x == b)
  | _ => false

theorem hypImpliesEq_sound (env : Nat → Nat) {a b : LawExpr} {h : LawProp}
    (hMatch : hypImpliesEq a b h = true) (hHolds : h.Holds env) :
    a.eval env = b.eval env := by
  cases h with
  | eq x y =>
    simp only [hypImpliesEq, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hMatch
    rcases hMatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hHolds
    · exact hHolds.symm
  | _ => cases hMatch

def linearEq (a b : LawExpr) : Bool :=
  match a.toLinear, b.toLinear with
  | some la, some lb => la == lb
  | _, _ => false

theorem linearEq_sound (env : Nat → Nat) {a b : LawExpr}
    (hLin : linearEq a b = true) :
    a.eval env = b.eval env := by
  dsimp [linearEq] at hLin
  cases ha : a.toLinear with
  | none => simp [ha] at hLin
  | some la =>
    cases hb : b.toLinear with
    | none => simp [ha, hb] at hLin
    | some lb =>
      simp only [ha, hb, beq_iff_eq] at hLin
      subst hLin
      exact (LawExpr.toLinear_sound env ha).symm.trans (LawExpr.toLinear_sound env hb)

def hypImpliesLt (a b : LawExpr) : LawProp → Bool
  | .lt x y => x == a && y == b
  | _ => false

theorem hypImpliesLt_sound (env : Nat → Nat) {a b : LawExpr} {h : LawProp}
    (hMatch : hypImpliesLt a b h = true) (hHolds : h.Holds env) :
    a.eval env < b.eval env := by
  cases h with
  | lt x y =>
    simp only [hypImpliesLt, Bool.and_eq_true, beq_iff_eq] at hMatch
    rcases hMatch with ⟨rfl, rfl⟩
    exact hHolds
  | _ => cases hMatch

def linearLt (a b : LawExpr) : Bool :=
  match a.toLinear, b.toLinear with
  | some la, some lb => decide (la.const < lb.const) && termsSubLe la.terms lb.terms
  | _, _ => false

theorem linearLt_sound (env : Nat → Nat) {a b : LawExpr}
    (hLin : linearLt a b = true) :
    a.eval env < b.eval env := by
  dsimp [linearLt] at hLin
  cases ha : a.toLinear with
  | none => simp [ha] at hLin
  | some la =>
    cases hb : b.toLinear with
    | none => simp [ha, hb] at hLin
    | some lb =>
      simp only [ha, hb, Bool.and_eq_true, decide_eq_true_eq] at hLin
      have haE := LawExpr.toLinear_sound env ha
      have hbE := LawExpr.toLinear_sound env hb
      have hTerms := termsSubLe_sound env la.terms lb.terms hLin.2
      simp only [LinearForm.eval] at haE hbE
      omega

private def isZeroConst : LawExpr → Bool
  | .const 0 => true
  | _ => false

def proveLe (hyps : List LawProp) : Nat → LawExpr → LawExpr → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    (a == b) ||
    isZeroConst a ||
    hyps.any (hypImpliesLe a b) ||
    linearLe a b ||
    (match a with | .sub x _ => proveLe hyps fuel x b | _ => false) ||
    (match a with | .min x y => proveLe hyps fuel x b || proveLe hyps fuel y b | _ => false) ||
    (match b with | .max x y => proveLe hyps fuel a x || proveLe hyps fuel a y | _ => false) ||
    (match a with | .max x y => proveLe hyps fuel x b && proveLe hyps fuel y b | _ => false) ||
    (match b with | .min x y => proveLe hyps fuel a x && proveLe hyps fuel a y | _ => false) ||
    (match a, b with
      | .add x1 x2, .add y1 y2 =>
        (proveLe hyps fuel x1 y1 && proveLe hyps fuel x2 y2) ||
        (proveLe hyps fuel x1 y2 && proveLe hyps fuel x2 y1)
      | _, _ => false) ||
    (match b with | .add y1 y2 => proveLe hyps fuel a y1 || proveLe hyps fuel a y2 | _ => false) ||
    (match a with
      | .add l r =>
        (match l with | .sub x y => r == y && proveLe hyps fuel y x && proveLe hyps fuel x b | _ => false) ||
        (match r with | .sub x y => l == y && proveLe hyps fuel y x && proveLe hyps fuel x b | _ => false)
      | _ => false) ||
    (match b with
      | .add l r =>
        (match l with | .sub x y => r == y && proveLe hyps fuel y x && proveLe hyps fuel a x | _ => false) ||
        (match r with | .sub x y => l == y && proveLe hyps fuel y x && proveLe hyps fuel a x | _ => false)
      | _ => false)

theorem proveLe_sound {hyps : List LawProp} {fuel : Nat} {a b : LawExpr}
    (hPrv : proveLe hyps fuel a b = true)
    (env : Nat → Nat) (hHyps : ∀ h ∈ hyps, h.Holds env) :
    a.eval env ≤ b.eval env := by
  induction fuel generalizing a b with
  | zero => cases hPrv
  | succ f ih =>
    dsimp [proveLe] at hPrv
    simp only [Bool.or_eq_true] at hPrv
    rcases hPrv with (((((((((((hEq | hZ) | hAny) | hLin) | hSub) | hMinL) | hMaxR) | hMaxL) | hMinR) | hAddM) | hWeak) | hSubAddL) | hSubAddR
    · have hSame := beq_iff_eq.mp hEq
      subst hSame
      exact Nat.le_refl _
    · cases a with
      | const n =>
        cases n with
        | zero => simp [LawExpr.eval]
        | succ _ => simp [isZeroConst] at hZ
      | _ => cases hZ
    · obtain ⟨h, hhMem, hhMatch⟩ := List.any_eq_true.mp hAny
      exact hypImpliesLe_sound env hhMatch (hHyps h hhMem)
    · exact linearLe_sound env hLin
    · cases a with
      | sub x y =>
        have hLe := ih hSub
        dsimp [LawExpr.eval]
        omega
      | _ => cases hSub
    · cases a with
      | min x y =>
        rcases Bool.or_eq_true_iff.mp hMinL with hX | hY
        · exact Nat.le_trans (Nat.min_le_left _ _) (ih hX)
        · exact Nat.le_trans (Nat.min_le_right _ _) (ih hY)
      | _ => cases hMinL
    · cases b with
      | max x y =>
        rcases Bool.or_eq_true_iff.mp hMaxR with hX | hY
        · exact Nat.le_trans (ih hX) (Nat.le_max_left _ _)
        · exact Nat.le_trans (ih hY) (Nat.le_max_right _ _)
      | _ => cases hMaxR
    · cases a with
      | max x y =>
        simp only [Bool.and_eq_true] at hMaxL
        exact Nat.max_le.mpr ⟨ih hMaxL.1, ih hMaxL.2⟩
      | _ => cases hMaxL
    · cases b with
      | min x y =>
        simp only [Bool.and_eq_true] at hMinR
        exact Nat.le_min.mpr ⟨ih hMinR.1, ih hMinR.2⟩
      | _ => cases hMinR
    · cases a <;> cases b <;> try cases hAddM
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hAddM
      dsimp [LawExpr.eval]
      rcases hAddM with ⟨h11, h22⟩ | ⟨h12, h21⟩
      · have := ih h11; have := ih h22; omega
      · have := ih h12; have := ih h21; omega
    · cases b with
      | add y1 y2 =>
        rcases Bool.or_eq_true_iff.mp hWeak with hY1 | hY2
        · have := ih hY1; dsimp [LawExpr.eval]; omega
        · have := ih hY2; dsimp [LawExpr.eval]; omega
      | _ => cases hWeak
    · cases a with
      | add l r =>
        rcases Bool.or_eq_true_iff.mp hSubAddL with hL | hR
        · cases l with
          | sub x y =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hL
            rcases hL with ⟨⟨rfl, hYx⟩, hXb⟩
            have := ih hYx; have := ih hXb
            dsimp [LawExpr.eval]
            omega
          | _ => cases hL
        · cases r with
          | sub x y =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hR
            rcases hR with ⟨⟨rfl, hYx⟩, hXb⟩
            have := ih hYx; have := ih hXb
            dsimp [LawExpr.eval]
            omega
          | _ => cases hR
      | _ => cases hSubAddL
    · cases b with
      | add l r =>
        rcases Bool.or_eq_true_iff.mp hSubAddR with hL | hR
        · cases l with
          | sub x y =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hL
            rcases hL with ⟨⟨rfl, hYx⟩, hAx⟩
            have := ih hYx; have := ih hAx
            dsimp [LawExpr.eval]
            omega
          | _ => cases hL
        · cases r with
          | sub x y =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hR
            rcases hR with ⟨⟨rfl, hYx⟩, hAx⟩
            have := ih hYx; have := ih hAx
            dsimp [LawExpr.eval]
            omega
          | _ => cases hR
      | _ => cases hSubAddR

def proveEq (hyps : List LawProp) : Nat → LawExpr → LawExpr → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    (a == b) ||
    hyps.any (hypImpliesEq a b) ||
    linearEq a b ||
    (match a with
      | .add l r =>
        (match l with | .sub x y => r == y && proveLe hyps fuel y x && proveEq hyps fuel x b | _ => false) ||
        (match r with | .sub x y => l == y && proveLe hyps fuel y x && proveEq hyps fuel x b | _ => false)
      | _ => false) ||
    (match b with
      | .add l r =>
        (match l with | .sub x y => r == y && proveLe hyps fuel y x && proveEq hyps fuel a x | _ => false) ||
        (match r with | .sub x y => l == y && proveLe hyps fuel y x && proveEq hyps fuel a x | _ => false)
      | _ => false) ||
    (proveLe hyps fuel a b && proveLe hyps fuel b a)

theorem proveEq_sound {hyps : List LawProp} {fuel : Nat} {a b : LawExpr}
    (hPrv : proveEq hyps fuel a b = true)
    (env : Nat → Nat) (hHyps : ∀ h ∈ hyps, h.Holds env) :
    a.eval env = b.eval env := by
  induction fuel generalizing a b with
  | zero => cases hPrv
  | succ f ih =>
    dsimp [proveEq] at hPrv
    simp only [Bool.or_eq_true] at hPrv
    rcases hPrv with ((((hEq | hAny) | hLin) | hSubL) | hSubR) | hAnti
    · have hSame := beq_iff_eq.mp hEq
      subst hSame
      rfl
    · obtain ⟨h, hhMem, hhMatch⟩ := List.any_eq_true.mp hAny
      exact hypImpliesEq_sound env hhMatch (hHyps h hhMem)
    · exact linearEq_sound env hLin
    · cases a with
      | add l r =>
        rcases Bool.or_eq_true_iff.mp hSubL with hL | hR
        · cases l with
          | sub x y =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hL
            rcases hL with ⟨⟨rfl, hYx⟩, hXb⟩
            have hLe := proveLe_sound hYx env hHyps
            have hRec := ih hXb
            dsimp [LawExpr.eval]
            omega
          | _ => cases hL
        · cases r with
          | sub x y =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hR
            rcases hR with ⟨⟨rfl, hYx⟩, hXb⟩
            have hLe := proveLe_sound hYx env hHyps
            have hRec := ih hXb
            dsimp [LawExpr.eval]
            omega
          | _ => cases hR
      | _ => cases hSubL
    · cases b with
      | add l r =>
        rcases Bool.or_eq_true_iff.mp hSubR with hL | hR
        · cases l with
          | sub x y =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hL
            rcases hL with ⟨⟨rfl, hYx⟩, hAx⟩
            have hLe := proveLe_sound hYx env hHyps
            have hRec := ih hAx
            dsimp [LawExpr.eval]
            omega
          | _ => cases hL
        · cases r with
          | sub x y =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hR
            rcases hR with ⟨⟨rfl, hYx⟩, hAx⟩
            have hLe := proveLe_sound hYx env hHyps
            have hRec := ih hAx
            dsimp [LawExpr.eval]
            omega
          | _ => cases hR
      | _ => cases hSubR
    · simp only [Bool.and_eq_true] at hAnti
      exact Nat.le_antisymm (proveLe_sound hAnti.1 env hHyps) (proveLe_sound hAnti.2 env hHyps)

def proveLt (hyps : List LawProp) : Nat → LawExpr → LawExpr → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    if hyps.any (hypImpliesLt a b) then true
    else if linearLt a b then true
    else proveLe hyps fuel (.add a (.const 1)) b

theorem proveLt_sound {hyps : List LawProp} {fuel : Nat} {a b : LawExpr}
    (hPrv : proveLt hyps fuel a b = true)
    (env : Nat → Nat) (hHyps : ∀ h ∈ hyps, h.Holds env) :
    a.eval env < b.eval env := by
  cases fuel with
  | zero => cases hPrv
  | succ f =>
    dsimp [proveLt] at hPrv
    split at hPrv
    · next hAny =>
      obtain ⟨h, hhMem, hhMatch⟩ := List.any_eq_true.mp hAny
      exact hypImpliesLt_sound env hhMatch (hHyps h hhMem)
    split at hPrv
    · next hLin =>
      exact linearLt_sound env hLin
    · have hLe := proveLe_sound hPrv env hHyps
      dsimp [LawExpr.eval] at hLe
      omega

def flattenHyp : LawProp → List LawProp
  | .tt => []
  | .and p q => flattenHyp p ++ flattenHyp q
  | .not (.lt a b) => [.le (normalizeExpr b) (normalizeExpr a)]
  | .not (.le a b) => [.lt (normalizeExpr b) (normalizeExpr a)]
  | .not (.not p) => flattenHyp p
  | .eq a b => [.eq (normalizeExpr a) (normalizeExpr b)]
  | .le a b => [.le (normalizeExpr a) (normalizeExpr b)]
  | .lt a b => [.lt (normalizeExpr a) (normalizeExpr b)]
  | .ne a b => [.ne (normalizeExpr a) (normalizeExpr b)]
  | p => [p]

theorem flattenHyp_sound (env : Nat → Nat) (p : LawProp) (hp : p.Holds env) :
    ∀ q ∈ flattenHyp p, q.Holds env := by
  match p with
  | .tt =>
    intro _ hq
    cases hq
  | .and p1 p2 =>
    intro q hq
    simp only [flattenHyp, List.mem_append] at hq
    rcases hq with h1 | h2
    · exact flattenHyp_sound env p1 hp.1 q h1
    · exact flattenHyp_sound env p2 hp.2 q h2
  | .not (.lt a b) =>
    intro q hq
    simp only [flattenHyp, List.mem_singleton] at hq
    subst hq
    dsimp [LawProp.Holds] at hp ⊢
    rw [normalizeExpr_sound, normalizeExpr_sound]
    omega
  | .not (.le a b) =>
    intro q hq
    simp only [flattenHyp, List.mem_singleton] at hq
    subst hq
    dsimp [LawProp.Holds] at hp ⊢
    rw [normalizeExpr_sound, normalizeExpr_sound]
    omega
  | .not (.not p1) =>
    intro q hq
    exact flattenHyp_sound env p1 (Classical.not_not.mp hp) q hq
  | .eq a b =>
    intro q hq
    simp only [flattenHyp, List.mem_singleton] at hq
    subst hq
    dsimp [LawProp.Holds] at hp ⊢
    rw [normalizeExpr_sound, normalizeExpr_sound]
    exact hp
  | .le a b =>
    intro q hq
    simp only [flattenHyp, List.mem_singleton] at hq
    subst hq
    dsimp [LawProp.Holds] at hp ⊢
    rw [normalizeExpr_sound, normalizeExpr_sound]
    exact hp
  | .lt a b =>
    intro q hq
    simp only [flattenHyp, List.mem_singleton] at hq
    subst hq
    dsimp [LawProp.Holds] at hp ⊢
    rw [normalizeExpr_sound, normalizeExpr_sound]
    exact hp
  | .ne a b =>
    intro q hq
    simp only [flattenHyp, List.mem_singleton] at hq
    subst hq
    dsimp [LawProp.Holds] at hp ⊢
    rw [normalizeExpr_sound, normalizeExpr_sound]
    exact hp
  | .ff => exact False.elim hp
  | .or _ _ =>
    intro q hq
    simp only [flattenHyp, List.mem_singleton] at hq
    subst hq
    exact hp
  | .imp _ _ =>
    intro q hq
    simp only [flattenHyp, List.mem_singleton] at hq
    subst hq
    exact hp
  | .not .tt => exact False.elim (hp trivial)
  | .not .ff =>
    intro q hq
    simp only [flattenHyp, List.mem_singleton] at hq
    subst hq
    exact hp
  | .not (.eq _ _) =>
    intro q hq
    simp only [flattenHyp, List.mem_singleton] at hq
    subst hq
    exact hp
  | .not (.ne _ _) =>
    intro q hq
    simp only [flattenHyp, List.mem_singleton] at hq
    subst hq
    exact hp
  | .not (.and _ _) =>
    intro q hq
    simp only [flattenHyp, List.mem_singleton] at hq
    subst hq
    exact hp
  | .not (.or _ _) =>
    intro q hq
    simp only [flattenHyp, List.mem_singleton] at hq
    subst hq
    exact hp
  | .not (.imp _ _) =>
    intro q hq
    simp only [flattenHyp, List.mem_singleton] at hq
    subst hq
    exact hp

def hypImpliesNe (a b : LawExpr) : LawProp → Bool
  | .ne x y => (x == a && y == b) || (y == a && x == b)
  | _ => false

theorem hypImpliesNe_sound (env : Nat → Nat) {a b : LawExpr} {h : LawProp}
    (hMatch : hypImpliesNe a b h = true) (hHolds : h.Holds env) :
    a.eval env ≠ b.eval env := by
  cases h with
  | ne x y =>
    simp only [hypImpliesNe, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hMatch
    rcases hMatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hHolds
    · exact hHolds.symm
  | _ => cases hMatch

def autoProve (hyps : List LawProp) : Nat → LawProp → Bool
  | 0, _ => false
  | fuel + 1, goal =>
    match goal with
    | .tt => true
    | .ff => hyps.any fun h => match h with | .ff => true | _ => false
    | .eq a b => proveEq hyps fuel (normalizeExpr a) (normalizeExpr b)
    | .ne a b =>
      let a' := normalizeExpr a
      let b' := normalizeExpr b
      proveLt hyps fuel a' b' || proveLt hyps fuel b' a' || hyps.any (hypImpliesNe a' b')
    | .le a b => proveLe hyps fuel (normalizeExpr a) (normalizeExpr b)
    | .lt a b => proveLt hyps fuel (normalizeExpr a) (normalizeExpr b)
    | .not (.lt a b) => proveLe hyps fuel (normalizeExpr b) (normalizeExpr a)
    | .not (.le a b) => proveLt hyps fuel (normalizeExpr b) (normalizeExpr a)
    | .not (.eq a b) => autoProve hyps fuel (.ne a b)
    | .not (.ne a b) => autoProve hyps fuel (.eq a b)
    | .not .ff => true
    | .not (.not p) => autoProve hyps fuel p
    | .not _ => false
    | .and p q => autoProve hyps fuel p && autoProve hyps fuel q
    | .or p q => autoProve hyps fuel p || autoProve hyps fuel q
    | .imp p q => autoProve (flattenHyp p ++ hyps) fuel q

theorem autoProve_sound {hyps : List LawProp} {fuel : Nat} {goal : LawProp}
    (hPrv : autoProve hyps fuel goal = true) :
    ∀ env, (∀ h ∈ hyps, h.Holds env) → goal.Holds env := by
  induction fuel generalizing hyps goal with
  | zero => cases hPrv
  | succ f ih =>
    intro env hHyps
    dsimp [autoProve] at hPrv
    cases goal with
    | tt => trivial
    | ff =>
      obtain ⟨h, hhMem, hhMatch⟩ := List.any_eq_true.mp hPrv
      cases h with
      | ff => exact hHyps .ff hhMem
      | _ => cases hhMatch
    | eq a b =>
      have hEq := proveEq_sound hPrv env hHyps
      dsimp [LawProp.Holds]
      rw [normalizeExpr_sound, normalizeExpr_sound] at hEq
      exact hEq
    | ne a b =>
      simp only [Bool.or_eq_true] at hPrv
      dsimp [LawProp.Holds]
      rcases hPrv with (hLt1 | hLt2) | hAny
      · have hL := proveLt_sound hLt1 env hHyps
        rw [normalizeExpr_sound, normalizeExpr_sound] at hL
        omega
      · have hL := proveLt_sound hLt2 env hHyps
        rw [normalizeExpr_sound, normalizeExpr_sound] at hL
        omega
      · obtain ⟨h, hhMem, hhMatch⟩ := List.any_eq_true.mp hAny
        have hN := hypImpliesNe_sound env hhMatch (hHyps h hhMem)
        rw [normalizeExpr_sound, normalizeExpr_sound] at hN
        exact hN
    | le a b =>
      have hLe := proveLe_sound hPrv env hHyps
      dsimp [LawProp.Holds]
      rw [normalizeExpr_sound, normalizeExpr_sound] at hLe
      exact hLe
    | lt a b =>
      have hLt := proveLt_sound hPrv env hHyps
      dsimp [LawProp.Holds]
      rw [normalizeExpr_sound, normalizeExpr_sound] at hLt
      exact hLt
    | not sub =>
      cases sub with
      | lt a b =>
        have hLe := proveLe_sound hPrv env hHyps
        dsimp [LawProp.Holds]
        rw [normalizeExpr_sound, normalizeExpr_sound] at hLe
        omega
      | le a b =>
        have hLt := proveLt_sound hPrv env hHyps
        dsimp [LawProp.Holds]
        rw [normalizeExpr_sound, normalizeExpr_sound] at hLt
        omega
      | eq a b => exact ih hPrv env hHyps
      | ne a b =>
        intro hNeg
        exact hNeg (ih hPrv env hHyps)
      | ff => exact id
      | not p =>
        intro hNeg
        exact hNeg (ih hPrv env hHyps)
      | tt => cases hPrv
      | and _ _ => cases hPrv
      | or _ _ => cases hPrv
      | imp _ _ => cases hPrv
    | and p q =>
      simp only [Bool.and_eq_true] at hPrv
      exact ⟨ih hPrv.1 env hHyps, ih hPrv.2 env hHyps⟩
    | or p q =>
      simp only [Bool.or_eq_true] at hPrv
      rcases hPrv with hP | hQ
      · exact Or.inl (ih hP env hHyps)
      · exact Or.inr (ih hQ env hHyps)
    | imp p q =>
      intro hp
      apply ih hPrv env
      intro h hh
      simp only [List.mem_append] at hh
      rcases hh with hFlat | hOrig
      · exact flattenHyp_sound env p hp h hFlat
      · exact hHyps h hOrig

/-- Normalizing front-end entry point for `autoProve`: flattens initial hypotheses once. -/
def autoProveNorm (hyps : List LawProp) (fuel : Nat) (goal : LawProp) : Bool :=
  autoProve (hyps.flatMap flattenHyp) fuel goal

theorem autoProveNorm_sound {hyps : List LawProp} {fuel : Nat} {goal : LawProp}
    (hPrv : autoProveNorm hyps fuel goal = true) :
    ∀ env, (∀ h ∈ hyps, h.Holds env) → goal.Holds env := by
  intro env hHyps
  apply autoProve_sound hPrv env
  intro h hh
  simp only [List.mem_flatMap] at hh
  obtain ⟨orig, hOrig, hFlat⟩ := hh
  exact flattenHyp_sound env orig (hHyps orig hOrig) h hFlat

def mkEnv3 (v0 v1 v2 : Nat) : Nat → Nat
  | 0 => v0
  | 1 => v1
  | 2 => v2
  | _ => 0

def falsifySymbolic (bound : Nat) (hyps : List LawProp) (goal : LawProp) :
    Option (Nat × Nat × Nat) :=
  let rng := List.range bound
  let triples := rng.flatMap fun v0 => rng.flatMap fun v1 => rng.map fun v2 => (v0, v1, v2)
  triples.find? fun (v0, v1, v2) =>
    let env := mkEnv3 v0 v1 v2
    hyps.all (·.evalBool env) && !goal.evalBool env

theorem falsifySymbolic_sound {bound : Nat} {hyps : List LawProp} {goal : LawProp}
    {v0 v1 v2 : Nat} (hFound : falsifySymbolic bound hyps goal = some (v0, v1, v2)) :
    ¬ (∀ env : Nat → Nat, (∀ h ∈ hyps, h.Holds env) → goal.Holds env) := by
  intro hAll
  have hPred := List.find?_some hFound
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hPred
  have hHyps : ∀ h ∈ hyps, h.Holds (mkEnv3 v0 v1 v2) := fun h hh =>
    (LawProp.evalBool_eq_true_iff _ _).mp (hPred.1 h hh)
  have hGoal := hAll (mkEnv3 v0 v1 v2) hHyps
  have hBoolTrue := (LawProp.evalBool_eq_true_iff (mkEnv3 v0 v1 v2) goal).mpr hGoal
  rw [hBoolTrue] at hPred
  cases hPred.2

/-! ## Concrete Unbounded Symbolic Law Witnesses -/

def exprBoundedDamage : LawProp :=
  .not (.lt (.var 0) (.sub (.var 0) (.var 1)))

def exprDamageRecovery : LawProp :=
  .imp (.le (.var 1) (.var 0)) (.eq (.add (.sub (.var 0) (.var 1)) (.var 1)) (.var 0))

def exprAddComm : LawProp :=
  .eq (.add (.var 0) (.var 1)) (.add (.var 1) (.var 0))

def exprMinLeAdd : LawProp :=
  .le (.min (.var 0) (.var 1)) (.add (.var 0) (.var 2))

def exprBuggyDamage : LawProp :=
  .not (.lt (.var 0) (.add (.var 0) (.var 1)))

theorem law_bounded_damage_proved : ∀ hp dmg : Nat, ¬ (hp < hp - dmg) := by
  intro hp dmg
  let env : Nat → Nat | 0 => hp | _ => dmg
  exact autoProveNorm_sound (hyps := []) (fuel := 12) (goal := exprBoundedDamage)
    (by decide) env (fun _ h => by cases h)

theorem law_damage_recovery_proved : ∀ hp dmg : Nat, dmg ≤ hp → (hp - dmg) + dmg = hp := by
  intro hp dmg hLe
  let env : Nat → Nat | 0 => hp | _ => dmg
  exact autoProveNorm_sound (hyps := []) (fuel := 12) (goal := exprDamageRecovery)
    (by decide) env (fun _ h => by cases h) hLe

theorem law_add_comm_proved : ∀ x y : Nat, x + y = y + x := by
  intro x y
  let env : Nat → Nat | 0 => x | _ => y
  exact autoProveNorm_sound (hyps := []) (fuel := 12) (goal := exprAddComm)
    (by decide) env (fun _ h => by cases h)

theorem law_min_le_add_proved : ∀ a b c : Nat, Nat.min a b ≤ a + c := by
  intro a b c
  let env : Nat → Nat | 0 => a | 1 => b | _ => c
  exact autoProveNorm_sound (hyps := []) (fuel := 12) (goal := exprMinLeAdd)
    (by decide) env (fun _ h => by cases h)

theorem law_buggy_damage_falsified : ¬ (∀ hp dmg : Nat, ¬ (hp < hp + dmg)) := by
  intro hAll
  have hFal : ¬ (∀ env : Nat → Nat, (∀ h ∈ ([] : List LawProp), h.Holds env) → exprBuggyDamage.Holds env) :=
    falsifySymbolic_sound (bound := 4) (hyps := []) (goal := exprBuggyDamage) (v0 := 0) (v1 := 1) (v2 := 0)
      (by decide)
  apply hFal
  intro env _
  exact hAll (env 0) (env 1)

end Aethel.LawAutoProver
