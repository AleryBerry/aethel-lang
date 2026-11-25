import Std

namespace Aethel

/-- Variables denote captured/SSA value identities, not mutable source names. -/
inductive IdxExpr where
  | const (n : Nat)
  | value (id : Nat)
  | add (left right : IdxExpr)
  deriving Repr, DecidableEq

def IdxExpr.eval (ν : Nat → Nat) : IdxExpr → Nat
  | .const n => n
  | .value id => ν id
  | .add a b => a.eval ν + b.eval ν

structure FactEnv where
  unequal : List (IdxExpr × IdxExpr) := []
  deriving Repr

def FactEnv.Valid (Δ : FactEnv) (ν : Nat → Nat) : Prop :=
  ∀ a b, (a, b) ∈ Δ.unequal → a.eval ν ≠ b.eval ν

def FactEnv.provesNe (Δ : FactEnv) (a b : IdxExpr) : Bool :=
  match a, b with
  | .const x, .const y => decide (x ≠ y)
  | _, _ => decide ((a, b) ∈ Δ.unequal ∨ (b, a) ∈ Δ.unequal)

theorem FactEnv.provesNe_sound {Δ : FactEnv} {ν : Nat → Nat} {a b : IdxExpr}
    (hΔ : Δ.Valid ν) (h : Δ.provesNe a b = true) :
    a.eval ν ≠ b.eval ν := by
  cases a <;> cases b <;> simp_all [FactEnv.provesNe, IdxExpr.eval, FactEnv.Valid]
  all_goals rcases h with h | h
  all_goals first | exact hΔ _ _ h | exact Ne.symm (hΔ _ _ h)

def FactEnv.assumeNe (Δ : FactEnv) (a b : IdxExpr) : FactEnv :=
  ⟨(a, b) :: Δ.unequal⟩

theorem FactEnv.assumeNe_valid {Δ : FactEnv} {ν : Nat → Nat} {a b : IdxExpr}
    (hΔ : Δ.Valid ν) (hab : a.eval ν ≠ b.eval ν) :
    (Δ.assumeNe a b).Valid ν := by
  intro x y h
  simp only [assumeNe, List.mem_cons, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | h
  · exact hab
  · exact hΔ _ _ h

/-- A merge retains only facts common to both incoming environments. -/
def FactEnv.join (a b : FactEnv) : FactEnv :=
  ⟨a.unequal.filter fun fact => decide (fact ∈ b.unequal)⟩

theorem FactEnv.join_valid_left {a b : FactEnv} {ν : Nat → Nat} (h : a.Valid ν) :
    (a.join b).Valid ν := by
  intro x y hm
  exact h x y (List.mem_filter.mp hm).1

theorem FactEnv.join_valid_right {a b : FactEnv} {ν : Nat → Nat} (h : b.Valid ν) :
    (a.join b).Valid ν := by
  intro x y hm
  exact h x y (of_decide_eq_true (List.mem_filter.mp hm).2)

/-- Half-open intervals, including empty intervals. -/
structure Interval where
  lo : Nat
  hi : Nat
  deriving Repr, DecidableEq

def Interval.Contains (s : Interval) (i : Nat) : Prop := s.lo ≤ i ∧ i < s.hi

def Interval.disjoint (a b : Interval) : Bool :=
  decide (a.hi ≤ b.lo ∨ b.hi ≤ a.lo ∨ a.hi ≤ a.lo ∨ b.hi ≤ b.lo)

theorem Interval.disjoint_sound {a b : Interval} {i : Nat} (h : a.disjoint b = true) :
    ¬ (a.Contains i ∧ b.Contains i) := by
  simp only [disjoint, decide_eq_true_eq] at h
  simp only [Contains]
  omega

theorem Interval.disjoint_correct (a b : Interval) :
    a.disjoint b = true ↔ ∀ i, ¬ (a.Contains i ∧ b.Contains i) := by
  constructor
  · intro checked _
    exact Interval.disjoint_sound checked
  · intro separate
    by_cases checked : a.disjoint b = true
    · exact checked
    · simp only [disjoint, decide_eq_true_eq] at checked
      exact False.elim (separate (max a.lo b.lo) (by
        simp only [Contains]
        omega))

end Aethel
