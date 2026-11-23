import Aethel.Disjointness

namespace Aethel

inductive PathStep where
  | field (id : Nat)
  | index (expr : IdxExpr)
  deriving Repr, DecidableEq

inductive ConcreteStep where
  | field (id : Nat)
  | index (value : Nat)
  deriving Repr, DecidableEq

def PathStep.resolve (ν : Nat → Nat) : PathStep → ConcreteStep
  | .field f => .field f
  | .index i => .index (i.eval ν)

def stepsDisjoint (Δ : FactEnv) : PathStep → PathStep → Bool
  | .field a, .field b => decide (a ≠ b)
  | .index a, .index b => Δ.provesNe a b
  | _, _ => false

theorem stepsDisjoint_sound {Δ : FactEnv} {ν : Nat → Nat} {a b : PathStep}
    (hΔ : Δ.Valid ν) (h : stepsDisjoint Δ a b = true) :
    a.resolve ν ≠ b.resolve ν := by
  cases a <;> cases b <;> simp_all [stepsDisjoint, PathStep.resolve]
  exact FactEnv.provesNe_sound hΔ h

/-- A prefix overlaps its descendants; disjointness needs a differing step. -/
def pathsDisjoint (Δ : FactEnv) : List PathStep → List PathStep → Bool
  | a :: as, b :: bs => stepsDisjoint Δ a b ||
      (decide (a = b) && pathsDisjoint Δ as bs)
  | _, _ => false

def resolvePath (ν : Nat → Nat) (p : List PathStep) : List ConcreteStep :=
  p.map (PathStep.resolve ν)

/-- Concrete prefix relation, used to account for parent/descendant overlap. -/
def Prefix (a b : List ConcreteStep) : Prop := ∃ suffix, b = a ++ suffix

theorem pathsDisjoint_sound {Δ : FactEnv} {ν : Nat → Nat} {a b : List PathStep}
    (hΔ : Δ.Valid ν) (h : pathsDisjoint Δ a b = true) :
    ¬ Prefix (resolvePath ν a) (resolvePath ν b) ∧
    ¬ Prefix (resolvePath ν b) (resolvePath ν a) := by
  induction a generalizing b with
  | nil => simp [pathsDisjoint] at h
  | cons x xs ih =>
    cases b with
    | nil => simp [pathsDisjoint] at h
    | cons y ys =>
      simp only [pathsDisjoint, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with h | ⟨rfl, h⟩
      · have hn := stepsDisjoint_sound hΔ h
        constructor
        · rintro ⟨suffix, he⟩
          simp only [resolvePath, List.map_cons, List.cons_append, List.cons.injEq] at he
          exact hn he.1.symm
        · rintro ⟨suffix, he⟩
          simp only [resolvePath, List.map_cons, List.cons_append, List.cons.injEq] at he
          exact hn he.1
      · rcases ih h with ⟨ha, hb⟩
        constructor
        · rintro ⟨suffix, he⟩
          apply ha; exact ⟨suffix, (List.cons.inj he).2⟩
        · rintro ⟨suffix, he⟩
          apply hb; exact ⟨suffix, (List.cons.inj he).2⟩

end Aethel
