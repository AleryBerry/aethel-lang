import Aethel.Disjointness
import Aethel.Paths

namespace Aethel

/-- Canonical affine index form `base + offset` (or constant `offset` when `base = none`). -/
structure AffineForm where
  base : Option Nat
  offset : Nat
  deriving Repr, DecidableEq

def AffineForm.eval (ν : Nat → Nat) : AffineForm → Nat
  | ⟨none, c⟩ => c
  | ⟨some id, c⟩ => ν id + c

def IdxExpr.toAffine? : IdxExpr → Option AffineForm
  | .const n => some ⟨none, n⟩
  | .value id => some ⟨some id, 0⟩
  | .add l r =>
    match l.toAffine?, r.toAffine? with
    | some ⟨none, c1⟩, some ⟨b, c2⟩ => some ⟨b, c1 + c2⟩
    | some ⟨b, c1⟩, some ⟨none, c2⟩ => some ⟨b, c1 + c2⟩
    | _, _ => none

theorem IdxExpr.toAffine_sound {e : IdxExpr} {af : AffineForm}
    (h : e.toAffine? = some af) (ν : Nat → Nat) :
    af.eval ν = e.eval ν := by
  induction e generalizing af with
  | const n =>
    cases h
    rfl
  | value id =>
    cases h
    simp [AffineForm.eval, IdxExpr.eval]
  | add l r ihl ihr =>
    simp only [toAffine?] at h
    cases hl : l.toAffine? with
    | none => simp [hl] at h
    | some afl =>
      cases hr : r.toAffine? with
      | none => simp [hl, hr] at h
      | some afr =>
        have el := ihl hl
        have er := ihr hr
        cases afl with
        | mk bl cl =>
          cases afr with
          | mk br cr =>
            cases bl <;> cases br <;> simp only [hl, hr] at h
            · cases h; simp [AffineForm.eval, IdxExpr.eval] at *; omega
            · cases h; simp [AffineForm.eval, IdxExpr.eval] at *; omega
            · cases h; simp [AffineForm.eval, IdxExpr.eval] at *; omega
            · contradiction

/-- Fact environment extended with `<` and `≤` relationships over value identities. -/
structure OrderFactEnv where
  base : FactEnv := {}
  ltFacts : List (Nat × Nat) := []
  leFacts : List (Nat × Nat) := []
  deriving Repr

def OrderFactEnv.Valid (Δ : OrderFactEnv) (ν : Nat → Nat) : Prop :=
  Δ.base.Valid ν ∧
  (∀ x y, (x, y) ∈ Δ.ltFacts → ν x < ν y) ∧
  (∀ x y, (x, y) ∈ Δ.leFacts → ν x ≤ ν y)

def OrderFactEnv.assumeLt (Δ : OrderFactEnv) (x y : Nat) : OrderFactEnv :=
  { Δ with ltFacts := (x, y) :: Δ.ltFacts }

def OrderFactEnv.assumeLe (Δ : OrderFactEnv) (x y : Nat) : OrderFactEnv :=
  { Δ with leFacts := (x, y) :: Δ.leFacts }

theorem OrderFactEnv.assumeLt_valid {Δ : OrderFactEnv} {ν : Nat → Nat} {x y : Nat}
    (hΔ : Δ.Valid ν) (hlt : ν x < ν y) : (Δ.assumeLt x y).Valid ν := by
  refine ⟨hΔ.1, ?_, hΔ.2.2⟩
  intro a b hmem
  rcases List.mem_cons.mp hmem with hEq | hOld
  · cases hEq
    exact hlt
  · exact hΔ.2.1 a b hOld

theorem OrderFactEnv.assumeLe_valid {Δ : OrderFactEnv} {ν : Nat → Nat} {x y : Nat}
    (hΔ : Δ.Valid ν) (hle : ν x ≤ ν y) : (Δ.assumeLe x y).Valid ν := by
  refine ⟨hΔ.1, hΔ.2.1, ?_⟩
  intro a b hmem
  rcases List.mem_cons.mp hmem with hEq | hOld
  · cases hEq
    exact hle
  · exact hΔ.2.2 a b hOld

def OrderFactEnv.provesLe (Δ : OrderFactEnv) (a b : IdxExpr) : Bool :=
  match a.toAffine?, b.toAffine? with
  | some ⟨none, c1⟩, some ⟨none, c2⟩ => decide (c1 ≤ c2)
  | some ⟨none, c1⟩, some ⟨some _, c2⟩ => decide (c1 ≤ c2)
  | some ⟨some x, c1⟩, some ⟨some y, c2⟩ =>
    if x == y then decide (c1 ≤ c2)
    else decide (c1 ≤ c2 ∧ ((x, y) ∈ Δ.leFacts ∨ (x, y) ∈ Δ.ltFacts))
  | _, _ => false

theorem OrderFactEnv.provesLe_sound {Δ : OrderFactEnv} {ν : Nat → Nat} {a b : IdxExpr}
    (hΔ : Δ.Valid ν) (h : Δ.provesLe a b = true) :
    a.eval ν ≤ b.eval ν := by
  unfold provesLe at h
  cases ha : a.toAffine? with
  | none => simp [ha] at h
  | some afa =>
    cases hb : b.toAffine? with
    | none => simp [ha, hb] at h
    | some afb =>
      have eva := IdxExpr.toAffine_sound ha ν
      have evb := IdxExpr.toAffine_sound hb ν
      rw [← eva, ← evb]
      cases afa with
      | mk ba ca =>
        cases afb with
        | mk bb cb =>
          cases ba <;> cases bb <;> simp only [ha, hb] at h
          · have hc : ca ≤ cb := of_decide_eq_true h
            exact hc
          · have hc : ca ≤ cb := of_decide_eq_true h
            simp [AffineForm.eval]
            omega
          · contradiction
          · rename_i x y
            by_cases hxy : x = y
            · subst hxy
              simp only [beq_self_eq_true, ↓reduceIte, decide_eq_true_eq] at h
              simp [AffineForm.eval]
              omega
            · have hxyBool : (x == y) = false := beq_false_of_ne hxy
              simp only [hxyBool, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at h
              obtain ⟨hc, hFact⟩ := h
              simp [AffineForm.eval]
              rcases hFact with hLe | hLt
              · have := hΔ.2.2 x y hLe; omega
              · have := hΔ.2.1 x y hLt; omega

def OrderFactEnv.provesLt (Δ : OrderFactEnv) (a b : IdxExpr) : Bool :=
  match a.toAffine?, b.toAffine? with
  | some ⟨none, c1⟩, some ⟨none, c2⟩ => decide (c1 < c2)
  | some ⟨none, c1⟩, some ⟨some _, c2⟩ => decide (c1 < c2)
  | some ⟨some x, c1⟩, some ⟨some y, c2⟩ =>
    if x == y then decide (c1 < c2)
    else decide (((x, y) ∈ Δ.ltFacts ∧ c1 ≤ c2) ∨ ((x, y) ∈ Δ.leFacts ∧ c1 < c2))
  | _, _ => false

theorem OrderFactEnv.provesLt_sound {Δ : OrderFactEnv} {ν : Nat → Nat} {a b : IdxExpr}
    (hΔ : Δ.Valid ν) (h : Δ.provesLt a b = true) :
    a.eval ν < b.eval ν := by
  unfold provesLt at h
  cases ha : a.toAffine? with
  | none => simp [ha] at h
  | some afa =>
    cases hb : b.toAffine? with
    | none => simp [ha, hb] at h
    | some afb =>
      have eva := IdxExpr.toAffine_sound ha ν
      have evb := IdxExpr.toAffine_sound hb ν
      rw [← eva, ← evb]
      cases afa with
      | mk ba ca =>
        cases afb with
        | mk bb cb =>
          cases ba <;> cases bb <;> simp only [ha, hb] at h
          · exact of_decide_eq_true h
          · have hc : ca < cb := of_decide_eq_true h
            simp [AffineForm.eval]
            omega
          · contradiction
          · rename_i x y
            by_cases hxy : x = y
            · subst hxy
              simp only [beq_self_eq_true, ↓reduceIte, decide_eq_true_eq] at h
              simp [AffineForm.eval]
              omega
            · have hxyBool : (x == y) = false := beq_false_of_ne hxy
              simp only [hxyBool, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at h
              simp [AffineForm.eval]
              rcases h with ⟨hLt, hc⟩ | ⟨hLe, hc⟩
              · have := hΔ.2.1 x y hLt; omega
              · have := hΔ.2.2 x y hLe; omega

def OrderFactEnv.provesNe (Δ : OrderFactEnv) (a b : IdxExpr) : Bool :=
  Δ.base.provesNe a b || Δ.provesLt a b || Δ.provesLt b a

theorem OrderFactEnv.provesNe_sound {Δ : OrderFactEnv} {ν : Nat → Nat} {a b : IdxExpr}
    (hΔ : Δ.Valid ν) (h : Δ.provesNe a b = true) :
    a.eval ν ≠ b.eval ν := by
  simp only [provesNe, Bool.or_eq_true] at h
  rcases h with (hBase | hLt) | hGt
  · exact Δ.base.provesNe_sound hΔ.1 hBase
  · exact Nat.ne_of_lt (Δ.provesLt_sound hΔ hLt)
  · exact Nat.ne_of_gt (Δ.provesLt_sound hΔ hGt)

structure SymbolicSlice where
  lo : IdxExpr
  hi : IdxExpr
  deriving Repr, DecidableEq

def SymbolicSlice.eval (ν : Nat → Nat) (s : SymbolicSlice) : Interval :=
  ⟨s.lo.eval ν, s.hi.eval ν⟩

def OrderFactEnv.slicesDisjoint (Δ : OrderFactEnv) (s1 s2 : SymbolicSlice) : Bool :=
  Δ.provesLe s1.hi s2.lo || Δ.provesLe s2.hi s1.lo ||
  Δ.provesLe s1.hi s1.lo || Δ.provesLe s2.hi s2.lo

theorem OrderFactEnv.slicesDisjoint_sound {Δ : OrderFactEnv} {ν : Nat → Nat}
    {s1 s2 : SymbolicSlice} {idx : Nat}
    (hΔ : Δ.Valid ν) (h : Δ.slicesDisjoint s1 s2 = true) :
    ¬ ((s1.eval ν).Contains idx ∧ (s2.eval ν).Contains idx) := by
  apply Interval.disjoint_sound
  simp only [slicesDisjoint, Bool.or_eq_true] at h
  simp only [Interval.disjoint, SymbolicSlice.eval]
  apply decide_eq_true
  rcases h with ((h1 | h2) | h3) | h4
  · exact Or.inl (Δ.provesLe_sound hΔ h1)
  · exact Or.inr (Or.inl (Δ.provesLe_sound hΔ h2))
  · exact Or.inr (Or.inr (Or.inl (Δ.provesLe_sound hΔ h3)))
  · exact Or.inr (Or.inr (Or.inr (Δ.provesLe_sound hΔ h4)))

def OrderFactEnv.stepsDisjoint (Δ : OrderFactEnv) : PathStep → PathStep → Bool
  | .field a, .field b => decide (a ≠ b)
  | .index a, .index b => Δ.provesNe a b
  | _, _ => false

theorem OrderFactEnv.stepsDisjoint_sound {Δ : OrderFactEnv} {ν : Nat → Nat} {a b : PathStep}
    (hΔ : Δ.Valid ν) (h : Δ.stepsDisjoint a b = true) :
    a.resolve ν ≠ b.resolve ν := by
  cases a <;> cases b <;> simp_all [stepsDisjoint, PathStep.resolve]
  exact Δ.provesNe_sound hΔ h

def OrderFactEnv.pathsDisjoint (Δ : OrderFactEnv) : List PathStep → List PathStep → Bool
  | a :: as, b :: bs => Δ.stepsDisjoint a b ||
      (decide (a = b) && Δ.pathsDisjoint as bs)
  | _, _ => false

theorem OrderFactEnv.pathsDisjoint_sound {Δ : OrderFactEnv} {ν : Nat → Nat} {a b : List PathStep}
    (hΔ : Δ.Valid ν) (h : Δ.pathsDisjoint a b = true) :
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
      · have hn := Δ.stepsDisjoint_sound hΔ h
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

/-- Machine arithmetic overflow-freedom certificate: when `x + c < 2 ^ width`,
modular addition equals mathematical natural addition. -/
def noWrapAdd (width x c : Nat) : Prop :=
  x + c < 2 ^ width

theorem noWrapAdd_exact {width x c : Nat} (h : noWrapAdd width x c) :
    (x + c) % 2 ^ width = x + c :=
  Nat.mod_eq_of_lt h

end Aethel
