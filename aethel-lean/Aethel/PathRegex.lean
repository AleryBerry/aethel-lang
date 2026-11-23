import Std

namespace Aethel

/-- Exact regexes over concrete symbols. Symbolic overlap is a separate judgment. -/
inductive Regex (α : Type) where
  | empty | epsilon
  | atom (symbol : α)
  | seq (left right : Regex α)
  | alt (left right : Regex α)
  | star (body : Regex α)
  deriving Repr, DecidableEq

namespace Regex

inductive Matches : Regex α → List α → Prop where
  | epsilon : Matches .epsilon []
  | atom : Matches (.atom a) [a]
  | seq : Matches r xs → Matches s ys → Matches (.seq r s) (xs ++ ys)
  | left : Matches r xs → Matches (.alt r s) xs
  | right : Matches s xs → Matches (.alt r s) xs
  | starNil : Matches (.star r) []
  | starCons : Matches r xs → Matches (.star r) ys → Matches (.star r) (xs ++ ys)

def nullable : Regex α → Bool
  | .empty | .atom _ => false
  | .epsilon | .star _ => true
  | .seq r s => nullable r && nullable s
  | .alt r s => nullable r || nullable s

@[simp] theorem matches_empty : ¬ Matches (.empty : Regex α) xs := by
  intro h; cases h

@[simp] theorem matches_epsilon : Matches (.epsilon : Regex α) xs ↔ xs = [] := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst xs; exact .epsilon

@[simp] theorem matches_atom : Matches (.atom a : Regex α) xs ↔ xs = [a] := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst xs; exact .atom

@[simp] theorem matches_alt : Matches (.alt r s) xs ↔ Matches r xs ∨ Matches s xs := by
  constructor
  · intro h; cases h with
    | left h => exact Or.inl h
    | right h => exact Or.inr h
  · intro h; cases h with
    | inl h => exact .left h
    | inr h => exact .right h

theorem matches_seq : Matches (.seq r s) zs ↔
    ∃ xs ys, zs = xs ++ ys ∧ Matches r xs ∧ Matches s ys := by
  constructor
  · intro h; cases h with
    | seq hx hy => exact ⟨_, _, rfl, hx, hy⟩
  · rintro ⟨xs, ys, rfl, hx, hy⟩; exact .seq hx hy

@[simp] theorem nullable_correct (r : Regex α) : nullable r = true ↔ Matches r [] := by
  induction r with
  | empty => simp [nullable]
  | epsilon => simp [nullable]
  | atom a => simp [nullable]
  | alt r s ih₁ ih₂ => simp [nullable, ih₁, ih₂]
  | seq r s ih₁ ih₂ =>
    simp only [nullable, Bool.and_eq_true, ih₁, ih₂, matches_seq]
    constructor
    · rintro ⟨hr, hs⟩; exact ⟨[], [], rfl, hr, hs⟩
    · rintro ⟨xs, ys, h, hr, hs⟩
      have h' : xs = [] ∧ ys = [] := List.append_eq_nil_iff.mp h.symm
      rcases h' with ⟨rfl, rfl⟩; exact ⟨hr, hs⟩
  | star r ih => exact ⟨fun _ => .starNil, fun _ => rfl⟩

def deriv [DecidableEq α] : Regex α → α → Regex α
  | .empty, _ | .epsilon, _ => .empty
  | .atom b, a => if a = b then .epsilon else .empty
  | .alt r s, a => .alt (deriv r a) (deriv s a)
  | .seq r s, a =>
    if nullable r then .alt (.seq (deriv r a) s) (deriv s a)
    else .seq (deriv r a) s
  | .star r, a => .seq (deriv r a) (.star r)

/-- Remove nullable iterations before the first consumed symbol. -/
theorem star_cons_inv (h : Matches (.star r) (a :: xs)) :
    ∃ pre suffix, xs = pre ++ suffix ∧
      Matches r (a :: pre) ∧ Matches (.star r) suffix := by
  generalize hz : a :: xs = zs at h
  generalize ht : Regex.star r = t at h
  induction h <;> cases ht
  case starNil => cases hz
  case starCons u v hu hv ihu ihv =>
    cases u with
    | nil => exact ihv hz rfl
    | cons b bs =>
      cases hz
      exact ⟨bs, v, rfl, hu, hv⟩

/-- Exact Brzozowski derivative theorem; no symbolic aliasing assumptions. -/
theorem deriv_correct [DecidableEq α] (r : Regex α) (a : α) (xs : List α) :
    Matches (deriv r a) xs ↔ Matches r (a :: xs) := by
  induction r generalizing xs with
  | empty => simp [deriv]
  | epsilon => simp [deriv]
  | atom b => by_cases h : a = b <;> simp [deriv, h]
  | alt r s ih₁ ih₂ => simp [deriv, ih₁, ih₂]
  | seq r s ih₁ ih₂ =>
    constructor
    · intro h
      by_cases hn : nullable r = true
      · simp only [deriv, hn, ↓reduceIte, matches_alt] at h
        rcases h with h | h
        · rcases matches_seq.mp h with ⟨u, v, rfl, hu, hv⟩
          exact .seq ((ih₁ u).mp hu) hv
        · exact .seq (nullable_correct r |>.mp hn) ((ih₂ xs).mp h)
      · simp only [deriv, hn, Bool.false_eq_true, ↓reduceIte] at h
        rcases matches_seq.mp h with ⟨u, v, rfl, hu, hv⟩
        exact .seq ((ih₁ u).mp hu) hv
    · intro h
      rcases matches_seq.mp h with ⟨u, v, heq, hu, hv⟩
      cases u with
      | nil =>
        have hn := (nullable_correct r).mpr hu
        simp only [List.nil_append] at heq
        subst v
        simp only [deriv, hn, ↓reduceIte, matches_alt]
        exact Or.inr ((ih₂ xs).mpr hv)
      | cons b bs =>
        simp only [List.cons_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        have hd : Matches (.seq (deriv r a) s) (bs ++ v) :=
          .seq ((ih₁ bs).mpr hu) hv
        by_cases hn : nullable r = true
        · simp only [deriv, hn, ↓reduceIte, matches_alt]; exact Or.inl hd
        · simpa only [deriv, hn, Bool.false_eq_true, ↓reduceIte] using hd
  | star r ih =>
    simp only [deriv, matches_seq]
    constructor
    · rintro ⟨u, v, rfl, hu, hv⟩
      exact .starCons ((ih u).mp hu) hv
    · intro h
      rcases star_cons_inv h with ⟨u, v, rfl, hu, hv⟩
      exact ⟨u, v, rfl, (ih u).mpr hu, hv⟩

def accepts [DecidableEq α] (r : Regex α) : List α → Bool
  | [] => nullable r
  | a :: xs => accepts (deriv r a) xs

theorem accepts_correct [DecidableEq α] (r : Regex α) (xs : List α) :
    accepts r xs = true ↔ Matches r xs := by
  induction xs generalizing r with
  | nil => exact nullable_correct r
  | cons a xs ih => exact (ih (deriv r a)).trans (deriv_correct r a xs)

def inhabited : Regex α → Bool
  | .empty => false
  | .epsilon | .atom _ | .star _ => true
  | .seq r s => inhabited r && inhabited s
  | .alt r s => inhabited r || inhabited s

theorem inhabited_of_matches (h : Matches r xs) : inhabited r = true := by
  induction h <;> simp_all [inhabited]

theorem inhabited_witness (r : Regex α) (h : inhabited r = true) :
    ∃ xs, Matches r xs := by
  induction r with
  | empty => simp [inhabited] at h
  | epsilon => exact ⟨[], .epsilon⟩
  | atom a => exact ⟨[a], .atom⟩
  | star r ih => exact ⟨[], .starNil⟩
  | seq r s ihr ihs =>
    simp only [inhabited, Bool.and_eq_true] at h
    obtain ⟨xs, hx⟩ := ihr h.1
    obtain ⟨ys, hy⟩ := ihs h.2
    exact ⟨xs ++ ys, .seq hx hy⟩
  | alt r s ihr ihs =>
    simp only [inhabited, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨xs, hx⟩ := ihr h
      exact ⟨xs, .left hx⟩
    · obtain ⟨xs, hx⟩ := ihs h
      exact ⟨xs, .right hx⟩

def positive : Regex α → Bool
  | .empty | .epsilon => false
  | .atom _ => true
  | .seq r s => (positive r && inhabited s) || (inhabited r && positive s)
  | .alt r s => positive r || positive s
  | .star r => positive r

theorem positive_of_matches (h : Matches r xs) (hne : xs ≠ []) : positive r = true := by
  induction h <;> grind [positive, inhabited_of_matches, List.append_eq_nil_iff]

theorem positive_witness (r : Regex α) (h : positive r = true) :
    ∃ xs, Matches r xs ∧ xs ≠ [] := by
  induction r with
  | empty => simp [positive] at h
  | epsilon => simp [positive] at h
  | atom a => exact ⟨[a], .atom, List.cons_ne_nil _ _⟩
  | seq r s ihr ihs =>
    simp only [positive, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨hr, hs⟩ | ⟨hr, hs⟩
    · obtain ⟨u, hu, hne⟩ := ihr hr
      obtain ⟨v, hv⟩ := inhabited_witness s hs
      exact ⟨u ++ v, .seq hu hv, by simp [hne]⟩
    · obtain ⟨v, hv, hne⟩ := ihs hs
      obtain ⟨u, hu⟩ := inhabited_witness r hr
      exact ⟨u ++ v, .seq hu hv, by simp [hne]⟩

  | alt r s ihr ihs =>
    simp only [positive, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨u, hu, hne⟩ := ihr h
      exact ⟨u, .left hu, hne⟩
    · obtain ⟨v, hv, hne⟩ := ihs h
      exact ⟨v, .right hv, hne⟩
  | star r ih =>
    obtain ⟨u, hu, hne⟩ := ih h
    exact ⟨u ++ [], .starCons hu .starNil, by simpa using hne⟩

/-- Exact decision procedure for L(r) ⊆ {epsilon}, including empty products. -/
def onlyEmpty (r : Regex α) : Bool := !positive r

theorem onlyEmpty_correct (r : Regex α) :
    onlyEmpty r = true ↔ ∀ xs, Matches r xs → xs = [] := by
  constructor
  · intro h xs hm
    grind [onlyEmpty, positive_of_matches]
  · intro h
    by_cases hp : positive r = true
    · obtain ⟨xs, hm, hne⟩ := positive_witness r hp
      exact False.elim (hne (h xs hm))
    · simpa [onlyEmpty] using hp

/-- Regression: distinct prefixes may have identical residual languages. -/
theorem residuals_can_overlap :
    Matches (deriv (.alt (.atom (0 : Nat)) (.atom 1)) 0) [] ∧
    Matches (deriv (.alt (.atom (0 : Nat)) (.atom 1)) 1) [] := by
  constructor <;> apply (accepts_correct _ []).mp <;> decide

end Regex
end Aethel
