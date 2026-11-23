import Aethel.BoundedSearch
import Aethel.StatusCodec
import Aethel.ADTLayout

namespace Aethel.LawFalsifier

open Aethel Aethel.Search Aethel.ADTLayout

/-!
## Tier 1 — Counterexample Falsifier & Exhaustive Finite Checker

Explores finite types (`Bool`, `Fin n`, `UInt8`, `Status`, products) exhaustively or with
bounded resumable search to immediately exhibit counterexamples when code violates a law.
-/

/-- Enumerated finite domain carrying a proof that every value appears in `elems`. -/
structure FiniteDomain (α : Type) where
  elems : List α
  complete : ∀ x : α, x ∈ elems

inductive LawVerdict (α : Type) where
  | proved
  | falsified (witness : α)
  deriving Repr, DecidableEq

def boolDomain : FiniteDomain Bool where
  elems := [false, true]
  complete := by
    intro b
    cases b <;> simp

def finDomain (n : Nat) : FiniteDomain (Fin n) where
  elems := List.finRange n
  complete := fun x => List.mem_finRange x

private theorem toUInt8_toNat (x : UInt8) : x.toNat.toUInt8 = x := by
  rw [← UInt8.toNat_inj]
  simp only [Nat.toUInt8, UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt x.toNat_lt

def u8Domain : FiniteDomain UInt8 where
  elems := (List.range 256).map Nat.toUInt8
  complete := by
    intro x
    apply List.mem_map.mpr
    exact ⟨x.toNat, List.mem_range.mpr x.toNat_lt, toUInt8_toNat x⟩

def statusDomain : FiniteDomain Status where
  elems := [.idle, .dead] ++ (List.finRange 4).map .moving ++ (List.finRange 16).map .poisoned
  complete := by
    intro s
    cases s with
    | idle => simp
    | dead => simp
    | moving v => simp [List.mem_finRange]
    | poisoned v => simp [List.mem_finRange]

def prodDomain {α β : Type} (da : FiniteDomain α) (db : FiniteDomain β) : FiniteDomain (α × β) where
  elems := da.elems.flatMap fun a => db.elems.map fun b => (a, b)
  complete := by
    rintro ⟨a, b⟩
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨a, da.complete a, b, db.complete b, rfl⟩

def findCounterexample {α : Type} (candidates : List α) (prop : α → Bool) : Option α :=
  candidates.find? fun x => !prop x

def verifyExhaustive {α : Type} (dom : FiniteDomain α) (prop : α → Bool) : LawVerdict α :=
  match findCounterexample dom.elems prop with
  | none => .proved
  | some witness => .falsified witness

def falsifyProbe {α : Type} (prop : α → Bool) : List α → Search.Probe (List α) α
  | [] => .finished
  | x :: xs => if prop x then .advance xs else .found x

def boundedFalsify {α : Type} (prop : α → Bool) (budget : Nat) (candidates : List α) :
    Search.Outcome (List α) α :=
  Search.run (falsifyProbe prop) budget candidates

theorem findCounterexample_some_refutes {α : Type} {candidates : List α} {prop : α → Bool}
    {w : α} (hFound : findCounterexample candidates prop = some w) :
    prop w = false ∧ ¬ (∀ x : α, prop x = true) := by
  dsimp [findCounterexample] at hFound
  have hPred : (!prop w) = true :=
    List.find?_some (p := fun x => !prop x) hFound
  have hFalse : prop w = false := by simpa using hPred
  refine ⟨hFalse, fun hAll => ?_⟩
  have hTrue := hAll w
  rw [hTrue] at hFalse
  cases hFalse

theorem verifyExhaustive_proved_iff {α : Type} (dom : FiniteDomain α) (prop : α → Bool) :
    verifyExhaustive dom prop = .proved ↔ ∀ x : α, prop x = true := by
  dsimp [verifyExhaustive, findCounterexample]
  cases hFind : dom.elems.find? (fun x => !prop x) with
  | none =>
    constructor
    · intro _ x
      have hNone := List.find?_eq_none.mp hFind x (dom.complete x)
      simpa using hNone
    · intro _
      rfl
  | some w =>
    constructor
    · intro hEq
      cases hEq
    · intro hAll
      have hPred : (!prop w) = true :=
        List.find?_some (p := fun x => !prop x) hFind
      have hTrue := hAll w
      simp [hTrue] at hPred

theorem verifyExhaustive_falsified_sound {α : Type} {dom : FiniteDomain α} {prop : α → Bool}
    {w : α} (hFal : verifyExhaustive dom prop = .falsified w) :
    prop w = false ∧ ¬ (∀ x : α, prop x = true) := by
  dsimp [verifyExhaustive] at hFal
  cases hFind : findCounterexample dom.elems prop with
  | none =>
    simp [hFind] at hFal
  | some v =>
    rw [hFind] at hFal
    cases hFal
    exact findCounterexample_some_refutes hFind

theorem boundedFalsify_found_refutes {α : Type} {prop : α → Bool} {budget : Nat}
    {candidates : List α} {w : α}
    (hFound : boundedFalsify prop budget candidates = .found w) :
    prop w = false ∧ ¬ (∀ x : α, prop x = true) := by
  induction budget generalizing candidates with
  | zero =>
    simp [boundedFalsify, Search.run] at hFound
  | succ b ih =>
    cases candidates with
    | nil =>
      simp [boundedFalsify, Search.run, falsifyProbe] at hFound
    | cons x xs =>
      by_cases hx : prop x = true
      · simp only [boundedFalsify, Search.run, falsifyProbe, hx, ↓reduceIte] at hFound
        exact ih hFound
      · have hxFalse : prop x = false := Bool.eq_false_iff.mpr hx
        simp only [boundedFalsify, Search.run, falsifyProbe, hxFalse, Bool.false_eq_true, ↓reduceIte] at hFound
        cases hFound
        refine ⟨hxFalse, fun hAll => ?_⟩
        have hT := hAll w
        rw [hT] at hxFalse
        cases hxFalse

theorem boundedFalsify_finished_all {α : Type} {prop : α → Bool} {budget : Nat}
    {candidates : List α}
    (hFin : boundedFalsify prop budget candidates = .finished) :
    ∀ x ∈ candidates, prop x = true := by
  induction budget generalizing candidates with
  | zero =>
    simp [boundedFalsify, Search.run] at hFin
  | succ b ih =>
    cases candidates with
    | nil =>
      intro _ hx
      cases hx
    | cons x xs =>
      by_cases hx : prop x = true
      · simp only [boundedFalsify, Search.run, falsifyProbe, hx, ↓reduceIte] at hFin
        intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hyXs
        · exact hx
        · exact ih hFin y hyXs
      · have hxFalse : prop x = false := Bool.eq_false_iff.mpr hx
        simp only [boundedFalsify, Search.run, falsifyProbe, hxFalse, Bool.false_eq_true, ↓reduceIte] at hFin
        cases hFin

theorem boundedFalsify_finished_complete {α : Type} (dom : FiniteDomain α) (prop : α → Bool)
    {budget : Nat} (hFin : boundedFalsify prop budget dom.elems = .finished) :
    ∀ x : α, prop x = true :=
  fun x => boundedFalsify_finished_all hFin x (dom.complete x)

theorem boundedFalsify_resume {α : Type} (prop : α → Bool) {budget : Nat}
    {initial rest : List α}
    (hPending : boundedFalsify prop budget initial = .pending rest) (extra : Nat) :
    boundedFalsify prop (extra + budget) initial = boundedFalsify prop extra rest :=
  Search.run_resume hPending extra

/-- Concrete safe and buggy damage arithmetic models (`apply_damage`). -/
def saturatingSubU8 (hp dmg : UInt8) : UInt8 :=
  if dmg ≤ hp then hp - dmg else 0

def wrappingSubU8 (hp dmg : UInt8) : UInt8 :=
  hp - dmg

theorem saturatingSubU8_never_exceeds (hp dmg : UInt8) :
    ¬ (saturatingSubU8 hp dmg > hp) := by
  dsimp [saturatingSubU8]
  split
  · next hLe =>
    have hLeNat : dmg.toNat ≤ hp.toNat := hLe
    rw [gt_iff_lt, UInt8.lt_iff_toNat_lt, UInt8.toNat_sub_of_le hp dmg hLe]
    omega
  · rw [gt_iff_lt, UInt8.lt_iff_toNat_lt]
    simp

theorem status_roundTrip_exhaustive :
    verifyExhaustive statusDomain (fun s => Status.decode (Status.encode s) == some s) = .proved := by
  rw [verifyExhaustive_proved_iff]
  intro s
  simp [Status.decode_encode s]

theorem badStatusDecoder_falsified :
    verifyExhaustive statusDomain (fun _ => some Status.idle == (none : Option Status)) = .falsified .idle := by
  decide

theorem badConstDecoder_falsified :
    verifyExhaustive statusDomain (fun s => some Status.idle == some s) = .falsified .dead := by
  decide

theorem wrappingSubU8_falsified :
    boundedFalsify (fun p : UInt8 × UInt8 => !(decide (wrappingSubU8 p.1 p.2 > p.1))) 4
      [(0, 0), (0, 1), (5, 2)] = .found (0, 1) := by
  decide

theorem wrappingSubU8_violates_never_exceed :
    ¬ (∀ hp dmg : UInt8, !(decide (wrappingSubU8 hp dmg > hp)) = true) := by
  intro hAll
  have ⟨_, hNotAll⟩ := boundedFalsify_found_refutes wrappingSubU8_falsified
  exact hNotAll fun p => hAll p.1 p.2

end Aethel.LawFalsifier
