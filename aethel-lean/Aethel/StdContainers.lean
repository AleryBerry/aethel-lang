import Aethel.DynamicMemory
import Aethel.CacheLayout
import Aethel.CategoricalTraits

namespace Aethel.StdContainers

open Aethel Aethel.CacheLayout Aethel.CategoricalTraits

/-!
## Standard Library Container Semantics & L1 Cache Efficiency (Phase 8 Lean Gate)

Models the dynamic container families shipped in Aethel `std/`:
1. SwissTable-style SoA metadata (`CtrlSlot`: 1-byte `h2` fingerprint array separate
   from keys/values) proving 64 control slots pack into one 64B L1 cache line and
   load-factor bound `used * 8 ≤ cap * 7` guarantees probe termination (`used < cap`).
2. `FlatMap K V` algebraic `Map` / `Set` lookup/insert/remove laws + Hash-Eq coherence
   with a counterexample showing unlawful `Hash` breaks `h2` fingerprint probing.
3. Power-of-two `Deque` ring buffer indexing `(head + idx) % cap`, proving bounds and
   in-range slot injectivity (`ringIndex_injective`), plus FIFO/LIFO operation lemmas.
-/

inductive CtrlSlot where
  | empty
  | tombstone
  | full (h2 : Fin 128)
  deriving Repr, DecidableEq

theorem swiss_ctrl_64_within_cacheLine {base : Nat} (hAlign : base % 64 = 0) :
    withinCacheLine 64 base 64 :=
  aligned_within_cacheLine (by decide) (by decide) (by decide) (by decide) hAlign

def SwissLoadValid (used cap : Nat) : Prop :=
  0 < cap ∧ used * 8 ≤ cap * 7

def checkSwissLoad (used cap : Nat) : Bool :=
  decide (0 < cap) && decide (used * 8 ≤ cap * 7)

theorem checkSwissLoad_correct (used cap : Nat) :
    checkSwissLoad used cap = true ↔ SwissLoadValid used cap := by
  unfold checkSwissLoad SwissLoadValid
  simp [Bool.and_eq_true]

theorem swissLoad_guarantees_empty_slot {used cap : Nat}
    (hValid : SwissLoadValid used cap) : used < cap := by
  rcases hValid with ⟨hPos, hLoad⟩
  omega

/-! ## Functional `FlatMap` Algebraic Semantics -/

structure FlatMap (K V : Type) where
  entries : List (K × V)
  deriving Repr, DecidableEq

def FlatMap.empty {K V : Type} : FlatMap K V := ⟨[]⟩

def FlatMap.lookup {K V : Type} [BEq K] (m : FlatMap K V) (k : K) : Option V :=
  match m.entries.find? (fun p => p.1 == k) with
  | some p => some p.2
  | none => none

def FlatMap.insert {K V : Type} [BEq K] (m : FlatMap K V) (k : K) (v : V) : FlatMap K V :=
  ⟨(k, v) :: m.entries.filter (fun p => p.1 != k)⟩

def FlatMap.remove {K V : Type} [BEq K] (m : FlatMap K V) (k : K) : FlatMap K V :=
  ⟨m.entries.filter (fun p => p.1 != k)⟩

def FlatMap.contains {K V : Type} [BEq K] (m : FlatMap K V) (k : K) : Bool :=
  (m.lookup k).isSome

theorem FlatMap.lookup_empty {K V : Type} [BEq K] (k : K) :
    (FlatMap.empty : FlatMap K V).lookup k = none := rfl

theorem FlatMap.lookup_insert_eq {K V : Type} [BEq K] [LawfulBEq K]
    (m : FlatMap K V) (k : K) (v : V) :
    (m.insert k v).lookup k = some v := by
  simp [FlatMap.insert, FlatMap.lookup]

private theorem find?_filter_ne_eq {K V : Type} [BEq K] [LawfulBEq K]
    (xs : List (K × V)) {k1 k2 : K} (hNe : k1 ≠ k2) :
    (xs.filter (fun p => p.1 != k1)).find? (fun p => p.1 == k2) =
      xs.find? (fun p => p.1 == k2) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx1 : x.1 = k1
    · have hx2 : (x.1 == k2) = false := by
        apply Bool.eq_false_iff.mpr
        intro hEq
        exact hNe (hx1.symm.trans (beq_iff_eq.mp hEq))
      have hBne : (x.1 != k1) = false := by
        simp [hx1]
      simp [List.filter, List.find?, hBne, hx2, ih]
    · have hBne : (x.1 != k1) = true := by simp [bne_iff_ne, hx1]
      dsimp only [List.filter]
      rw [hBne]
      by_cases hx2 : x.1 = k2
      · simp [List.find?, hx2]
      · have hx2F : (x.1 == k2) = false := beq_false_of_ne hx2
        simp [List.find?, hx2F, ih]

theorem FlatMap.lookup_insert_ne {K V : Type} [BEq K] [LawfulBEq K]
    (m : FlatMap K V) {k1 k2 : K} (v : V) (hNe : k1 ≠ k2) :
    (m.insert k1 v).lookup k2 = m.lookup k2 := by
  have hk12 : (k1 == k2) = false := beq_false_of_ne hNe
  simp only [FlatMap.insert, FlatMap.lookup, List.find?_cons, hk12]
  rw [find?_filter_ne_eq m.entries hNe]

theorem FlatMap.lookup_remove_eq {K V : Type} [BEq K] [LawfulBEq K]
    (m : FlatMap K V) (k : K) :
    (m.remove k).lookup k = none := by
  unfold FlatMap.remove FlatMap.lookup
  have hNone : (m.entries.filter (fun p => p.1 != k)).find? (fun p => p.1 == k) = none := by
    rw [List.find?_eq_none]
    intro p hp
    rw [List.mem_filter] at hp
    have hBne := hp.2
    simp only [bne_iff_ne, ne_eq] at hBne
    exact beq_false_of_ne hBne ▸ by decide
  simp [hNone]

theorem FlatMap.lookup_remove_ne {K V : Type} [BEq K] [LawfulBEq K]
    (m : FlatMap K V) {k1 k2 : K} (hNe : k1 ≠ k2) :
    (m.remove k1).lookup k2 = m.lookup k2 := by
  unfold FlatMap.remove FlatMap.lookup
  rw [find?_filter_ne_eq m.entries hNe]

/-! ## Eq / Hash Coherence & Unlawful-Hash Counterexample -/

structure EqLawTrait (α : Type) where
  eq : α → α → Bool
  refl : ∀ x, eq x x = true
  symm : ∀ x y, eq x y = eq y x
  sound : ∀ x y, eq x y = true ↔ x = y

structure HashLawTrait (α : Type) extends EqLawTrait α where
  hash : α → UInt64
  hash_congr : ∀ x y, eq x y = true → hash x = hash y

/-- Negative counterexample: two logically equal keys (signed magnitude pairs
`(0, true)` and `(0, false)`) whose broken hash gives distinct `h2` fingerprints,
breaking SwissTable probe equivalence. -/
def brokenKeyEq (a b : Nat × Bool) : Bool :=
  a.1 == b.1

def brokenKeyHash (a : Nat × Bool) : Nat :=
  if a.2 then 1 else 2

theorem unlawful_hash_misses_equal_bucket :
    brokenKeyEq (0, false) (0, true) = true ∧
    brokenKeyHash (0, false) % 128 ≠ brokenKeyHash (0, true) % 128 := by
  decide

/-! ## Power-of-Two `Deque` Ring Buffer Semantics -/

def ringIndex (head cap idx : Nat) : Nat :=
  (head + idx) % cap

theorem ringIndex_in_bounds {head cap idx : Nat} (hCap : 0 < cap) :
    ringIndex head cap idx < cap :=
  Nat.mod_lt _ hCap

private theorem mod_eq_sub_of_ge {x cap : Nat} (hLo : cap ≤ x) (hHi : x < cap + cap) :
    x % cap = x - cap := by
  have hRem : x - cap < cap := by omega
  have hEq : x = (x - cap) + cap := by omega
  calc
    x % cap = ((x - cap) + cap) % cap := congrArg (· % cap) hEq
    _ = ((x - cap) % cap + cap % cap) % cap := Nat.add_mod _ _ _
    _ = (x - cap) % cap := by simp [Nat.mod_eq_of_lt hRem]
    _ = x - cap := Nat.mod_eq_of_lt hRem

theorem ringIndex_injective {head cap len i j : Nat}
    (hLen : len ≤ cap) (hi : i < len) (hj : j < len)
    (hEq : ringIndex head cap i = ringIndex head cap j) : i = j := by
  have hCap : 0 < cap := by omega
  have hiCap : i < cap := Nat.lt_of_lt_of_le hi hLen
  have hjCap : j < cap := Nat.lt_of_lt_of_le hj hLen
  have hHeadMod : (head + i) % cap = ((head % cap) + i) % cap := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hiCap]
  have hHeadModJ : (head + j) % cap = ((head % cap) + j) % cap := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hjCap]
  unfold ringIndex at hEq
  rw [hHeadMod, hHeadModJ] at hEq
  have hHmLt : head % cap < cap := Nat.mod_lt head hCap
  by_cases hiWrap : head % cap + i < cap <;> by_cases hjWrap : head % cap + j < cap
  · rw [Nat.mod_eq_of_lt hiWrap, Nat.mod_eq_of_lt hjWrap] at hEq
    omega
  · have hjMod := mod_eq_sub_of_ge (by omega : cap ≤ head % cap + j) (by omega)
    rw [Nat.mod_eq_of_lt hiWrap, hjMod] at hEq
    omega
  · have hiMod := mod_eq_sub_of_ge (by omega : cap ≤ head % cap + i) (by omega)
    rw [hiMod, Nat.mod_eq_of_lt hjWrap] at hEq
    omega
  · have hiMod := mod_eq_sub_of_ge (by omega : cap ≤ head % cap + i) (by omega)
    have hjMod := mod_eq_sub_of_ge (by omega : cap ≤ head % cap + j) (by omega)
    rw [hiMod, hjMod] at hEq
    omega

structure RingDeque (α : Type) where
  elems : List α
  deriving Repr, DecidableEq

def RingDeque.empty {α : Type} : RingDeque α := ⟨[]⟩

def RingDeque.pushBack {α : Type} (d : RingDeque α) (x : α) : RingDeque α :=
  ⟨d.elems ++ [x]⟩

def RingDeque.pushFront {α : Type} (d : RingDeque α) (x : α) : RingDeque α :=
  ⟨x :: d.elems⟩

def RingDeque.popFront {α : Type} (d : RingDeque α) : Option (α × RingDeque α) :=
  match d.elems with
  | [] => none
  | x :: xs => some (x, ⟨xs⟩)

def RingDeque.popBack {α : Type} (d : RingDeque α) : Option (α × RingDeque α) :=
  match d.elems.reverse with
  | [] => none
  | x :: xs => some (x, ⟨xs.reverse⟩)

theorem RingDeque.popFront_pushFront {α : Type} (d : RingDeque α) (x : α) :
    (d.pushFront x).popFront = some (x, d) := rfl

theorem RingDeque.popFront_pushBack_singleton {α : Type} (x : α) :
    ((RingDeque.empty : RingDeque α).pushBack x).popFront = some (x, RingDeque.empty) := rfl

theorem RingDeque.popBack_pushBack {α : Type} (d : RingDeque α) (x : α) :
    (d.pushBack x).popBack = some (x, d) := by
  simp [RingDeque.pushBack, RingDeque.popBack]

end Aethel.StdContainers
