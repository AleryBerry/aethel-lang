import Aethel.CacheLayout
import Aethel.ResourceFrame

namespace Aethel.CategoricalFusion

open Aethel Aethel.Core Aethel.CacheLayout

/-!
## Effectful In-Place Functorial Traversal & Loop Fusion

Models explicit in-place field mutations across AoS, SoA, and Tiled AoSoA
collection layouts and proves functor identity, horizontal composition fusion,
disjoint-field commutativity, dual-field loop fusion, and map-fold deforestation.
-/

def mapFieldStep (owner : OwnerId) (layout : CollectionLayout)
    (length fieldCount field : Nat) (f : UInt8 → UInt8)
    (s : Core.State) (i : Nat) : Core.State :=
  applyElemField owner layout length fieldCount field f s i

def mapFieldLoop (owner : OwnerId) (layout : CollectionLayout)
    (length fieldCount field : Nat) (f : UInt8 → UInt8)
    (s : Core.State) : Nat → Core.State
  | 0 => s
  | n + 1 =>
    let mid := mapFieldLoop owner layout length fieldCount field f s n
    mapFieldStep owner layout length fieldCount field f mid n

def mapFieldInPlace (owner : OwnerId) (layout : CollectionLayout)
    (length fieldCount field : Nat) (f : UInt8 → UInt8)
    (s : Core.State) : Core.State :=
  mapFieldLoop owner layout length fieldCount field f s length

def mapTwoFieldsStep (owner : OwnerId) (layout : CollectionLayout)
    (length fieldCount f1 f2 : Nat) (fn1 fn2 : UInt8 → UInt8)
    (s : Core.State) (i : Nat) : Core.State :=
  let loc1 : ByteLocation := ⟨owner, collectionSlot layout length fieldCount i f1⟩
  let loc2 : ByteLocation := ⟨owner, collectionSlot layout length fieldCount i f2⟩
  let s1 := match s.byte loc1 with | some b => s.store loc1 (fn1 b) | none => s
  match s1.byte loc2 with | some b => s1.store loc2 (fn2 b) | none => s1

def mapTwoFieldsLoop (owner : OwnerId) (layout : CollectionLayout)
    (length fieldCount f1 f2 : Nat) (fn1 fn2 : UInt8 → UInt8)
    (s : Core.State) : Nat → Core.State
  | 0 => s
  | n + 1 =>
    let mid := mapTwoFieldsLoop owner layout length fieldCount f1 f2 fn1 fn2 s n
    mapTwoFieldsStep owner layout length fieldCount f1 f2 fn1 fn2 mid n

def mapTwoFieldsInPlace (owner : OwnerId) (layout : CollectionLayout)
    (length fieldCount f1 f2 : Nat) (fn1 fn2 : UInt8 → UInt8)
    (s : Core.State) : Core.State :=
  mapTwoFieldsLoop owner layout length fieldCount f1 f2 fn1 fn2 s length

def foldFieldStep (owner : OwnerId) (layout : CollectionLayout)
    (length fieldCount field : Nat) {β : Type} (step : β → UInt8 → β)
    (s : Core.State) (acc : β) (i : Nat) : β :=
  match s.byte ⟨owner, collectionSlot layout length fieldCount i field⟩ with
  | some b => step acc b
  | none => acc

def foldFieldLoop (owner : OwnerId) (layout : CollectionLayout)
    (length fieldCount field : Nat) {β : Type} (step : β → UInt8 → β)
    (s : Core.State) (init : β) : Nat → β
  | 0 => init
  | n + 1 =>
    let acc := foldFieldLoop owner layout length fieldCount field step s init n
    foldFieldStep owner layout length fieldCount field step s acc n

def foldField (owner : OwnerId) (layout : CollectionLayout)
    (length fieldCount field : Nat) {β : Type} (init : β) (step : β → UInt8 → β)
    (s : Core.State) : β :=
  foldFieldLoop owner layout length fieldCount field step s init length

private theorem mapFieldLoop_byte {owner : OwnerId} {layout : CollectionLayout}
    (hValid : layout.Valid) {length fieldCount field n : Nat}
    (hN : n ≤ length) (hField : field < fieldCount)
    (f : UInt8 → UInt8) (s : Core.State) (loc : ByteLocation) :
    (mapFieldLoop owner layout length fieldCount field f s n).byte loc =
      if ∃ i, i < n ∧ loc = ⟨owner, collectionSlot layout length fieldCount i field⟩
      then (s.byte loc).map f
      else s.byte loc := by
  classical
  induction n generalizing loc with
  | zero =>
    simp [mapFieldLoop]
  | succ n ih =>
    have hNLe : n ≤ length := Nat.le_of_succ_le hN
    have hNLt : n < length := hN
    let locN : ByteLocation := ⟨owner, collectionSlot layout length fieldCount n field⟩
    have hNotLt : ¬ ∃ i, i < n ∧ locN = ⟨owner, collectionSlot layout length fieldCount i field⟩ := by
      rintro ⟨i, hiLt, hEq⟩
      have hSlotEq : collectionSlot layout length fieldCount n field =
          collectionSlot layout length fieldCount i field := congrArg ByteLocation.offset hEq
      have hSame := (collectionSlot_eq_iff hValid hNLt (Nat.lt_trans hiLt hNLt) hField hField).mp hSlotEq
      omega
    have hMidN : (mapFieldLoop owner layout length fieldCount field f s n).byte locN = s.byte locN := by
      have hAtN := ih hNLe locN
      rw [ite_eq_right hNotLt] at hAtN
      exact hAtN
    dsimp [mapFieldLoop, mapFieldStep]
    change (match (mapFieldLoop owner layout length fieldCount field f s n).byte locN with
      | some b => (mapFieldLoop owner layout length fieldCount field f s n).store locN (f b)
      | none => mapFieldLoop owner layout length fieldCount field f s n).byte loc = _
    rw [hMidN]
    by_cases hIsN : loc = locN
    · subst hIsN
      have hExists : ∃ i, i < n + 1 ∧ locN = ⟨owner, collectionSlot layout length fieldCount i field⟩ :=
        ⟨n, Nat.lt_succ_self n, rfl⟩
      rw [ite_eq_left hExists]
      cases hByte : s.byte locN with
      | none => exact hMidN.trans hByte
      | some b => exact Core.State.store_byte_written _ locN b (f b) (hMidN.trans hByte)
    · have hEquiv : (∃ i, i < n + 1 ∧ loc = ⟨owner, collectionSlot layout length fieldCount i field⟩) ↔
          (∃ i, i < n ∧ loc = ⟨owner, collectionSlot layout length fieldCount i field⟩) := by
        constructor
        · rintro ⟨i, hi, hEq⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hLt | rfl
          · exact ⟨i, hLt, hEq⟩
          · exact False.elim (hIsN hEq)
        · rintro ⟨i, hi, hEq⟩
          exact ⟨i, Nat.lt_succ_of_lt hi, hEq⟩
      cases hByte : s.byte locN with
      | none =>
        rw [ih hNLe loc]
        simp [hEquiv]
      | some b =>
        rw [Core.State.store_byte_other _ locN loc (f b) (Ne.symm hIsN), ih hNLe loc]
        simp [hEquiv]

theorem mapFieldInPlace_rep {owner : OwnerId} {layout : CollectionLayout}
    (hValid : layout.Valid) {length fieldCount field : Nat}
    (hField : field < fieldCount) (f : UInt8 → UInt8)
    {s : Core.State} {table : Nat → Nat → UInt8}
    (hRep : ByteCollectionRep s owner layout length fieldCount table) :
    ByteCollectionRep (mapFieldInPlace owner layout length fieldCount field f s)
      owner layout length fieldCount
      (fun i g => if g = field then f (table i g) else table i g) := by
  intro i hi g hg
  classical
  dsimp [mapFieldInPlace]
  rw [mapFieldLoop_byte hValid (Nat.le_refl _) hField f s]
  by_cases hGF : g = field
  · subst hGF
    rw [ite_eq_left ⟨i, hi, rfl⟩, ite_eq_left rfl, hRep i hi g hg]
    rfl
  · have hNot : ¬ ∃ j, j < length ∧
        (⟨owner, collectionSlot layout length fieldCount i g⟩ : ByteLocation) =
          ⟨owner, collectionSlot layout length fieldCount j field⟩ := by
      rintro ⟨j, hj, hLocEq⟩
      have hSlotEq := congrArg ByteLocation.offset hLocEq
      have hSame := (collectionSlot_eq_iff hValid hi hj hg hField).mp hSlotEq
      exact hGF hSame.2
    rw [ite_eq_right hNot, ite_eq_right hGF]
    exact hRep i hi g hg

theorem mapFieldInPlace_id {owner : OwnerId} {layout : CollectionLayout}
    (hValid : layout.Valid) {length fieldCount field : Nat}
    (hField : field < fieldCount) (s : Core.State) :
    ∀ loc, (mapFieldInPlace owner layout length fieldCount field id s).byte loc = s.byte loc := by
  classical
  intro loc
  dsimp [mapFieldInPlace]
  rw [mapFieldLoop_byte hValid (Nat.le_refl _) hField id s loc]
  split
  · simp
  · rfl

theorem mapFieldInPlace_fusion {owner : OwnerId} {layout : CollectionLayout}
    (hValid : layout.Valid) {length fieldCount field : Nat}
    (hField : field < fieldCount) (f g : UInt8 → UInt8) (s : Core.State) :
    ∀ loc, (mapFieldInPlace owner layout length fieldCount field g
        (mapFieldInPlace owner layout length fieldCount field f s)).byte loc =
      (mapFieldInPlace owner layout length fieldCount field (g ∘ f) s).byte loc := by
  classical
  intro loc
  dsimp [mapFieldInPlace]
  rw [mapFieldLoop_byte hValid (Nat.le_refl _) hField g _ loc,
    mapFieldLoop_byte hValid (Nat.le_refl _) hField f s loc,
    mapFieldLoop_byte hValid (Nat.le_refl _) hField (g ∘ f) s loc]
  split
  · simp [Option.map_map]
  · rfl

theorem mapFieldInPlace_disjoint_commute {owner : OwnerId} {layout : CollectionLayout}
    (hValid : layout.Valid) {length fieldCount f1 f2 : Nat}
    (hf1 : f1 < fieldCount) (hf2 : f2 < fieldCount) (hNe : f1 ≠ f2)
    (fn1 fn2 : UInt8 → UInt8) (s : Core.State) :
    ∀ loc, (mapFieldInPlace owner layout length fieldCount f2 fn2
        (mapFieldInPlace owner layout length fieldCount f1 fn1 s)).byte loc =
      (mapFieldInPlace owner layout length fieldCount f1 fn1
        (mapFieldInPlace owner layout length fieldCount f2 fn2 s)).byte loc := by
  classical
  intro loc
  dsimp [mapFieldInPlace]
  rw [mapFieldLoop_byte hValid (Nat.le_refl _) hf2 fn2 _ loc,
    mapFieldLoop_byte hValid (Nat.le_refl _) hf1 fn1 s loc,
    mapFieldLoop_byte hValid (Nat.le_refl _) hf1 fn1 _ loc,
    mapFieldLoop_byte hValid (Nat.le_refl _) hf2 fn2 s loc]
  by_cases hIn1 : ∃ i, i < length ∧ loc = ⟨owner, collectionSlot layout length fieldCount i f1⟩ <;>
    by_cases hIn2 : ∃ i, i < length ∧ loc = ⟨owner, collectionSlot layout length fieldCount i f2⟩
  · obtain ⟨i1, hi1, hEq1⟩ := hIn1
    obtain ⟨i2, hi2, hEq2⟩ := hIn2
    have hSlotEq : collectionSlot layout length fieldCount i1 f1 =
        collectionSlot layout length fieldCount i2 f2 :=
      congrArg ByteLocation.offset (hEq1.symm.trans hEq2)
    have hSame := (collectionSlot_eq_iff hValid hi1 hi2 hf1 hf2).mp hSlotEq
    exact False.elim (hNe hSame.2)
  · simp [hIn1, hIn2]
  · simp [hIn1, hIn2]
  · simp [hIn1, hIn2]

private theorem mapTwoFieldsLoop_byte {owner : OwnerId} {layout : CollectionLayout}
    (hValid : layout.Valid) {length fieldCount f1 f2 n : Nat}
    (hN : n ≤ length) (hf1 : f1 < fieldCount) (hf2 : f2 < fieldCount) (hNe : f1 ≠ f2)
    (fn1 fn2 : UInt8 → UInt8) (s : Core.State) (loc : ByteLocation) :
    (mapTwoFieldsLoop owner layout length fieldCount f1 f2 fn1 fn2 s n).byte loc =
      if ∃ i, i < n ∧ loc = ⟨owner, collectionSlot layout length fieldCount i f1⟩
      then (s.byte loc).map fn1
      else if ∃ i, i < n ∧ loc = ⟨owner, collectionSlot layout length fieldCount i f2⟩
      then (s.byte loc).map fn2
      else s.byte loc := by
  classical
  induction n generalizing loc with
  | zero => simp [mapTwoFieldsLoop]
  | succ n ih =>
    have hNLe : n ≤ length := Nat.le_of_succ_le hN
    have hNLt : n < length := hN
    let loc1 : ByteLocation := ⟨owner, collectionSlot layout length fieldCount n f1⟩
    let loc2 : ByteLocation := ⟨owner, collectionSlot layout length fieldCount n f2⟩
    have hLoc12Ne : loc1 ≠ loc2 := by
      intro hEq
      have hSame := (collectionSlot_eq_iff hValid hNLt hNLt hf1 hf2).mp
        (congrArg ByteLocation.offset hEq)
      exact hNe hSame.2
    have hNot1Lt : ¬ ∃ i, i < n ∧ loc1 = ⟨owner, collectionSlot layout length fieldCount i f1⟩ := by
      rintro ⟨i, hi, hEq⟩
      have hSame := (collectionSlot_eq_iff hValid hNLt (Nat.lt_trans hi hNLt) hf1 hf1).mp
        (congrArg ByteLocation.offset hEq)
      omega
    have hNot12 : ¬ ∃ i, i < n ∧ loc1 = ⟨owner, collectionSlot layout length fieldCount i f2⟩ := by
      rintro ⟨i, hi, hEq⟩
      have hSame := (collectionSlot_eq_iff hValid hNLt (Nat.lt_trans hi hNLt) hf1 hf2).mp
        (congrArg ByteLocation.offset hEq)
      exact hNe hSame.2
    have hNot21 : ¬ ∃ i, i < n + 1 ∧ loc2 = ⟨owner, collectionSlot layout length fieldCount i f1⟩ := by
      rintro ⟨i, hi, hEq⟩
      have hSame := (collectionSlot_eq_iff hValid hNLt (Nat.lt_of_lt_of_le hi hN) hf2 hf1).mp
        (congrArg ByteLocation.offset hEq)
      exact hNe hSame.2.symm
    have hNot2Lt : ¬ ∃ i, i < n ∧ loc2 = ⟨owner, collectionSlot layout length fieldCount i f2⟩ := by
      rintro ⟨i, hi, hEq⟩
      have hSame := (collectionSlot_eq_iff hValid hNLt (Nat.lt_trans hi hNLt) hf2 hf2).mp
        (congrArg ByteLocation.offset hEq)
      omega
    have hMid1 : (mapTwoFieldsLoop owner layout length fieldCount f1 f2 fn1 fn2 s n).byte loc1 = s.byte loc1 := by
      have hAt1 := ih hNLe loc1
      rw [ite_eq_right hNot1Lt, ite_eq_right hNot12] at hAt1
      exact hAt1
    have hMid2 : (mapTwoFieldsLoop owner layout length fieldCount f1 f2 fn1 fn2 s n).byte loc2 = s.byte loc2 := by
      have hNot21' : ¬ ∃ i, i < n ∧ loc2 = ⟨owner, collectionSlot layout length fieldCount i f1⟩ :=
        fun ⟨i, hi, hEq⟩ => hNot21 ⟨i, Nat.lt_succ_of_lt hi, hEq⟩
      have hAt2 := ih hNLe loc2
      rw [ite_eq_right hNot21', ite_eq_right hNot2Lt] at hAt2
      exact hAt2
    dsimp [mapTwoFieldsLoop, mapTwoFieldsStep]
    change (let s1 := match (mapTwoFieldsLoop owner layout length fieldCount f1 f2 fn1 fn2 s n).byte loc1 with
        | some b => (mapTwoFieldsLoop owner layout length fieldCount f1 f2 fn1 fn2 s n).store loc1 (fn1 b)
        | none => mapTwoFieldsLoop owner layout length fieldCount f1 f2 fn1 fn2 s n
      match s1.byte loc2 with
      | some b => s1.store loc2 (fn2 b)
      | none => s1).byte loc = _
    dsimp only
    rw [hMid1]
    have hS1Byte2 : (match s.byte loc1 with
        | some b => (mapTwoFieldsLoop owner layout length fieldCount f1 f2 fn1 fn2 s n).store loc1 (fn1 b)
        | none => mapTwoFieldsLoop owner layout length fieldCount f1 f2 fn1 fn2 s n).byte loc2 =
        s.byte loc2 := by
      cases s.byte loc1 with
      | none => exact hMid2
      | some b =>
        rw [Core.State.store_byte_other _ loc1 loc2 (fn1 b) hLoc12Ne]
        exact hMid2
    have hS1ByteLoc : (match s.byte loc1 with
        | some b => (mapTwoFieldsLoop owner layout length fieldCount f1 f2 fn1 fn2 s n).store loc1 (fn1 b)
        | none => mapTwoFieldsLoop owner layout length fieldCount f1 f2 fn1 fn2 s n).byte loc =
        if loc = loc1 then (s.byte loc).map fn1
        else if ∃ i, i < n ∧ loc = ⟨owner, collectionSlot layout length fieldCount i f1⟩ then (s.byte loc).map fn1
        else if ∃ i, i < n ∧ loc = ⟨owner, collectionSlot layout length fieldCount i f2⟩ then (s.byte loc).map fn2
        else s.byte loc := by
      by_cases hIs1 : loc = loc1
      · subst hIs1
        rw [ite_eq_left rfl]
        cases hB1 : s.byte loc1 with
        | none => exact hMid1.trans hB1
        | some b1 => exact Core.State.store_byte_written _ loc1 b1 (fn1 b1) (hMid1.trans hB1)
      · rw [ite_eq_right hIs1]
        cases hB1 : s.byte loc1 with
        | none => exact ih hNLe loc
        | some b1 =>
          rw [Core.State.store_byte_other _ loc1 loc (fn1 b1) (Ne.symm hIs1)]
          exact ih hNLe loc
    rw [hS1Byte2]
    by_cases hIs2 : loc = loc2
    · subst hIs2
      have hEx2 : ∃ i, i < n + 1 ∧ loc2 = ⟨owner, collectionSlot layout length fieldCount i f2⟩ :=
        ⟨n, Nat.lt_succ_self n, rfl⟩
      rw [ite_eq_right hNot21, ite_eq_left hEx2]
      cases hB2 : s.byte loc2 with
      | none =>
        rw [hS1ByteLoc, ite_eq_right hLoc12Ne.symm,
          ite_eq_right (fun ⟨i, hi, hEq⟩ => hNot21 ⟨i, Nat.lt_succ_of_lt hi, hEq⟩),
          ite_eq_right hNot2Lt]
        exact hB2
      | some b2 =>
        have hS1At2 : (match s.byte loc1 with
            | some b => (mapTwoFieldsLoop owner layout length fieldCount f1 f2 fn1 fn2 s n).store loc1 (fn1 b)
            | none => mapTwoFieldsLoop owner layout length fieldCount f1 f2 fn1 fn2 s n).byte loc2 = some b2 :=
          hS1Byte2.trans hB2
        exact Core.State.store_byte_written _ loc2 b2 (fn2 b2) hS1At2
    · have hEquiv1 : (∃ i, i < n + 1 ∧ loc = ⟨owner, collectionSlot layout length fieldCount i f1⟩) ↔
          (loc = loc1 ∨ ∃ i, i < n ∧ loc = ⟨owner, collectionSlot layout length fieldCount i f1⟩) := by
        constructor
        · rintro ⟨i, hi, hEq⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hLt | rfl
          · exact Or.inr ⟨i, hLt, hEq⟩
          · exact Or.inl hEq
        · rintro (rfl | ⟨i, hi, hEq⟩)
          · exact ⟨n, Nat.lt_succ_self n, rfl⟩
          · exact ⟨i, Nat.lt_succ_of_lt hi, hEq⟩
      have hEquiv2 : (∃ i, i < n + 1 ∧ loc = ⟨owner, collectionSlot layout length fieldCount i f2⟩) ↔
          (∃ i, i < n ∧ loc = ⟨owner, collectionSlot layout length fieldCount i f2⟩) := by
        constructor
        · rintro ⟨i, hi, hEq⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hLt | rfl
          · exact ⟨i, hLt, hEq⟩
          · exact False.elim (hIs2 hEq)
        · rintro ⟨i, hi, hEq⟩
          exact ⟨i, Nat.lt_succ_of_lt hi, hEq⟩
      cases hB2 : s.byte loc2 with
      | none =>
        rw [hS1ByteLoc]
        simp only [hEquiv1, hEquiv2]
        by_cases h1 : loc = loc1 <;> simp [h1]
      | some b2 =>
        rw [Core.State.store_byte_other _ loc2 loc (fn2 b2) (Ne.symm hIs2), hS1ByteLoc]
        simp only [hEquiv1, hEquiv2]
        by_cases h1 : loc = loc1 <;> simp [h1]

theorem mapTwoFieldsInPlace_fusion {owner : OwnerId} {layout : CollectionLayout}
    (hValid : layout.Valid) {length fieldCount f1 f2 : Nat}
    (hf1 : f1 < fieldCount) (hf2 : f2 < fieldCount) (hNe : f1 ≠ f2)
    (fn1 fn2 : UInt8 → UInt8) (s : Core.State) :
    ∀ loc, (mapTwoFieldsInPlace owner layout length fieldCount f1 f2 fn1 fn2 s).byte loc =
      (mapFieldInPlace owner layout length fieldCount f2 fn2
        (mapFieldInPlace owner layout length fieldCount f1 fn1 s)).byte loc := by
  classical
  intro loc
  dsimp [mapTwoFieldsInPlace, mapFieldInPlace]
  rw [mapTwoFieldsLoop_byte hValid (Nat.le_refl _) hf1 hf2 hNe fn1 fn2 s loc,
    mapFieldLoop_byte hValid (Nat.le_refl _) hf2 fn2 _ loc,
    mapFieldLoop_byte hValid (Nat.le_refl _) hf1 fn1 s loc]
  by_cases hIn1 : ∃ i, i < length ∧ loc = ⟨owner, collectionSlot layout length fieldCount i f1⟩ <;>
    by_cases hIn2 : ∃ i, i < length ∧ loc = ⟨owner, collectionSlot layout length fieldCount i f2⟩
  · obtain ⟨i1, hi1, hEq1⟩ := hIn1
    obtain ⟨i2, hi2, hEq2⟩ := hIn2
    have hSame := (collectionSlot_eq_iff hValid hi1 hi2 hf1 hf2).mp
      (congrArg ByteLocation.offset (hEq1.symm.trans hEq2))
    exact False.elim (hNe hSame.2)
  · simp [hIn1, hIn2]
  · simp [hIn1, hIn2]
  · simp [hIn1, hIn2]

theorem mapFieldInPlace_preserves_other_owner {owner other : OwnerId}
    {layout : CollectionLayout} (hValid : layout.Valid)
    {length fieldCount field : Nat} (hField : field < fieldCount)
    (f : UInt8 → UInt8) (s : Core.State) (hNe : other ≠ owner) (off : Nat) :
    (mapFieldInPlace owner layout length fieldCount field f s).byte ⟨other, off⟩ =
      s.byte ⟨other, off⟩ := by
  classical
  dsimp [mapFieldInPlace]
  rw [mapFieldLoop_byte hValid (Nat.le_refl _) hField f s]
  have hNot : ¬ ∃ i, i < length ∧
      (⟨other, off⟩ : ByteLocation) = ⟨owner, collectionSlot layout length fieldCount i field⟩ := by
    rintro ⟨i, _, hEq⟩
    exact hNe (congrArg ByteLocation.allocation hEq)
  rw [ite_eq_right hNot]

private theorem map_fold_fusion_loop {owner : OwnerId} {layout : CollectionLayout}
    (hValid : layout.Valid) {length fieldCount field n : Nat}
    (hN : n ≤ length) (hField : field < fieldCount) (f : UInt8 → UInt8)
    {β : Type} (init : β) (step : β → UInt8 → β) (s : Core.State) :
    foldFieldLoop owner layout length fieldCount field step
        (mapFieldInPlace owner layout length fieldCount field f s) init n =
      foldFieldLoop owner layout length fieldCount field (fun acc b => step acc (f b)) s init n := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    have hNLe : n ≤ length := Nat.le_of_succ_le hN
    have hNLt : n < length := hN
    dsimp [foldFieldLoop, foldFieldStep]
    rw [ih hNLe]
    dsimp [mapFieldInPlace]
    rw [mapFieldLoop_byte hValid (Nat.le_refl _) hField f s]
    rw [ite_eq_left ⟨n, hNLt, rfl⟩]
    cases s.byte ⟨owner, collectionSlot layout length fieldCount n field⟩ <;> rfl

theorem map_fold_fusion {owner : OwnerId} {layout : CollectionLayout}
    (hValid : layout.Valid) {length fieldCount field : Nat}
    (hField : field < fieldCount) (f : UInt8 → UInt8)
    {β : Type} (init : β) (step : β → UInt8 → β) (s : Core.State) :
    foldField owner layout length fieldCount field init step
        (mapFieldInPlace owner layout length fieldCount field f s) =
      foldField owner layout length fieldCount field init (fun acc b => step acc (f b)) s :=
  map_fold_fusion_loop hValid (Nat.le_refl _) hField f init step s

def composeStages : List (UInt8 → UInt8) → UInt8 → UInt8
  | [] => id
  | f :: rest => composeStages rest ∘ f

def runPipeline (owner : OwnerId) (layout : CollectionLayout)
    (length fieldCount field : Nat) : List (UInt8 → UInt8) → Core.State → Core.State
  | [], s => s
  | f :: rest, s =>
    runPipeline owner layout length fieldCount field rest
      (mapFieldInPlace owner layout length fieldCount field f s)

theorem runPipeline_eq_single_pass {owner : OwnerId} {layout : CollectionLayout}
    (hValid : layout.Valid) {length fieldCount field : Nat}
    (hField : field < fieldCount) (stages : List (UInt8 → UInt8)) (s : Core.State) :
    ∀ loc, (runPipeline owner layout length fieldCount field stages s).byte loc =
      (mapFieldInPlace owner layout length fieldCount field (composeStages stages) s).byte loc := by
  induction stages generalizing s with
  | nil =>
    intro loc
    exact (mapFieldInPlace_id hValid hField s loc).symm
  | cons f rest ih =>
    intro loc
    dsimp [runPipeline, composeStages]
    rw [ih (mapFieldInPlace owner layout length fieldCount field f s) loc]
    exact mapFieldInPlace_fusion hValid hField f (composeStages rest) s loc

private theorem foldFieldLoop_byte_congr {owner : OwnerId} {layout : CollectionLayout}
    {length fieldCount field n : Nat} {β : Type} (step : β → UInt8 → β)
    (init : β) {s₁ s₂ : Core.State}
    (hEq : ∀ loc, s₁.byte loc = s₂.byte loc) :
    foldFieldLoop owner layout length fieldCount field step s₁ init n =
      foldFieldLoop owner layout length fieldCount field step s₂ init n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [foldFieldLoop, foldFieldStep]
    rw [ih, hEq ⟨owner, collectionSlot layout length fieldCount n field⟩]

theorem runPipeline_fold_deforestation {owner : OwnerId} {layout : CollectionLayout}
    (hValid : layout.Valid) {length fieldCount field : Nat}
    (hField : field < fieldCount) (stages : List (UInt8 → UInt8))
    {β : Type} (init : β) (step : β → UInt8 → β) (s : Core.State) :
    foldField owner layout length fieldCount field init step
        (runPipeline owner layout length fieldCount field stages s) =
      foldField owner layout length fieldCount field init
        (fun acc b => step acc (composeStages stages b)) s := by
  dsimp [foldField]
  rw [foldFieldLoop_byte_congr step init (runPipeline_eq_single_pass hValid hField stages s)]
  exact map_fold_fusion hValid hField (composeStages stages) init step s

end Aethel.CategoricalFusion
