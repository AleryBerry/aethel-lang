import Aethel.Machine
import Aethel.ResourceCheck
import Aethel.Representation
import Aethel.CacheLayout

namespace Aethel.DynamicMemory

open Aethel Aethel.Core Aethel.CacheLayout

/-!
## Compiler-Managed Dynamic Heap Memory & Layout-Polymorphic Growth (Phase 8 Lean Gate)

Establishes why Aethel needs NO user-facing `Allocator` parameter API:
1. Geometric growth (`growCap`) guarantees strict capacity increase (`cap < growCap cap`)
   and bounded `2×` overhead at full capacity.
2. Reallocation / drop is gated by `checkUnreserved s owner = true ↔ s.Unreserved owner`.
   Any live view/slice blocks `.destroy`, preventing dangling pointers across growth.
3. Three-way layout-polymorphic dynamic vectors (`AoS`, `DynSoA`, `DynAoSoA`) support
   zero-allocation Perceus in-place `push` (`len < cap`) and representation-preserving
   migration on growth (`len = cap`), preserving 64B cache-line tile alignment.
4. Compiler-managed affine scope exit (`emitScopeDrop`) guarantees deallocation for
   non-moved locals, preservation across moves, and impossibility of double-free.
-/

def initialCap : Nat := 8

def growCap (cap : Nat) : Nat :=
  if cap == 0 then initialCap else cap * 2

theorem growCap_gt (cap : Nat) : cap < growCap cap := by
  by_cases hZero : cap = 0 <;> simp [growCap, initialCap, hZero] <;> omega

theorem growCap_pos (cap : Nat) : 0 < growCap cap := by
  have h := growCap_gt cap
  omega

theorem growCap_bounded_overhead {len cap : Nat} (hFull : len = cap) (hPos : 0 < len) :
    growCap cap = 2 * len := by
  subst hFull
  have hNe : (len == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro hBeq
    have : len = 0 := beq_iff_eq.mp hBeq
    omega
  simp [growCap, hNe]
  omega

def aosoaTileCap (tileWidth elemCap : Nat) : Nat :=
  (elemCap + tileWidth - 1) / tileWidth

theorem aosoaTileCap_covers {tileWidth elemCap : Nat} (hw : 0 < tileWidth) :
    elemCap ≤ aosoaTileCap tileWidth elemCap * tileWidth := by
  unfold aosoaTileCap
  have hMod : (elemCap + tileWidth - 1) % tileWidth < tileWidth :=
    Nat.mod_lt _ hw
  have hEq := Nat.div_add_mod (elemCap + tileWidth - 1) tileWidth
  rw [Nat.mul_comm tileWidth _] at hEq
  omega

theorem aosoaDynTile_64B_aligned (baseAddr tileBytes tile : Nat)
    (hBase : baseAddr % 64 = 0) (hTile : tileBytes % 64 = 0) :
    (baseAddr + tile * tileBytes) % 64 = 0 := by
  have h1 : 64 ∣ baseAddr := Nat.dvd_of_mod_eq_zero hBase
  have h2 : 64 ∣ tileBytes := Nat.dvd_of_mod_eq_zero hTile
  have h3 : 64 ∣ tile * tileBytes := Nat.dvd_trans h2 (Nat.dvd_mul_left tileBytes tile)
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add h1 h3)

/-! ## Borrow-Checked Reallocation & Drop Gate -/

def checkUnreserved (s : Core.State) (owner : OwnerId) : Bool :=
  s.views.all (fun v => v.location.allocation != owner)

theorem checkUnreserved_correct (s : Core.State) (owner : OwnerId) :
    checkUnreserved s owner = true ↔ s.Unreserved owner := by
  unfold checkUnreserved Core.State.Unreserved
  rw [List.all_eq_true]
  constructor
  · intro h v hv
    have hBne := h v hv
    intro hEq
    simp [hEq] at hBne
  · intro h v hv
    have hNe := h v hv
    simp [bne_iff_ne, hNe]

theorem realloc_blocked_by_active_view {s : Core.State} {owner : OwnerId} {v : View}
    (hv : v ∈ s.views) (hOwn : v.location.allocation = owner) :
    checkUnreserved s owner = false ∧ ¬ ∃ s', Core.Step s (.destroy owner) s' := by
  constructor
  · apply Bool.eq_false_iff.mpr
    intro hTrue
    have hUnres := (checkUnreserved_correct s owner).mp hTrue
    exact hUnres v hv hOwn
  · rintro ⟨s', hStep⟩
    cases hStep with
    | destroy _ hUnres => exact hUnres v hv hOwn

/-! ## Dynamic Vector Layout-Polymorphic Representation & Perceus In-Place Push -/

def soaDynSlot (cap element field : Nat) : Nat :=
  soaSlot cap element field

def dynVecSlot (layout : CollectionLayout) (cap fieldCount element field : Nat) : Nat :=
  collectionSlot layout cap fieldCount element field

theorem dynVecSlot_eq_iff {layout : CollectionLayout} (hValid : layout.Valid)
    {len cap fieldCount i j f g : Nat}
    (hCap : len ≤ cap) (hi : i < len) (hj : j < len) (hf : f < fieldCount) (hg : g < fieldCount) :
    dynVecSlot layout cap fieldCount i f = dynVecSlot layout cap fieldCount j g ↔ i = j ∧ f = g :=
  collectionSlot_eq_iff hValid (Nat.lt_of_lt_of_le hi hCap) (Nat.lt_of_lt_of_le hj hCap) hf hg

def DynVecRep (layout : CollectionLayout) (table : ScalarTable) (store : SlotStore)
    (len cap fieldCount : Nat) : Prop :=
  len ≤ cap ∧
  ∀ i, i < len → ∀ f, f < fieldCount → store (dynVecSlot layout cap fieldCount i f) = table i f

def extendRow (table : ScalarTable) (len : Nat) (row : Nat → Nat) : ScalarTable :=
  fun i f => if i = len then row f else table i f

def pushSlotInPlaceAux (layout : CollectionLayout) (cap fieldCount len : Nat) (row : Nat → Nat) :
    Nat → SlotStore → SlotStore
  | 0, store => store
  | k + 1, store =>
    let rest := pushSlotInPlaceAux layout cap fieldCount len row k store
    writeSlot rest (dynVecSlot layout cap fieldCount len k) (row k)

def pushSlotInPlace (layout : CollectionLayout) (cap fieldCount len : Nat) (row : Nat → Nat)
    (store : SlotStore) : SlotStore :=
  pushSlotInPlaceAux layout cap fieldCount len row fieldCount store

private theorem writeRow_target {layout : CollectionLayout} (hValid : layout.Valid)
    {cap fieldCount len k : Nat} (hk : k ≤ fieldCount) (hLen : len < cap)
    (row : Nat → Nat) (store : SlotStore) :
    ∀ f, f < k →
      pushSlotInPlaceAux layout cap fieldCount len row k store
        (dynVecSlot layout cap fieldCount len f) = row f := by
  induction k with
  | zero => intro f hf; omega
  | succ k ih =>
    intro f hf
    unfold pushSlotInPlaceAux
    have hkLe : k ≤ fieldCount := Nat.le_of_succ_le hk
    have hkLt : k < fieldCount := hk
    by_cases hEq : f = k
    · subst hEq
      simp [writeSlot]
    · have hLt : f < k := by omega
      have hNeSlot : dynVecSlot layout cap fieldCount len f ≠
          dynVecSlot layout cap fieldCount len k := by
        intro hSlot
        have hPair := (dynVecSlot_eq_iff hValid (Nat.succ_le_of_lt hLen)
          (Nat.lt_succ_self len) (Nat.lt_succ_self len) (Nat.lt_of_lt_of_le hLt hkLe) hkLt).mp hSlot
        exact hEq hPair.2
      simp [writeSlot, hNeSlot, ih hkLe f hLt]

private theorem writeRow_other {layout : CollectionLayout} (hValid : layout.Valid)
    {cap fieldCount len k : Nat} (hk : k ≤ fieldCount) (hLen : len < cap)
    (row : Nat → Nat) (store : SlotStore) {i f : Nat}
    (hi : i < cap) (hf : f < fieldCount) (hOther : i ≠ len) :
    pushSlotInPlaceAux layout cap fieldCount len row k store
      (dynVecSlot layout cap fieldCount i f) = store (dynVecSlot layout cap fieldCount i f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have different : dynVecSlot layout cap fieldCount i f ≠
        dynVecSlot layout cap fieldCount len k :=
      fun same => hOther ((collectionSlot_eq_iff hValid hi hLen hf hk).mp same).1
    simp [pushSlotInPlaceAux, writeSlot, different, ih (Nat.le_of_succ_le hk)]

theorem dynPush_inPlace_preserves_rep {layout : CollectionLayout} (hValid : layout.Valid)
    {table : ScalarTable} {store : SlotStore} {len cap fieldCount : Nat}
    (hRep : DynVecRep layout table store len cap fieldCount)
    (hRoom : len < cap) (row : Nat → Nat) :
    DynVecRep layout (extendRow table len row)
      (pushSlotInPlace layout cap fieldCount len row store) (len + 1) cap fieldCount := by
  refine ⟨hRoom, ?_⟩
  intro i hi f hf
  by_cases hIsNew : i = len
  · subst hIsNew
    simp only [extendRow, ite_true, pushSlotInPlace]
    exact writeRow_target hValid (Nat.le_refl _) hRoom row store f hf
  · have hLt : i < len := by omega
    have hNe : i ≠ len := hIsNew
    simp only [extendRow, ite_eq_right hNe, pushSlotInPlace]
    rw [writeRow_other hValid (Nat.le_refl _) hRoom row store (Nat.lt_trans hLt hRoom) hf hNe]
    exact hRep.2 i hLt f hf

theorem dynPush_inPlace_zero_alloc (s : Core.State) {loc : ByteLocation} {v : UInt8} :
    (s.store loc v).issued = s.issued := rfl

/-! ## Reallocating Growth Across AoS, DynSoA, and DynAoSoA -/

def migrateRowAux (layout : CollectionLayout) (oldCap newCap fieldCount rowIdx : Nat)
    (oldStore : SlotStore) : Nat → SlotStore → SlotStore :=
  pushSlotInPlaceAux layout newCap fieldCount rowIdx
    (fun f => oldStore (dynVecSlot layout oldCap fieldCount rowIdx f))

def migrateStoreAux (layout : CollectionLayout) (oldCap newCap fieldCount : Nat)
    (oldStore : SlotStore) : Nat → SlotStore → SlotStore
  | 0, dst => dst
  | r + 1, dst =>
    let rest := migrateStoreAux layout oldCap newCap fieldCount oldStore r dst
    migrateRowAux layout oldCap newCap fieldCount r oldStore fieldCount rest

def migrateStore (layout : CollectionLayout) (oldCap newCap fieldCount len : Nat)
    (oldStore : SlotStore) (freshDst : SlotStore) : SlotStore :=
  migrateStoreAux layout oldCap newCap fieldCount oldStore len freshDst

private theorem migrateStoreAux_preserves {layout : CollectionLayout} (hValid : layout.Valid)
    {oldCap newCap fieldCount count : Nat} (hBound : count ≤ newCap)
    (oldStore dst : SlotStore) :
    ∀ i, i < count → ∀ f, f < fieldCount →
      migrateStoreAux layout oldCap newCap fieldCount oldStore count dst
        (dynVecSlot layout newCap fieldCount i f) =
        oldStore (dynVecSlot layout oldCap fieldCount i f) := by
  induction count with
  | zero => intro i hi; omega
  | succ r ih =>
    intro i hi f hf
    unfold migrateStoreAux
    have hrNew : r < newCap := hBound
    have hrLe : r ≤ newCap := Nat.le_of_lt hrNew
    have hiNew : i < newCap := Nat.lt_of_lt_of_le hi hBound
    by_cases hEq : i = r
    · subst hEq
      exact writeRow_target hValid (Nat.le_refl _) hrNew _ _ f hf
    · have hiLt : i < r := by omega
      rw [migrateRowAux, writeRow_other hValid (Nat.le_refl _) hrNew _ _ hiNew hf hEq]
      exact ih hrLe i hiLt f hf

theorem migrateStore_preserves_rep {layout : CollectionLayout} (hValid : layout.Valid)
    {table : ScalarTable} {oldStore freshDst : SlotStore} {len cap fieldCount : Nat}
    (hRep : DynVecRep layout table oldStore len cap fieldCount) :
    DynVecRep layout table
      (migrateStore layout cap (growCap cap) fieldCount len oldStore freshDst)
      len (growCap cap) fieldCount := by
  have hNewCap : len ≤ growCap cap := Nat.le_of_lt (Nat.lt_of_le_of_lt hRep.1 (growCap_gt cap))
  refine ⟨hNewCap, ?_⟩
  intro i hi f hf
  unfold migrateStore
  rw [migrateStoreAux_preserves hValid hNewCap oldStore freshDst i hi f hf]
  exact hRep.2 i hi f hf

/-! ## Allocation, Reallocation Retirement, and Compiler-Managed Scope Drop -/

theorem State.addAllocation_self (s : Core.State) (owner : OwnerId) (bytes : List UInt8) :
    (s.addAllocation owner bytes).allocation owner = some ⟨owner, bytes⟩ := by
  simp [Core.State.addAllocation, Core.State.allocation]

theorem State.removeOwner_self (s : Core.State) (owner : OwnerId) :
    (s.removeOwner owner).allocation owner = none := by
  simp only [Core.State.removeOwner, Core.State.allocation]
  rw [List.find?_eq_none]
  intro a ha hEq
  rw [List.mem_filter] at ha
  have hBne := ha.2
  simp only [bne_iff_ne, ne_eq] at hBne
  simp only [beq_iff_eq] at hEq
  exact hBne hEq

theorem dynRealloc_step_retires_old_and_frames_others
    {s : Core.State} {oldOwner newOwner : OwnerId} {oldBytes newBytes : List UInt8}
    (hFresh : newOwner ∉ s.issued)
    (hOldFound : s.allocation oldOwner = some ⟨oldOwner, oldBytes⟩)
    (hUnres : s.Unreserved oldOwner)
    (hNe : newOwner ≠ oldOwner) :
    let s1 := s.addAllocation newOwner newBytes
    let s2 := s1.removeOwner oldOwner
    Core.Runs s [.alloc newOwner newBytes, .destroy oldOwner] s2 ∧
    s2.allocation oldOwner = none ∧
    s2.allocation newOwner = some ⟨newOwner, newBytes⟩ ∧
    (∀ other, other ≠ oldOwner → other ≠ newOwner → s2.allocation other = s.allocation other) := by
  have hS1Old : (s.addAllocation newOwner newBytes).allocation oldOwner = some ⟨oldOwner, oldBytes⟩ := by
    have hNeBool : (newOwner == oldOwner) = false := beq_false_of_ne hNe
    simpa [Core.State.addAllocation, Core.State.allocation, hNeBool] using hOldFound
  have hS1Unres : (s.addAllocation newOwner newBytes).Unreserved oldOwner := by
    simpa [Core.State.addAllocation, Core.State.Unreserved] using hUnres
  have hRun : Core.Runs s [.alloc newOwner newBytes, .destroy oldOwner]
      ((s.addAllocation newOwner newBytes).removeOwner oldOwner) :=
    Core.Runs.cons (Core.Step.alloc hFresh)
      (Core.Runs.cons (Core.Step.destroy hS1Old hS1Unres) Core.Runs.nil)
  refine ⟨hRun, State.removeOwner_self _ oldOwner, ?_, ?_⟩
  · have hAdd := State.addAllocation_self s newOwner newBytes
    rw [Representation.State.removeOwner_allocation_other (s.addAllocation newOwner newBytes) oldOwner newOwner hNe]
    exact hAdd
  · intro other hNeOld hNeNew
    rw [Representation.State.removeOwner_allocation_other (s.addAllocation newOwner newBytes) oldOwner other hNeOld]
    have hNeBool : (newOwner == other) = false := beq_false_of_ne hNeNew.symm
    simp [Core.State.addAllocation, Core.State.allocation, hNeBool]

def emitScopeDrop (moved : Bool) (owner : OwnerId) : Program :=
  if moved then [] else [.destroy owner]

theorem autoScopeDrop_local_frees {s : Core.State} {owner : OwnerId} {a : Allocation}
    (hFound : s.allocation owner = some a) (hUnres : s.Unreserved owner) :
    Core.Runs s (emitScopeDrop false owner) (s.removeOwner owner) ∧
    (s.removeOwner owner).allocation owner = none := by
  exact ⟨Core.Runs.cons (Core.Step.destroy hFound hUnres) Core.Runs.nil,
    State.removeOwner_self s owner⟩

theorem autoScopeDrop_moved_preserves (s : Core.State) (owner : OwnerId) :
    Core.Runs s (emitScopeDrop true owner) s := by
  exact Core.Runs.nil

theorem autoScopeDrop_no_double_free (s : Core.State) (owner : OwnerId) :
    ¬ ∃ s'', Core.Step (s.removeOwner owner) (.destroy owner) s'' := by
  rintro ⟨s'', hStep⟩
  cases hStep with
  | destroy hFound _ =>
    rw [State.removeOwner_self s owner] at hFound
    cases hFound

end Aethel.DynamicMemory
