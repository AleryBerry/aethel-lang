import Aethel.BranchFacts
import Aethel.ByteLoans
import Aethel.CacheLayout

namespace Aethel.CacheLayout

open Core Functional Structured

/-- A fixed byte collection whose fields have separate physical slots. -/
structure ByteCollection where
  owner : OwnerId
  layout : CollectionLayout
  length : Nat
  fields : Nat
  valid : layout.Valid

def ByteCollection.cellOffset (collection : ByteCollection) (row : Nat) (field : Fin collection.fields) : Nat :=
  collectionSlot collection.layout collection.length collection.fields row field.val

def ByteCollection.entry (collection : ByteCollection) (table : Nat → Nat → UInt8) : Program :=
  byteRegionEntry collection.owner (collection.layout.encodeBytes collection.length collection.fields table)

theorem ByteCollection.entry_correct (collection : ByteCollection) {table : Nat → Nat → UInt8} {state : State}
    (ran : Core.run {} (collection.entry table) = some state) :
    ByteCollectionRep state collection.owner collection.layout collection.length collection.fields table ∧
      state.views = [] ∧ ∀ row, row < collection.length → ∀ field : Fin collection.fields,
        state.handle (collection.cellOffset row field) =
          some ⟨⟨collection.owner, collection.cellOffset row field⟩, .exclusive⟩ := by
  obtain ⟨allocated, views, handles⟩ := byteRegionEntry_exact _ _ ran
  refine ⟨?_, views, ?_⟩
  · intro row within field declared
    simpa [State.byte, State.allocation, allocated, bind] using
      collection.layout.encodeBytes_cell collection.valid table within declared
  · intro row within field
    have fits := collectionSlot_fits collection.valid within field.isLt
    rw [handles, CollectionLayout.encodeBytes_length]
    exact ite_eq_left (show collection.cellOffset row field < _ from fits)

/-- Select the handle for the actual slot. A reachable out-of-bounds arm
has no execution and makes resource verification fail. -/
def ByteCollection.dispatch (collection : ByteCollection) (index : Term ctx .byte)
    (field : Fin collection.fields) (body : HandleId → Code ctx) : Code ctx :=
  Code.dispatchByte index fun row =>
    if row.val < collection.length then body (collection.cellOffset row.val field) else .unreachable

theorem ByteCollection.dispatch_correct (collection : ByteCollection) (index : Term ctx .byte)
    (field : Fin collection.fields) (body : HandleId → Code ctx)
    {env : Env ctx} {state final : State} {trace : Program} :
    Executes env state (collection.dispatch index field body) trace final ↔
      (index.eval env : UInt8).toNat < collection.length ∧
        Executes env state (body (collection.cellOffset (index.eval env : UInt8).toNat field)) trace final := by
  rw [dispatch, Code.dispatchByte_correct]
  change Executes env state
    (if (index.eval env : UInt8).toNat < collection.length then
      body (collection.cellOffset (index.eval env : UInt8).toNat field) else .unreachable) trace final ↔ _
  split
  · simp_all
  · constructor
    · intro ran
      cases ran
    · rintro ⟨within, _⟩
      contradiction

structure IndexedCell (collection : ByteCollection) (ctx : List Ty) where
  index : Term ctx .byte
  field : Fin collection.fields
  mode : AccessMode

def IndexedCell.location {collection : ByteCollection} (request : IndexedCell collection ctx) (env : Env ctx) :
    ByteLocation :=
  ⟨collection.owner, collection.cellOffset (request.index.eval env : UInt8).toNat request.field⟩

private def checkIndexBound (facts : BranchFacts ctx) (index : Term ctx .byte) (bound : Nat) : Bool :=
  if 256 ≤ bound then true
  else match index with
  | .byte value => decide (value.toNat < bound)
  | _ => facts.resolve (.byteLt index (.byte (UInt8.ofNat bound))) == some true

private theorem checkIndexBound_sound {facts : BranchFacts ctx} {env : Env ctx}
    {index : Term ctx .byte} {bound : Nat} (valid : facts.Valid env)
    (checked : checkIndexBound facts index bound = true) :
    (index.eval env : UInt8).toNat < bound := by
  unfold checkIndexBound at checked
  split at checked
  · have within := (index.eval env : UInt8).toNat_lt
    omega
  · rename_i short
    split at checked
    · exact of_decide_eq_true checked
    · have evaluated := BranchFacts.resolve_sound valid (beq_iff_eq.mp checked)
      change decide ((index.eval env : UInt8).toNat < (UInt8.ofNat bound).toNat) = true at evaluated
      have within : bound < 256 := by omega
      rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt within] at evaluated
      exact of_decide_eq_true evaluated

private def checkIndexDisjoint (facts : BranchFacts ctx) : Term ctx .byte → Term ctx .byte → Bool
  | .byte a, .byte b => decide (a ≠ b)
  | a, b => facts.resolve (.byteEq a b) == some false

private theorem checkIndexDisjoint_sound {facts : BranchFacts ctx} {env : Env ctx}
    {left right : Term ctx .byte} (valid : facts.Valid env)
    (checked : checkIndexDisjoint facts left right = true) :
    (left.eval env : UInt8).toNat ≠ (right.eval env : UInt8).toNat := by
  intro same
  have equal := UInt8.toNat_inj.mp same
  unfold checkIndexDisjoint at checked
  split at checked
  · exact (of_decide_eq_true checked) equal
  · have evaluated := BranchFacts.resolve_sound valid (beq_iff_eq.mp checked)
    change ((left.eval env : UInt8) == right.eval env) = false at evaluated
    simp [equal] at evaluated

private def checkCellPair {collection : ByteCollection} (facts : BranchFacts ctx)
    (left right : IndexedCell collection ctx) : Bool :=
  decide (left.mode.Compatible right.mode ∨ left.field ≠ right.field) ||
    checkIndexDisjoint facts left.index right.index

private theorem checkCellPair_sound {collection : ByteCollection} {facts : BranchFacts ctx} {env : Env ctx}
    {left right : IndexedCell collection ctx} (valid : facts.Valid env)
    (leftBound : (left.index.eval env : UInt8).toNat < collection.length)
    (rightBound : (right.index.eval env : UInt8).toNat < collection.length)
    (checked : checkCellPair facts left right = true) :
    left.location env ≠ right.location env ∨ left.mode.Compatible right.mode := by
  simp only [checkCellPair, Bool.or_eq_true, decide_eq_true_eq] at checked
  rcases or_assoc.mp checked with shared | apart
  · exact .inr shared
  · apply Or.inl
    intro collision
    obtain ⟨sameIndex, sameField⟩ := (collectionSlot_eq_iff collection.valid leftBound rightBound
      left.field.isLt right.field.isLt).mp (congrArg ByteLocation.offset collision)
    rcases apart with fields | indices
    · exact fields (Fin.ext sameField)
    · exact checkIndexDisjoint_sound valid indices sameIndex

/-- Checks lexical index facts and field separation before resolving any
physical address. Borrowed bytes additionally need caller availability. -/
def checkIndexedBorrow {collection : ByteCollection} (facts : BranchFacts ctx)
    (requests : List (IndexedCell collection ctx)) : Bool :=
  requests.all (fun request => checkIndexBound facts request.index collection.length) &&
    decide (requests.Pairwise (fun left right => checkCellPair facts left right = true))

def IndexedBorrowValid {collection : ByteCollection} (env : Env ctx)
    (requests : List (IndexedCell collection ctx)) : Prop :=
  (∀ request ∈ requests, (request.index.eval env : UInt8).toNat < collection.length) ∧
    requests.Pairwise (fun left right =>
      left.location env ≠ right.location env ∨ left.mode.Compatible right.mode)

theorem checkIndexedBorrow_sound {collection : ByteCollection} {facts : BranchFacts ctx} {env : Env ctx}
    {requests : List (IndexedCell collection ctx)} (valid : facts.Valid env)
    (checked : checkIndexedBorrow facts requests = true) : IndexedBorrowValid env requests := by
  simp only [checkIndexedBorrow, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at checked
  have bounds := fun request member => checkIndexBound_sound valid (checked.1 request member)
  refine ⟨bounds, checked.2.imp_of_mem ?_⟩
  intro left right leftMember rightMember pair
  exact checkCellPair_sound valid (bounds left leftMember) (bounds right rightMember) pair

def indexedBorrowCells {collection : ByteCollection} (env : Env ctx) (requests : List (IndexedCell collection ctx)) :
    List (ByteLocation × AccessMode) :=
  requests.map fun request => (request.location env, request.mode)

theorem IndexedBorrowValid.acquires {collection : ByteCollection} {env : Env ctx}
    {requests : List (IndexedCell collection ctx)} {state : State} {table : Nat → Nat → UInt8}
    (valid : IndexedBorrowValid env requests)
    (represented : ByteCollectionRep state collection.owner collection.layout collection.length collection.fields table)
    (available : ∀ request ∈ requests, state.Available (request.location env) request.mode none) :
    ∃ opened, Runs state
      (acquireViews state.freshHandle (indexedViews state.freshView (indexedBorrowCells env requests))) opened := by
  apply acquireIndexedViews
  · rintro cell membership
    obtain ⟨request, requested, rfl⟩ := List.mem_map.mp membership
    exact ⟨_, represented _ (valid.1 request requested) _ request.field.isLt⟩
  · rintro cell membership
    obtain ⟨request, requested, rfl⟩ := List.mem_map.mp membership
    exact available request requested
  · exact List.pairwise_map.mpr valid.2

/-- Captured caller locations describe the live views on this collection.
Views on other allocations need no index facts for this scope. -/
structure IndexedCallerViews {collection : ByteCollection} (env : Env ctx) (state : State)
    (active : List (IndexedCell collection ctx)) : Prop where
  bounded : ∀ request ∈ active, (request.index.eval env : UInt8).toNat < collection.length
  covers : ∀ view ∈ state.views, view.location.allocation = collection.owner →
    ∃ request ∈ active, request.location env = view.location ∧ request.mode = view.mode

def checkScopedIndexedBorrow {collection : ByteCollection} (facts : BranchFacts ctx)
    (active requests : List (IndexedCell collection ctx)) : Bool :=
  checkIndexedBorrow facts requests &&
    requests.all fun requested => active.all fun held => checkCellPair facts requested held

theorem checkScopedIndexedBorrow_sound {collection : ByteCollection} {env : Env ctx} {state : State}
    {facts : BranchFacts ctx} {active requests : List (IndexedCell collection ctx)}
    (valid : facts.Valid env) (caller : IndexedCallerViews env state active)
    (checked : checkScopedIndexedBorrow facts active requests = true) :
    IndexedBorrowValid env requests ∧
      ∀ request ∈ requests, state.Available (request.location env) request.mode none := by
  simp only [checkScopedIndexedBorrow, Bool.and_eq_true, List.all_eq_true] at checked
  have plan := checkIndexedBorrow_sound valid checked.1
  refine ⟨plan, ?_⟩
  intro request granted view present
  by_cases owner : view.location.allocation = collection.owner
  · obtain ⟨held, borrowed, samePlace, sameMode⟩ := caller.covers view present owner
    have compatible := checkCellPair_sound valid (plan.1 request granted) (caller.bounded held borrowed)
      (checked.2 request granted held borrowed)
    exact .inr (by simpa only [samePlace, sameMode] using compatible)
  · exact .inr (.inl fun same => owner (congrArg ByteLocation.allocation same).symm)

theorem checkScopedIndexedBorrow_bracket {collection : ByteCollection} {env : Env ctx}
    {facts : BranchFacts ctx} {active requests : List (IndexedCell collection ctx)}
    {state : State} {table : Nat → Nat → UInt8} (factsValid : facts.Valid env)
    (caller : IndexedCallerViews env state active)
    (admitted : checkScopedIndexedBorrow facts active requests = true)
    (represented : ByteCollectionRep state collection.owner collection.layout collection.length collection.fields table) :
    let loans := indexedViews state.freshView (indexedBorrowCells env requests)
    ∃ opened, Runs state (acquireViews state.freshHandle loans) opened ∧
      ∀ changed, changed.views = opened.views →
        Runs changed (releaseViews (loans.reverse.map View.id)) { changed with views := state.views } := by
  obtain ⟨plan, allowed⟩ := checkScopedIndexedBorrow_sound factsValid caller admitted
  obtain ⟨opened, entered⟩ := plan.acquires represented allowed
  exact ⟨opened, entered, fun _ kept => acquireViews_release entered kept⟩

end Aethel.CacheLayout
