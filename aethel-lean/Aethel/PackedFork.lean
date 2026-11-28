import Aethel.PackedMachine

namespace Aethel.AutomaticLayout

open Core ScopedForkJoin

/-- A checked fork action uses a resolved field and, for stores, a value
already decoded against the field's codec. -/
inductive PackedForkAction (size : Nat) where
  | load (ty : PackedType) (field : PackedValueField size ty.width)
  | store (ty : PackedType) (field : PackedValueField size ty.width) (value : ty.Value)

def PackedForkAction.footprint (owner : OwnerId) : PackedForkAction size → TaskFootprint
  | .load _ field => field.footprint owner .shared
  | .store _ field _ => field.footprint owner .exclusive

def PackedForkAction.apply (action : PackedForkAction size) (image : Image size) : Image size :=
  match action with
  | .load .. => image
  | .store ty field value => field.store ty.codec image value

def PackedForkAction.result (action : PackedForkAction size) (image : Image size) : Option Nat :=
  match action with
  | .load ty field => (field.load ty.codec image).map (fun value => value.val.toNat)
  | .store .. => none

private theorem byteLocation_mem {offsets : List Nat} {byte : Nat}
    (owner : OwnerId) (member : byte ∈ offsets) :
    (⟨owner, byte⟩ : ByteLocation) ∈ offsets.map (fun offset => ⟨owner, offset⟩) :=
  List.mem_map_of_mem member

theorem PackedForkAction.apply_commutes {owner : OwnerId} {a b : PackedForkAction size}
    (compatible : ForkDisjoint (a.footprint owner) (b.footprint owner)) (before : Image size) :
    b.apply (a.apply before) = a.apply (b.apply before) := by
  cases a with
  | load _ _ => rfl
  | store tyA fieldA valueA =>
    cases b with
    | load _ _ => rfl
    | store tyB fieldB valueB =>
      apply PackedValueField.store_commutes tyA.codec tyB.codec before valueA valueB
      intro byte inA inB
      exact (compatible.1 ⟨owner, byte⟩ (byteLocation_mem owner inA)).2 (byteLocation_mem owner inB)

theorem PackedForkAction.result_stable {owner : OwnerId} {a b : PackedForkAction size}
    (compatible : ForkDisjoint (a.footprint owner) (b.footprint owner)) (before : Image size) :
    a.result (b.apply before) = a.result before := by
  cases a with
  | store _ _ _ => rfl
  | load tyA fieldA =>
    cases b with
    | load _ _ => rfl
    | store tyB fieldB valueB =>
      have stable := PackedValueField.load_stable (reader := fieldA) (writer := fieldB)
        tyA.codec tyB.codec before valueB
        (fun byte inA inB =>
          (compatible.2 ⟨owner, byte⟩ (byteLocation_mem owner inB)).1 (byteLocation_mem owner inA))
      exact congrArg (Option.map (fun value : tyA.Value => value.val.toNat)) stable

def applyPackedSchedule (actions : List (PackedForkAction size)) (before : Image size) : Image size :=
  actions.foldl (fun image action => action.apply image) before

def observePackedSchedule : List (PackedForkAction size) → Image size → List (Option Nat)
  | [], _ => []
  | action :: rest, before =>
    action.result before :: observePackedSchedule rest (action.apply before)

/-- Masked stores are recomputed on the current image in both schedules.
Any permutation of compatible actions produces exactly the same byte image. -/
theorem applyPackedSchedule_perm (owner : OwnerId)
    {left right : List (PackedForkAction size)} (perm : left.Perm right)
    (compatible : left.Pairwise (fun a b => ForkDisjoint (a.footprint owner) (b.footprint owner)))
    (before : Image size) : applyPackedSchedule left before = applyPackedSchedule right before := by
  induction perm generalizing before with
  | nil => rfl
  | cons action _ ih =>
    exact ih (List.pairwise_cons.mp compatible).2 (action.apply before)
  | swap a b rest =>
    have adjacent := (List.pairwise_cons.mp compatible).1 a List.mem_cons_self
    change applyPackedSchedule rest (a.apply (b.apply before)) =
      applyPackedSchedule rest (b.apply (a.apply before))
    rw [PackedForkAction.apply_commutes adjacent before]
  | trans perm _ ihLeft ihRight =>
    exact (ihLeft compatible before).trans (ihRight
      (compatible.perm perm (fun h => forkDisjoint_symm h)) before)

/-- Read results belong to their source action and take the same value in
every safe schedule, even though the schedule can reorder observations. -/
theorem observePackedSchedule_eq_snapshot (owner : OwnerId)
    (actions : List (PackedForkAction size))
    (compatible : actions.Pairwise (fun a b => ForkDisjoint (a.footprint owner) (b.footprint owner)))
    (before : Image size) :
    observePackedSchedule actions before = actions.map (fun action => action.result before) := by
  induction actions generalizing before with
  | nil => rfl
  | cons action rest ih =>
    obtain ⟨head, tail⟩ := List.pairwise_cons.mp compatible
    simp only [observePackedSchedule, List.map_cons, List.cons.injEq, true_and]
    rw [ih tail]
    apply List.map_congr_left
    intro later member
    exact PackedForkAction.result_stable (forkDisjoint_symm (head later member)) before

end Aethel.AutomaticLayout
