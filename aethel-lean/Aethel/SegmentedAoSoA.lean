import Aethel.CacheLayout

namespace Aethel.SegmentedAoSoA

open Core

/-- Each directory entry names a separate allocation containing SoA columns. -/
structure Vector where
  tiles : Array OwnerId := #[]
  length : Nat := 0
  deriving Repr, DecidableEq

abbrev Row := Nat → UInt8

private def laneLocation (owner : OwnerId) (width lane field : Nat) : ByteLocation :=
  ⟨owner, soaSlot width lane field⟩

/-- Resolve a physical slot. Spare lanes may resolve too. The vector's logical
bounds are checked separately before exposing a slot to a caller. -/
def slot (vec : Vector) (width index field : Nat) : Option ByteLocation :=
  vec.tiles[index / width]?.map fun owner => laneLocation owner width (index % width) field

/-- Observe a logical byte for representation checking. Borrowed program reads
use the byte machine’s handle or view operations. -/
def get (s : State) (vec : Vector) (width fields index field : Nat) : Option UInt8 := do
  if index < vec.length ∧ field < fields then
    (← slot vec width index field) |> s.byte
  else none

/-- The directory uses distinct, issued owners. Each initialized row has live
bytes at the corresponding physical locations. -/
def Represents (s : State) (vec : Vector) (width fields : Nat) (rows : List Row) : Prop :=
  vec.length = rows.length ∧
  vec.tiles.toList.Nodup ∧
  (∀ owner ∈ vec.tiles, owner ∈ s.issued) ∧
  ∀ i (hi : i < rows.length) f, f < fields →
    ∃ owner, vec.tiles[i / width]? = some owner ∧
      s.byte (laneLocation owner width (i % width) f) = some (rows[i] f)

private def Writable (s : State) (owner : OwnerId) (width lane count : Nat) : Prop :=
  ∀ f, f < count →
    let loc := laneLocation owner width lane f
    (s.byte loc).isSome = true ∧ s.Available loc .exclusive none

private def checkWritable (s : State) (owner : OwnerId) (width lane count : Nat) : Bool :=
  (List.range count).all fun f =>
    let loc := laneLocation owner width lane f
    (s.byte loc).isSome && decide (s.Available loc .exclusive none)

private theorem checkWritable_correct (s : State) (owner : OwnerId) (width lane count : Nat) :
    checkWritable s owner width lane count = true ↔ Writable s owner width lane count := by
  simp [checkWritable, Writable, List.all_eq_true, List.mem_range]

private def writeRow (owner : OwnerId) (width lane : Nat) (row : Row) :
    Nat → State → State
  | 0, s => s
  | n + 1, s => (writeRow owner width lane row n s).store (laneLocation owner width lane n) (row n)

private def tileBytes (width fields : Nat) : List UInt8 :=
  List.replicate (width * fields) 0

/-- Prepare an existing lane or allocate a fresh tile at capacity. -/
private def prepare (s : State) (vec : Vector) (width fields : Nat) (fresh : OwnerId) :
    Option (State × Array OwnerId × OwnerId) := do
  let index := vec.length / width
  if let some owner := vec.tiles[index]? then
    return (s, vec.tiles, owner)
  else if index = vec.tiles.size ∧ vec.length % width = 0 then
    let next ← execute s (.alloc fresh (tileBytes width fields))
    return (next, vec.tiles.push fresh, fresh)
  else none

/-- Append one row using byte writes checked against the current reservations.
A failed check returns no new vector or state. -/
def push (s : State) (vec : Vector) (width fields : Nat) (fresh : OwnerId) (row : Row) :
    Option (State × Vector) := do
  if width = 0 then none else do
    let (base, tiles, owner) ← prepare s vec width fields fresh
    let lane := vec.length % width
    if checkWritable base owner width lane fields then
      return (writeRow owner width lane row fields base, ⟨tiles, vec.length + 1⟩)
    else none

private theorem store_byte_frame {s : State} {owner : OwnerId} {width lane count : Nat}
    (row : Row) (p : ByteLocation)
    (away : ∀ f, f < count → laneLocation owner width lane f ≠ p) :
    (writeRow owner width lane row count s).byte p = s.byte p := by
  induction count with
  | zero => rfl
  | succ n ih =>
    exact (State.store_byte_other _ _ _ _ (away n (Nat.lt_succ_self n))).trans
      (ih (fun f hf => away f (Nat.lt_succ_of_lt hf)))

private theorem laneLocation_injective {owner : OwnerId} {width lane f g : Nat}
    (hl : lane < width)
    (same : laneLocation owner width lane f = laneLocation owner width lane g) : f = g :=
  (soaSlot_eq_iff width lane lane f g hl hl |>.mp (congrArg ByteLocation.offset same)).2

private theorem writeRow_target {s : State} {owner : OwnerId} {width lane count f : Nat}
    (row : Row) (hl : lane < width) (hf : f < count)
    (live : ∃ b, s.byte (laneLocation owner width lane f) = some b) :
    (writeRow owner width lane row count s).byte (laneLocation owner width lane f) = some (row f) := by
  induction count with
  | zero => omega
  | succ n ih =>
    by_cases same : f = n
    · subst f
      obtain ⟨b, hb⟩ := live
      exact State.store_byte_written _ _ _ _ ((store_byte_frame row _ (fun g hg eq =>
        (Nat.ne_of_lt hg) (laneLocation_injective hl eq))).trans hb)
    · exact (State.store_byte_other _ _ _ _ (fun eq =>
        same (laneLocation_injective hl eq).symm)).trans (ih (by omega))

private theorem addAllocation_byte_other (s : State) (owner : OwnerId) (bytes : List UInt8)
    (p : ByteLocation) (different : p.allocation ≠ owner) :
    (s.addAllocation owner bytes).byte p = s.byte p := by
  simp [State.byte, State.addAllocation, State.allocation, beq_false_of_ne different.symm]

private theorem writeRow_metadata (s : State) (owner width lane count : Nat) (row : Row) :
    let next := writeRow owner width lane row count s
    next.views = s.views ∧ next.handles = s.handles ∧ next.issued = s.issued ∧
      next.resources = s.resources := by
  induction count with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ n ih => exact ⟨ih.1, ih.2.1, ih.2.2.1, (State.resources_store _ _ _).trans ih.2.2.2⟩

private inductive Prepared (s : State) (vec : Vector) (width fields : Nat) (fresh : OwnerId) :
    State → Array OwnerId → OwnerId → Prop where
  | existing (found : vec.tiles[vec.length / width]? = some owner) :
      Prepared s vec width fields fresh s vec.tiles owner
  | newTile (index : vec.length / width = vec.tiles.size)
      (lane : vec.length % width = 0) (unused : fresh ∉ s.issued) :
      Prepared s vec width fields fresh
        (s.addAllocation fresh (tileBytes width fields)) (vec.tiles.push fresh) fresh

private theorem prepare_sound {s base : State} {vec : Vector} {width fields : Nat}
    {fresh owner : OwnerId} {tiles : Array OwnerId}
    (ok : prepare s vec width fields fresh = some (base, tiles, owner)) :
    Prepared s vec width fields fresh base tiles owner := by
  simp only [prepare] at ok
  split at ok
  · rename_i found
    cases ok
    exact .existing found
  · split at ok
    · rename_i boundary
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at ok
      obtain ⟨next, allocated, rfl, rfl, rfl⟩ := ok
      cases execute_sound allocated with
      | alloc unused => exact .newTile boundary.1 boundary.2 unused
    · cases ok

private theorem push_sound {s next : State} {vec out : Vector} {width fields : Nat}
    {fresh : OwnerId} {row : Row}
    (ok : push s vec width fields fresh row = some (next, out)) :
    0 < width ∧ ∃ base tiles owner, Prepared s vec width fields fresh base tiles owner ∧
      Writable base owner width (vec.length % width) fields ∧
      next = writeRow owner width (vec.length % width) row fields base ∧
      out = ⟨tiles, vec.length + 1⟩ := by
  simp only [push] at ok
  split at ok
  · cases ok
  · rename_i widthNonzero
    simp only [bind, Option.bind_eq_some_iff, Prod.exists] at ok
    obtain ⟨base, tiles, owner, prepared, checked⟩ := ok
    simp only [pure] at checked
    split at checked
    · rename_i writable
      cases checked
      exact ⟨Nat.pos_of_ne_zero widthNonzero, base, tiles, owner, prepare_sound prepared,
        (checkWritable_correct _ _ _ _ _).mp writable, rfl, rfl⟩
    · cases checked

private theorem Prepared.keepEntry {s base : State} {vec : Vector} {width fields fresh owner : Nat}
    {tiles : Array OwnerId} (h : Prepared s vec width fields fresh base tiles owner)
    {index old : Nat} (found : vec.tiles[index]? = some old) :
    tiles[index]? = some old := by
  cases h with
  | existing => exact found
  | newTile =>
    have bound := (Array.getElem?_eq_some_iff.mp found).choose
    simpa only [Array.getElem?_push, Nat.ne_of_lt bound, ite_false] using found

private theorem Prepared.nextEntry {s base : State} {vec : Vector} {width fields fresh owner : Nat}
    {tiles : Array OwnerId} (h : Prepared s vec width fields fresh base tiles owner) :
    tiles[vec.length / width]? = some owner := by
  cases h with
  | existing found => exact found
  | newTile index => simp [index]

private theorem Prepared.directory {s base : State} {vec : Vector} {width fields fresh owner : Nat}
    {tiles : Array OwnerId} (h : Prepared s vec width fields fresh base tiles owner)
    (distinct : vec.tiles.toList.Nodup) (issued : ∀ o ∈ vec.tiles, o ∈ s.issued) :
    tiles.toList.Nodup ∧ (∀ o ∈ tiles, o ∈ base.issued) := by
  cases h with
  | existing => exact ⟨distinct, issued⟩
  | newTile _ _ unused =>
    refine ⟨?_, ?_⟩
    · rw [Array.toList_push, List.nodup_append]
      exact ⟨distinct, by simp, fun o ho b hb same => by
        simp only [List.mem_singleton] at hb
        exact unused ((same.trans hb) ▸ issued o (Array.mem_toList_iff.mp ho))⟩
    · intro o ho
      rcases Array.mem_push.mp ho with member | rfl
      · exact List.mem_cons_of_mem _ (issued o member)
      · exact List.mem_cons_self

private theorem Prepared.frame {s base : State} {vec : Vector} {width fields fresh owner : Nat}
    {tiles : Array OwnerId} (h : Prepared s vec width fields fresh base tiles owner) :
    base.views = s.views ∧ base.handles = s.handles ∧
      (∀ p : ByteLocation, p.allocation ∈ s.issued → base.byte p = s.byte p) := by
  cases h with
  | existing => exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | newTile _ _ unused =>
    exact ⟨rfl, rfl, fun p issued => addAllocation_byte_other _ _ _ p
      (fun same => unused (same ▸ issued))⟩

private theorem oldLocation_ne {vec : Vector} {tiles : Array OwnerId} {width owner i old f g : Nat}
    (hw : 0 < width) (hi : i < vec.length) (distinct : tiles.toList.Nodup)
    (atOld : tiles[i / width]? = some old) (atNext : tiles[vec.length / width]? = some owner) :
    laneLocation owner width (vec.length % width) g ≠ laneLocation old width (i % width) f := by
  intro same
  have owns := congrArg ByteLocation.allocation same
  change owner = old at owns
  subst old
  have bound := (Array.getElem?_eq_some_iff.mp atOld).choose
  have tileEq : i / width = vec.length / width := (distinct.getElem?_inj (by simpa using bound)).mp
    (by simp only [Array.getElem?_toList, atOld, atNext])
  have laneEq := ((soaSlot_eq_iff width _ _ _ _ (Nat.mod_lt _ hw) (Nat.mod_lt _ hw)).mp
    (congrArg ByteLocation.offset same)).1
  exact (Nat.ne_of_lt hi) (by
    have h1 := Nat.div_add_mod i width
    have h2 := Nat.div_add_mod vec.length width
    rw [tileEq, ← laneEq] at h1
    exact h1.symm.trans h2)

theorem push_preserves_rep {s next : State} {vec out : Vector}
    {width fields fresh : Nat} {row : Row} {rows : List Row}
    (ok : push s vec width fields fresh row = some (next, out))
    (rep : Represents s vec width fields rows) :
    Represents next out width fields (rows ++ [row]) ∧
      ∀ i, i < vec.length → ∀ f, f < fields →
        slot out width i f = slot vec width i f := by
  obtain ⟨hw, base, tiles, owner, prepared, writable, rfl, rfl⟩ := push_sound ok
  obtain ⟨hlen, distinct, issued, stored⟩ := rep
  obtain ⟨unique, directoryIssued⟩ := prepared.directory distinct issued
  have atNext := prepared.nextEntry
  have metadata := writeRow_metadata base owner width (vec.length % width) fields row
  refine ⟨⟨by simp [hlen], unique, by simpa only [metadata.2.2.1] using directoryIssued, ?_⟩, ?_⟩
  · intro i hi f hf
    by_cases oldRow : i < rows.length
    · obtain ⟨old, entry, read⟩ := stored i oldRow f hf
      have keeps := prepared.keepEntry entry
      refine ⟨old, keeps, ?_⟩
      rw [List.getElem_append_left oldRow]
      rw [store_byte_frame row _ (fun _ _ => oldLocation_ne hw (hlen ▸ oldRow) unique keeps atNext)]
      exact (prepared.frame.2.2 _ (issued old (Array.mem_of_getElem? entry))).trans read
    · have atEnd : i = vec.length := by simp only [List.length_append, List.length_singleton] at hi; omega
      subst i
      refine ⟨owner, atNext, ?_⟩
      rw [List.getElem_append_right (Nat.le_of_eq hlen.symm)]
      simpa [hlen] using writeRow_target row (Nat.mod_lt vec.length hw) hf
        (Option.isSome_iff_exists.mp (writable f hf).1)
  · intro i hi f hf
    obtain ⟨old, entry, _⟩ := stored i (hlen ▸ hi) f hf
    simp [slot, prepared.keepEntry entry, entry]

theorem get_rep {s : State} {vec : Vector} {width fields : Nat} {rows : List Row}
    (rep : Represents s vec width fields rows) {i f : Nat} (hi : i < rows.length) (hf : f < fields) :
    get s vec width fields i f = some (rows[i] f) := by
  obtain ⟨owner, entry, read⟩ := rep.2.2.2 i hi f hf
  simpa [get, slot, rep.1, hi, hf, entry, bind] using read

theorem push_frames_views {s next : State} {vec out : Vector}
    {width fields fresh : Nat} {row : Row}
    (ok : push s vec width fields fresh row = some (next, out)) :
    next.views = s.views ∧ next.handles = s.handles ∧
      ∀ v ∈ s.views, v.location.allocation ∈ s.issued →
        next.byte v.location = s.byte v.location := by
  obtain ⟨_, base, _, owner, prepared, writable, rfl, rfl⟩ := push_sound ok
  have metadata := writeRow_metadata base owner width (vec.length % width) fields row
  obtain ⟨views, handles, frame⟩ := prepared.frame
  refine ⟨metadata.1.trans views, metadata.2.1.trans handles, ?_⟩
  intro v hv issued
  rw [store_byte_frame row _]
  · exact frame v.location issued
  · intro f hf
    have available := (writable f hf).2 v (views ▸ hv)
    simpa [AccessMode.Compatible] using available

/-- The empty directory represents an empty logical sequence. -/
theorem empty_rep (s : State) (width fields : Nat) :
    Represents s {} width fields [] := by
  simp [Represents]

private theorem writeRow_allocationOwners (s : State) (owner width lane count : Nat) (row : Row) :
    (writeRow owner width lane row count s).allocations.map Allocation.owner =
      s.allocations.map Allocation.owner := by
  induction count with
  | zero => rfl
  | succ n ih => exact (State.store_owners _ _ _).trans ih

theorem push_preserves_machine {s next : State} {vec out : Vector}
    {width fields fresh : Nat} {row : Row}
    (ok : push s vec width fields fresh row = some (next, out))
    (owners : s.OwnersValid) (live : s.ReferencesLive) (compatible : s.ViewsCompatible) :
    next.OwnersValid ∧ next.ReferencesLive ∧ next.ViewsCompatible := by
  obtain ⟨_, base, _, owner, prepared, _, rfl, rfl⟩ := push_sound ok
  have baseValid : base.OwnersValid ∧ base.ReferencesLive ∧ base.ViewsCompatible := by
    cases prepared with
    | existing => exact ⟨owners, live, compatible⟩
    | newTile _ _ unused =>
      have step : Step s (.alloc fresh (tileBytes width fields)) _ := .alloc unused
      exact ⟨step.owners_valid owners, step.references_live owners live, step.views_compatible compatible⟩
  have metadata := writeRow_metadata base owner width (vec.length % width) fields row
  refine ⟨?_, ?_, ?_⟩
  · simpa only [State.OwnersValid, writeRow_allocationOwners, metadata.2.2.1] using baseValid.1
  · simpa only [State.ReferencesLive, metadata.1, metadata.2.1, metadata.2.2.2] using baseValid.2.1
  · simpa only [State.ViewsCompatible, metadata.1] using baseValid.2.2

private theorem liveByte_issued {s : State} {p : ByteLocation} {value : UInt8}
    (valid : s.OwnersValid) (live : s.byte p = some value) :
    p.allocation ∈ s.issued := by
  simp only [State.byte, bind, Option.bind_eq_some_iff] at live
  obtain ⟨allocation, found, _⟩ := live
  have entry := List.mem_of_find?_eq_some found
  have same : allocation.owner = p.allocation := by simpa using List.find?_some found
  exact valid.2 _ (List.mem_map.mpr ⟨allocation, entry, same⟩)

/-- A read through an existing shared or exclusive view still succeeds with
the same value after the append. -/
theorem push_preserves_view_read {s next : State} {vec out : Vector}
    {width fields fresh : Nat} {row : Row} {id : ViewId} {value : UInt8}
    (ok : push s vec width fields fresh row = some (next, out))
    (valid : s.OwnersValid) (read : Step s (.readView id) (s.observe value)) :
    Step next (.readView id) (next.observe value) := by
  cases read with
  | readView found live available =>
    obtain ⟨views, _, frame⟩ := push_frames_views ok
    exact .readView (by simpa only [State.view, views] using found)
      ((frame _ (List.mem_of_find?_eq_some found) (liveByte_issued valid live)).trans live)
      (by simpa only [State.Available, views] using available)

end Aethel.SegmentedAoSoA
