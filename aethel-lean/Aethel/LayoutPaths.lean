import Aethel.LayoutAccess

namespace Aethel.AutomaticLayout

/-- An observed integer leaf, expressed in absolute bit coordinates relative to
the record. The byte footprint can be larger than this logical interval. -/
def Leaf (layout : Layout) (path : List Nat) (start width : Nat) : Prop :=
  ∃ placement kind slot, resolve layout path = some (placement, .integer kind slot) ∧
    start = placement.bitStart ∧ width = kind.bits

private theorem lookupLeaf {abi : TargetIntegerABI} {fields : List (StoragePolicy × Schema)}
    {size alignment index start width : Nat} {placed : List Field} {tail : List Nat}
    (planned : Conforms abi (.record fields) (.record size alignment placed))
    (leaf : Leaf (.record size alignment placed) (index :: tail) start width) :
    ∃ outer child policy, placed[index]? = some outer ∧ Conforms abi child outer.2 ∧
      Field.Valid size alignment policy outer ∧
      0 < width ∧ outer.1.byteOffset * 8 ≤ start ∧
      start + width ≤ (outer.1.byteOffset + outer.bytes) * 8 ∧
      ((∃ kind slot, tail = [] ∧ outer.2 = .integer kind slot ∧
          start = outer.1.bitStart ∧ width = kind.bits) ∨
        (tail ≠ [] ∧ outer.1.bitOffset = none ∧
          ∃ relative, start = outer.1.byteOffset * 8 + relative ∧
            Leaf outer.2 tail relative width)) := by
  obtain ⟨placement, kind, slot, found, rfl, rfl⟩ := leaf
  have positive : 0 < kind.bits := kind.bits_pos
  cases atIndex : placed[index]? with
  | none => simp [resolve, atIndex, bind] at found
  | some outer =>
    obtain ⟨policy, child, _, valid, repr⟩ := planned.field atIndex
    obtain ⟨place, nested⟩ := outer
    cases tail with
    | nil =>
      simp [resolve, atIndex, bind] at found
      obtain ⟨rfl, rfl⟩ := found
      cases repr with
      | integer slotValid =>
        have span := integer_span (.integer slotValid) valid
        exact ⟨_, _, policy, rfl, .integer slotValid, valid, positive,
          Nat.le_add_right _ _, span, .inl ⟨_, _, rfl, rfl, rfl, rfl⟩⟩
    | cons next rest =>
      simp only [resolve, atIndex, bind, pure, Option.bind_eq_some_iff, Prod.exists,
        Option.some.injEq] at found
      obtain ⟨outerLoc, outerLayout, outerEq, relative, _, inner, rebased⟩ := found
      obtain ⟨sameLoc, sameLayout⟩ := Prod.mk.inj outerEq
      subst outerLoc
      subst outerLayout
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj rebased
      have bound := resolved_integer_fits repr inner
      change relative.bitStart + kind.bits ≤ nested.size * 8 at bound
      have addressable : place.bitOffset = none := by
        cases h : place.bitOffset with
        | none => rfl
        | some bit =>
          cases nested with
          | integer kind slot => simp [resolve] at inner
          | record size align fields => simp [Field.Valid, h, Layout.bits] at valid
      have combined : (⟨place.byteOffset + relative.byteOffset, relative.bitOffset⟩ : Placement).bitStart =
          place.byteOffset * 8 + relative.bitStart := by
        simp [Placement.bitStart]
        omega
      refine ⟨_, _, policy, rfl, repr, valid, positive, ?_, ?_, .inr ⟨by simp, addressable,
        relative.bitStart, combined, ⟨relative, kind, slot, inner, rfl, rfl⟩⟩⟩
      · rw [combined]
        exact Nat.le_add_right _ _
      · rw [combined]
        simp [Field.bytes, addressable]
        omega

private theorem pairSeparated {abi : TargetIntegerABI} {fields : List (StoragePolicy × Schema)}
    {size alignment i j : Nat} {placed : List Field} {left right : Field}
    (planned : Conforms abi (.record fields) (.record size alignment placed))
    (foundLeft : placed[i]? = some left) (foundRight : placed[j]? = some right)
    (ordered : i < j) : left.Separate right := by
  cases planned with
  | record _ _ _ separate _ _ =>
    obtain ⟨hi, hleft⟩ := List.getElem?_eq_some_iff.mp foundLeft
    obtain ⟨hj, hright⟩ := List.getElem?_eq_some_iff.mp foundRight
    simpa only [hleft, hright] using List.pairwise_iff_getElem.mp separate i j hi hj ordered

theorem Field.Separate.symm {a b : Field} (h : a.Separate b) : b.Separate a := by
  unfold Field.Separate at h ⊢
  rcases h with empty | empty | before | after | ⟨same, bits⟩
  · exact .inr (.inl empty)
  · exact .inl empty
  · exact .inr (.inr (.inr (.inl before)))
  · exact .inr (.inr (.inl after))
  · refine .inr (.inr (.inr (.inr ⟨same.symm, ?_⟩)))
    cases x : a.1.bitOffset <;> cases y : b.1.bitOffset <;> simp_all only
    exact bits.symm

theorem leaves_separate {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    {left right : List Nat} {a w b v : Nat}
    (planned : Conforms abi schema layout) (first : Leaf layout left a w)
    (second : Leaf layout right b v) (distinct : left ≠ right) :
    a + w ≤ b ∨ b + v ≤ a := by
  induction left generalizing schema layout right a b w v with
  | nil =>
    obtain ⟨placement, kind, slot, here, _, _⟩ := first
    simp [resolve] at here
    obtain ⟨_, rfl⟩ := here
    cases right
    · exact (distinct rfl).elim
    · obtain ⟨_, _, _, impossible, _, _⟩ := second
      simp [resolve] at impossible
  | cons i tail ih =>
    cases right with
    | nil =>
      obtain ⟨placement, kind, slot, here, _, _⟩ := second
      simp [resolve] at here
      obtain ⟨_, rfl⟩ := here
      obtain ⟨_, _, _, impossible, _, _⟩ := first
      simp [resolve] at impossible
    | cons j rest =>
      cases planned with
      | integer _ =>
        obtain ⟨_, _, _, impossible, _, _⟩ := first
        simp [resolve] at impossible
      | record aligned stride count separation positions children =>
        have planned := Conforms.record aligned stride count separation positions children
        obtain ⟨outer, child, p, lookup, conforms, valid, positive, lower, upper, descent⟩ :=
          lookupLeaf planned first
        obtain ⟨other, _, q, lookupOther, _, _, positiveOther, lowerOther, upperOther, descentOther⟩ :=
          lookupLeaf planned second
        by_cases same : i = j
        · subst j
          rw [lookup] at lookupOther
          cases lookupOther
          rcases descent with ⟨kind, slot, rfl, scalar, _, _⟩ | ⟨nonempty, _, x, hx, sub⟩
          · rcases descentOther with ⟨_, _, rfl, _, _, _⟩ |
              ⟨nonempty, _, y, hy, ⟨_, _, _, impossible, _, _⟩⟩
            · exact (distinct rfl).elim
            · cases rest <;> simp_all [resolve]
          · rcases descentOther with ⟨_, _, rfl, scalar, _, _⟩ | ⟨_, _, y, hy, subOther⟩
            · obtain ⟨_, _, _, impossible, _, _⟩ := sub
              cases tail <;> simp_all [resolve]
            · have separated := ih conforms sub subOther (fun equal => distinct (congrArg (List.cons i) equal))
              omega
        · have apart : outer.Separate other ∨ other.Separate outer := by
            rcases Nat.lt_or_gt_of_ne same with less | greater
            · exact .inl (pairSeparated planned lookup lookupOther less)
            · exact .inr (pairSeparated planned lookupOther lookup greater)
          have symmetric : outer.Separate other := apart.elim id Field.Separate.symm
          unfold Field.Separate at symmetric
          rcases symmetric with zero | zero | before | after | ⟨sameByte, separateBits⟩
          · omega
          · omega
          · omega
          · omega
          · cases h : outer.1.bitOffset <;> cases k : other.1.bitOffset <;>
              simp only [h, k] at separateBits
            all_goals try contradiction
            rcases descent with ⟨kind, slot, _, scalar, ha, hw⟩ | ⟨_, bad, _⟩
            · rcases descentOther with ⟨kind', slot', _, scalar', hb, hv⟩ | ⟨_, bad, _⟩
              · simp [scalar, scalar', Layout.bits] at separateBits
                simp [Placement.bitStart, h] at ha
                simp [Placement.bitStart, k] at hb
                omega
              · simp [k] at bad
            · simp [h] at bad

theorem resolveInteger_leaf {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    {planned : Conforms abi schema layout} {path : List Nat} {field : IntegerField layout.size}
    (found : resolveInteger planned path = some field) :
    Leaf layout path field.offset field.kind.bits := by
  unfold resolveInteger at found
  split at found
  next placement kind slot geometry =>
    cases found
    exact ⟨placement, kind, slot, geometry, rfl, rfl⟩
  next => cases found

theorem leaf_paths_separate {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) {left right : List Nat}
    {a b : IntegerField layout.size}
    (first : resolveInteger planned left = some a) (second : resolveInteger planned right = some b)
    (different : left ≠ right) :
    a.offset + a.kind.bits ≤ b.offset ∨ b.offset + b.kind.bits ≤ a.offset :=
  leaves_separate planned (resolveInteger_leaf first) (resolveInteger_leaf second) different

theorem readInteger_preserved_other_path {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) {writePath readPath : List Nat}
    {image next : Image layout.size} {value : IntegerBits}
    (different : writePath ≠ readPath)
    (updated : writeInteger planned writePath image value = some next) :
    readInteger planned readPath next = readInteger planned readPath image := by
  cases readAt : resolveInteger planned readPath with
  | none => simp [readInteger, readAt]
  | some observed =>
    cases writeAt : resolveInteger planned writePath with
    | none => simp [writeInteger, writeAt, bind] at updated
    | some written =>
      exact readInteger_preserved_by_disjoint_write planned writeAt readAt
        (leaf_paths_separate planned writeAt readAt different) updated

def Layout.leafPaths : Layout → List (List Nat)
  | .integer .. => [[]]
  | .record _ _ fields =>
    fields.attach.zipIdx.flatMap fun (field, index) =>
      (leafPaths field.val.2).map (List.cons index)
termination_by layout => sizeOf layout
decreasing_by
  have smaller := List.sizeOf_lt_of_mem field.property
  have childSmaller : sizeOf field.val.2 < sizeOf field.val := by
    cases field.val
    simp
    omega
  simp_wf
  omega

private theorem Layout.mem_childPaths {size alignment index : Nat} {fields : List Field}
    {field : Field} {path : List Nat} (lookup : fields[index]? = some field)
    (member : path ∈ field.2.leafPaths) :
    index :: path ∈ (Layout.record size alignment fields).leafPaths := by
  obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp lookup
  have atZip : index < fields.attach.zipIdx.length := by simpa using bound
  have atIndex := List.mem_of_getElem (h := atZip) (rfl : fields.attach.zipIdx[index] = _)
  rw [List.getElem_zipIdx atZip] at atIndex
  simp only [Nat.zero_add] at atIndex
  rw [Layout.leafPaths, List.mem_flatMap]
  refine ⟨_, atIndex, List.mem_map.mpr ⟨path, ?_, rfl⟩⟩
  simpa only [List.getElem_attach, eq] using member

theorem Leaf.mem_leafPaths {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    {path : List Nat} {start width : Nat} (planned : Conforms abi schema layout)
    (leaf : Leaf layout path start width) : path ∈ layout.leafPaths := by
  induction path generalizing schema layout start width with
  | nil =>
    obtain ⟨_, _, _, found, _, _⟩ := leaf
    simp [resolve] at found
    obtain ⟨_, rfl⟩ := found
    simp [Layout.leafPaths]
  | cons index tail ih =>
    cases planned with
    | integer _ =>
      obtain ⟨_, _, _, found, _, _⟩ := leaf
      simp [resolve] at found
    | record aligned stride count separate positions children =>
      obtain ⟨outer, child, policy, lookup, conforms, _, _, _, _, descent⟩ :=
        lookupLeaf (.record aligned stride count separate positions children) leaf
      apply Layout.mem_childPaths lookup
      rcases descent with ⟨kind, slot, rfl, scalar, _, _⟩ | ⟨_, _, relative, _, inner⟩
      · simp [scalar, Layout.leafPaths]
      · exact ih conforms inner

theorem Layout.leafPaths_sound {layout : Layout} {path : List Nat}
    (member : path ∈ layout.leafPaths) : ∃ start width, Leaf layout path start width := by
  induction path generalizing layout with
  | nil =>
    cases layout with
    | integer kind slot => exact ⟨0, kind.bits, ⟨0, none⟩, kind, slot, rfl, rfl, rfl⟩
    | record size align fields =>
      rw [Layout.leafPaths, List.mem_flatMap] at member
      obtain ⟨_, _, found⟩ := member
      obtain ⟨_, _, impossible⟩ := List.mem_map.mp found
      cases impossible
  | cons index path ih =>
    cases layout with
    | integer _ _ => simp [Layout.leafPaths] at member
    | record size align fields =>
      rw [Layout.leafPaths, List.mem_flatMap] at member
      obtain ⟨⟨entry, i⟩, indexed, found⟩ := member
      obtain ⟨tail, inner, eq⟩ := List.mem_map.mp found
      obtain ⟨rfl, rfl⟩ := List.cons.inj eq
      have indexInfo := List.mem_zipIdx indexed
      have h : i < fields.length := by simpa using indexInfo.2.1
      have lookup : fields[i]? = some entry.val := by
        have attached := congrArg Subtype.val indexInfo.2.2
        simp only [Nat.sub_zero, List.getElem_attach] at attached
        rw [List.getElem?_eq_getElem h, attached]
      obtain ⟨_, _, place, kind, slot, resolves, _, _⟩ := ih inner
      cases tail with
      | nil =>
        simp [resolve] at resolves
        obtain ⟨_, scalar⟩ := resolves
        exact ⟨_, _, entry.val.1, kind, slot, by simp [resolve, lookup, bind, scalar], rfl, rfl⟩
      | cons next rest =>
        exact ⟨_, _, ⟨entry.val.1.byteOffset + place.byteOffset, place.bitOffset⟩, kind, slot,
          by simp [resolve, lookup, bind, resolves], rfl, rfl⟩

end Aethel.AutomaticLayout
