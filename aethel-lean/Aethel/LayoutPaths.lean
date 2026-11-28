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
      0 < width ∧ outer.1.bitStart ≤ start ∧
      start + width ≤ outer.1.bitStart + outer.bitExtent ∧
      ((∃ kind slot, tail = [] ∧ outer.2 = .integer kind slot ∧
          start = outer.1.bitStart ∧ width = kind.bits) ∨
        (tail ≠ [] ∧
          ∃ relative, start = outer.1.bitStart + relative ∧
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
        refine ⟨_, _, policy, rfl, .integer slotValid, valid, positive,
          Nat.le_refl _, ?_, .inl ⟨_, _, rfl, rfl, rfl, rfl⟩⟩
        have fits := slotValid.1
        unfold IntegerType.payloadBytes at fits
        cases h : place.bitOffset <;>
          simp [Field.bitExtent, h, Layout.size, Layout.bits] <;> omega
    | cons next rest =>
      simp only [resolve, atIndex, bind, pure, Option.bind_eq_some_iff, Prod.exists,
        Option.some.injEq] at found
      obtain ⟨outerLoc, outerLayout, outerEq, relative, _, inner, rebased⟩ := found
      obtain ⟨sameLoc, sameLayout⟩ := Prod.mk.inj outerEq
      subst outerLoc
      subst outerLayout
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj rebased
      have combined := place.bitStart_rebase relative
      refine ⟨_, _, policy, rfl, repr, valid, positive, ?_, ?_, .inr ⟨by simp,
        relative.bitStart, combined, ⟨relative, kind, slot, inner, rfl, rfl⟩⟩⟩
      · rw [combined]
        exact Nat.le_add_right _ _
      · rw [combined]
        have bound : relative.bitStart + kind.bits ≤ Field.bitExtent (place, nested) := by
          cases h : place.bitOffset with
          | none => simpa [Field.bitExtent, h] using resolved_integer_fits repr inner
          | some bit =>
            have approved := valid.2
            rw [show (place, nested).1.bitOffset = some bit from h] at approved
            have fits := (repr.resolvePacked approved.2.1 inner).2
            simpa [Field.bitExtent, h, Layout.bits] using fits
        change place.bitStart + relative.bitStart + kind.bits ≤
          place.bitStart + Field.bitExtent (place, nested)
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
  rcases h with empty | empty | before | after | bits
  · exact .inr (.inl empty)
  · exact .inl empty
  · exact .inr (.inr (.inr (.inl before)))
  · exact .inr (.inr (.inl after))
  · refine .inr (.inr (.inr (.inr ?_)))
    cases x : a.1.bitOffset <;> cases y : b.1.bitOffset <;> simp_all only
    exact bits.symm

theorem Field.Separate.bitExtents {left right : Field} (apart : left.Separate right)
    (nonemptyLeft : 0 < left.bitExtent) (nonemptyRight : 0 < right.bitExtent) :
    left.1.bitStart + left.bitExtent ≤ right.1.bitStart ∨
      right.1.bitStart + right.bitExtent ≤ left.1.bitStart := by
  have leftLower : left.1.byteOffset * 8 ≤ left.1.bitStart := Nat.le_add_right _ _
  have rightLower : right.1.byteOffset * 8 ≤ right.1.bitStart := Nat.le_add_right _ _
  have leftUpper := left.bitExtent_fits nonemptyLeft
  have rightUpper := right.bitExtent_fits nonemptyRight
  unfold Field.Separate at apart
  rcases apart with zero | zero | before | after | packed
  · omega
  · omega
  · omega
  · omega
  · cases placeLeft : left.1.bitOffset <;> cases placeRight : right.1.bitOffset <;>
      simp only [placeLeft, placeRight] at packed
    all_goals try contradiction
    simpa [Field.bitExtent, placeLeft, placeRight] using packed

/-- A descendant is translated in absolute bits, and stays within its
immediate enclosing field's bit extent. -/
private theorem resolveChild {abi : TargetIntegerABI} {fields : List (StoragePolicy × Schema)}
    {size alignment index : Nat} {placed : List Field} {rest : List Nat} {found : Field}
    (planned : Conforms abi (.record fields) (.record size alignment placed))
    (projection : resolve (.record size alignment placed) (index :: rest) = some found) :
    ∃ outer child, placed[index]? = some outer ∧ Conforms abi child outer.2 ∧
      outer.1.bitStart ≤ found.1.bitStart ∧
      found.1.bitStart + found.bitExtent ≤ outer.1.bitStart + outer.bitExtent ∧
      (rest ≠ [] → ∃ inner, resolve outer.2 rest = some inner ∧
        found.1.bitStart = outer.1.bitStart + inner.1.bitStart ∧ found.bitExtent = inner.bitExtent) := by
  cases atIndex : placed[index]? with
  | none => simp [resolve, atIndex, bind] at projection
  | some outer =>
    obtain ⟨_, child, _, valid, conforms⟩ := planned.field atIndex
    obtain ⟨place, layout⟩ := outer
    cases rest with
    | nil =>
      simp [resolve, atIndex, bind] at projection
      obtain ⟨rfl, rfl⟩ := projection
      exact ⟨_, _, rfl, conforms, Nat.le_refl _, Nat.le_refl _, fun h => (h rfl).elim⟩
    | cons next rest =>
      simp only [resolve, atIndex, bind, pure, Option.bind_eq_some_iff, Prod.exists,
        Option.some.injEq] at projection
      obtain ⟨_, _, outerEq, inner, leaf, projected, rfl⟩ := projection
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj outerEq
      have rebased := place.bitStart_rebase inner
      have extent : Field.bitExtent (place.rebase inner, leaf) = Field.bitExtent (inner, leaf) := by
        cases h : place.bitOffset with
        | none => simp [Field.bitExtent, Placement.rebase, h]
        | some bit =>
          have packed := valid.2
          rw [show (place, layout).1.bitOffset = some bit from h] at packed
          have inherited := (conforms.resolvePacked packed.2.1 projected).1
          simpa [Field.bitExtent, Placement.rebase, h] using congrArg
            (fun packed => if packed then leaf.bits else leaf.size * 8) inherited.symm
      have contained : inner.bitStart + Field.bitExtent (inner, leaf) ≤
          Field.bitExtent (place, layout) := by
        cases h : place.bitOffset with
        | none =>
          have ⟨_, _, _, inside⟩ := resolve_sound conforms projected
          simpa [Field.bitExtent, h] using inside.bitExtent_within
        | some bit =>
          have packed := valid.2
          rw [show (place, layout).1.bitOffset = some bit from h] at packed
          obtain ⟨inherits, fits⟩ := conforms.resolvePacked packed.2.1 projected
          simpa [Field.bitExtent, h, inherits] using fits
      refine ⟨_, _, rfl, conforms, ?_, ?_,
        fun _ => ⟨_, projected, rebased, extent⟩⟩
      · change place.bitStart ≤ (place.rebase inner).bitStart
        exact rebased.symm ▸ Nat.le_add_right _ _
      · change (place.rebase inner).bitStart + Field.bitExtent (place.rebase inner, leaf) ≤
          place.bitStart + Field.bitExtent (place, layout)
        rw [rebased, extent, Nat.add_assoc]
        exact Nat.add_le_add_left contained _

theorem resolve_disjoint_paths {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    {left right : List Nat} {a b : Field}
    (planned : Conforms abi schema layout) (first : resolve layout left = some a)
    (second : resolve layout right = some b) (neither : ¬ left <+: right ∧ ¬ right <+: left)
    (aSize : 0 < a.bitExtent) (bSize : 0 < b.bitExtent) :
    a.1.bitStart + a.bitExtent ≤ b.1.bitStart ∨ b.1.bitStart + b.bitExtent ≤ a.1.bitStart := by
  induction left generalizing schema layout right a b with
  | nil => exact (neither.1 List.nil_prefix).elim
  | cons i tail ih =>
    cases right with
    | nil => exact (neither.2 List.nil_prefix).elim
    | cons j rest =>
      cases planned with
      | integer _ => simp [resolve] at first
      | fixed _ => simp [resolve] at first
      | record align stride count separate positions children =>
        have planned := Conforms.record align stride count separate positions children
        obtain ⟨outer, child, atI, layoutI, lowerI, upperI, stepsI⟩ := resolveChild planned first
        obtain ⟨other, _, atJ, _, lowerJ, upperJ, stepsJ⟩ := resolveChild planned second
        by_cases same : i = j
        · subst j
          have aHasTail : tail ≠ [] := by
            intro empty
            subst tail
            exact neither.1 (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩)
          have bHasTail : rest ≠ [] := by
            intro empty
            subst rest
            exact neither.2 (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩)
          rw [atI] at atJ
          cases atJ
          obtain ⟨innerA, foundA, startA, extentA⟩ := stepsI aHasTail
          obtain ⟨innerB, foundB, startB, extentB⟩ := stepsJ bHasTail
          have apart := ih layoutI foundA foundB
            ⟨fun within => neither.1 (List.cons_prefix_cons.mpr ⟨rfl, within⟩),
              fun within => neither.2 (List.cons_prefix_cons.mpr ⟨rfl, within⟩)⟩
            (extentA ▸ aSize) (extentB ▸ bSize)
          omega
        · have apart : outer.Separate other := by
            rcases Nat.lt_or_gt_of_ne same with less | greater
            · exact pairSeparated planned atI atJ less
            · exact (pairSeparated planned atJ atI greater).symm
          have bounded := apart.bitExtents (by omega) (by omega)
          omega

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
      | fixed _ =>
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
          rcases descent with ⟨kind, slot, rfl, scalar, _, _⟩ | ⟨nonempty, x, hx, sub⟩
          · rcases descentOther with ⟨_, _, rfl, _, _, _⟩ |
              ⟨nonempty, y, hy, ⟨_, _, _, impossible, _, _⟩⟩
            · exact (distinct rfl).elim
            · cases rest <;> simp_all [resolve]
          · rcases descentOther with ⟨_, _, rfl, scalar, _, _⟩ | ⟨_, y, hy, subOther⟩
            · obtain ⟨_, _, _, impossible, _, _⟩ := sub
              cases tail <;> simp_all [resolve]
            · have separated := ih conforms sub subOther (fun equal => distinct (congrArg (List.cons i) equal))
              omega
        · have apart : outer.Separate other ∨ other.Separate outer := by
            rcases Nat.lt_or_gt_of_ne same with less | greater
            · exact .inl (pairSeparated planned lookup lookupOther less)
            · exact .inr (pairSeparated planned lookupOther lookup greater)
          have symmetric : outer.Separate other := apart.elim id Field.Separate.symm
          have leftEnd := outer.bitExtent_fits (by omega)
          have rightEnd := other.bitExtent_fits (by omega)
          have leftStart : outer.1.byteOffset * 8 ≤ outer.1.bitStart := Nat.le_add_right _ _
          have rightStart : other.1.byteOffset * 8 ≤ other.1.bitStart := Nat.le_add_right _ _
          unfold Field.Separate at symmetric
          rcases symmetric with zero | zero | before | after | separateBits
          · omega
          · omega
          · omega
          · omega
          · cases h : outer.1.bitOffset <;> cases k : other.1.bitOffset <;>
              simp only [h, k] at separateBits
            all_goals try contradiction
            simp [Field.bitExtent, h] at upper
            simp [Field.bitExtent, k] at upperOther
            omega

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

/-- Enumerate the leaves initialized by the integer-only record runtime. -/
def Layout.leafPaths : Layout → List (List Nat)
  | .integer .. => [[]]
  | .fixed .. => []
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
    | fixed _ =>
      obtain ⟨_, _, _, found, _, _⟩ := leaf
      simp [resolve] at found
    | record aligned stride count separate positions children =>
      obtain ⟨outer, child, policy, lookup, conforms, _, _, _, _, descent⟩ :=
        lookupLeaf (.record aligned stride count separate positions children) leaf
      apply Layout.mem_childPaths lookup
      rcases descent with ⟨kind, slot, rfl, scalar, _, _⟩ | ⟨_, relative, _, inner⟩
      · simp [scalar, Layout.leafPaths]
      · exact ih conforms inner

theorem Layout.leafPaths_sound {layout : Layout} {path : List Nat}
    (member : path ∈ layout.leafPaths) : ∃ start width, Leaf layout path start width := by
  induction path generalizing layout with
  | nil =>
    cases layout with
    | integer kind slot => exact ⟨0, kind.bits, ⟨0, none⟩, kind, slot, rfl, rfl, rfl⟩
    | fixed width slot => simp [Layout.leafPaths] at member
    | record size align fields =>
      rw [Layout.leafPaths, List.mem_flatMap] at member
      obtain ⟨_, _, found⟩ := member
      obtain ⟨_, _, impossible⟩ := List.mem_map.mp found
      cases impossible
  | cons index path ih =>
    cases layout with
    | integer _ _ => simp [Layout.leafPaths] at member
    | fixed _ _ => simp [Layout.leafPaths] at member
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
        exact ⟨_, _, entry.val.1.rebase place, kind, slot,
          by simp [resolve, lookup, bind, resolves], rfl, rfl⟩

end Aethel.AutomaticLayout
