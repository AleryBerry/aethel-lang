import Aethel.SourceSyntax
import Aethel.PackedMIR

namespace Aethel.SourcePacked

open AutomaticLayout SourceVerification

inductive FieldType where
  | integer (kind : IntegerType)
  | bool
  | unit
  | binary32
  | binary64
  | record (name : String) (flat : Bool) (fields : List (String × FieldType))
  | tagged (name : String) (variants : List (String × FieldType))
  deriving Repr

structure Place where
  root : String
  fields : List String
  deriving Repr

structure PayloadProjection where
  constructorName : String
  index : Nat
  fields : List String
  deriving Repr

structure ResultPlace where
  place : Place
  payload : Option PayloadProjection := none
  deriving Repr

abbrev Task := Place × Option Tokens

inductive Body where
  | done
  | assign (target : Place) (literal : Tokens) (rest : Body)
  | borrow (name : String) (target : Place) (mode : Core.AccessMode) (inside rest : Body)
  | fork (tasks : List Task) (rest : Body)
  deriving Repr

structure Source where
  record : FieldType
  root : String
  initial : List (List Nat × Nat)
  body : Body
  result : ResultPlace
  resultKind : IntegerType
  deriving Repr

private def parseKind : Tokens → Except Error (IntegerType × Tokens)
  | spelling :: rest =>
    match IntegerType.parse? spelling with
    | some kind => .ok (kind, rest)
    | none => .error (.syntax "fixed-width integer type")
  | [] => .error (.syntax "fixed-width integer type")

private abbrev Definitions := List (String × FieldType)

private def parseFieldType (definitions : Definitions) :
    Tokens → Except Error (FieldType × Tokens)
  | "bool" :: rest => .ok (.bool, rest)
  | "Unit" :: rest => .ok (.unit, rest)
  | "f32" :: rest => .ok (.binary32, rest)
  | "f64" :: rest => .ok (.binary64, rest)
  | spelling :: rest =>
    if let some kind := IntegerType.parse? spelling then .ok (.integer kind, rest)
    else match definitions.find? (fun declaration => declaration.1 == spelling) with
      | some (_, ty) => .ok (ty, rest)
      | none => .error (.syntax s!"unknown fixed-width field type {spelling}")
  | [] => .error (.syntax "fixed-width field type")

private def parseFields (definitions : Definitions) :
    Nat → Tokens → Except Error (List (String × FieldType) × Tokens)
  | _, "}" :: rest => .ok ([], rest)
  | 0, _ => .error (.syntax "record field or }")
  | fuel + 1, input => do
    let (name, rest) ← readName false input
    let (kind, rest) ← parseFieldType definitions (← expect [":"] rest)
    let (fields, rest) ← parseFields definitions fuel (← expect [","] rest)
    return ((name, kind) :: fields, rest)

private def parseVariantPayload (definitions : Definitions) :
    Nat → Tokens → Except Error (List FieldType × Tokens)
  | _, ")" :: rest => .ok ([], rest)
  | fuel + 1, input => do
    let (ty, rest) ← parseFieldType definitions input
    match rest with
    | ")" :: rest => return ([ty], rest)
    | _ =>
      let (more, rest) ← parseVariantPayload definitions fuel (← expect [","] rest)
      return (ty :: more, rest)
  | _, _ => .error (.syntax "variant payload type")

private def parseVariants (definitions : Definitions) :
    Nat → Tokens → Except Error (List (String × FieldType) × Tokens)
  | _, "}" :: rest => .ok ([], rest)
  | fuel + 1, input => do
    let (variant, rest) ← readName true input
    let (payload, rest) ← match rest with
      | "(" :: rest => parseVariantPayload definitions fuel rest
      | _ => pure ([], rest)
    let (variants, rest) ← parseVariants definitions fuel (← expect [","] rest)
    let fields := payload.zipIdx.map fun (ty, i) => (toString i, ty)
    return ((variant, .record variant false fields) :: variants, rest)
  | _, _ => .error (.syntax "variant declaration")

private def parseDefinitions : Nat → Definitions → Tokens → Except Error (Definitions × Tokens)
  | fuel + 1, definitions, input => do
    let (flat, declaration) := match input with
      | "@layout" :: "(" :: "flat" :: ")" :: rest => (true, rest)
      | _ => (false, input)
    let "type" :: rest := declaration | return (definitions, input)
    let (name, rest) ← readName true rest
    if definitions.any (fun previous => previous.1 == name) then
      throw (.syntax "duplicate packed type declaration")
    let rest ← expect ["{"] rest
    let (ty, rest) ← match readName true rest with
      | .ok _ => do
        if flat then throw (.syntax "@layout(flat) requires a record type")
        let (variants, rest) ← parseVariants definitions fuel rest
        if ¬ (variants.map Prod.fst).Nodup then throw (.syntax "duplicate variant")
        pure (FieldType.tagged name variants, rest)
      | .error _ => do
        let (fields, rest) ← parseFields definitions fuel rest
        if ¬ (fields.map Prod.fst).Nodup then throw (.syntax "duplicate record fields")
        pure (FieldType.record name flat fields, rest)
    parseDefinitions fuel ((name, ty) :: definitions) rest
  | _, definitions, input => .ok (definitions, input)

def integerCode (kind : IntegerType) (literal : String) : Except Error Nat := do
  let some n := literal.toInt? | throw (.syntax "decimal integer literal")
  let some value := kind.checkedLiteral n
    | throw (.syntax s!"literal in range of {kind.spelling}")
  return (kind.toBits value).toNat

private def packedInteger (kind : IntegerType) : PackedType :=
  match kind with
  | .unsigned width => .range width false 0 ((2 : Int)^width.bits - 1)
  | .signed width =>
    let bound := (2 : Int)^(width.bits - 1)
    .range width true (-bound) (bound - 1)

theorem packedInteger_represents (kind : IntegerType) (bits : BitVec kind.bits) :
    (packedInteger kind).Represents bits.toNat := by
  cases kind with
  | unsigned width =>
    simp only [packedInteger, PackedType.Represents]
    change bits.toNat < 2 ^ width.bits ∧ 0 ≤ (bits.toNat : Int) ∧ (bits.toNat : Int) ≤ (2 : Int)^width.bits - 1
    exact ⟨bits.isLt, by omega, by exact Int.le_sub_one_of_lt (by exact_mod_cast bits.isLt)⟩
  | signed width =>
    simp only [packedInteger, PackedType.Represents]
    change bits.toNat < 2 ^ width.bits ∧
      -(2 : Int)^(width.bits - 1) ≤ (BitVec.ofNat width.bits bits.toNat).toInt ∧
      (BitVec.ofNat width.bits bits.toNat).toInt ≤ (2 : Int)^(width.bits - 1) - 1
    exact ⟨bits.isLt, BitVec.le_toInt _, BitVec.toInt_le⟩

theorem integerCode_sound {kind : IntegerType} {literal : String} {code : Nat}
    (parsed : integerCode kind literal = .ok code) :
    ∃ (number : Int) (value : kind.Value),
      literal.toInt? = some number ∧
      kind.Fits number ∧ kind.checkedLiteral number = some value ∧
      code = (kind.toBits value).toNat ∧ (packedInteger kind).Represents code := by
  unfold integerCode at parsed
  cases read : literal.toInt? with
  | none => simp [read] at parsed
  | some number =>
    cases checked : kind.checkedLiteral number with
    | none => simp [read, checked] at parsed
    | some value =>
      have same : (kind.toBits value).toNat = code := by
        simpa [read, checked, bind, Except.bind, pure, Except.pure] using parsed
      subst code
      have fits := (IntegerType.checkedLiteral_correct kind number).mp (by simp [checked])
      exact ⟨number, value, rfl, fits, checked, rfl,
        packedInteger_represents kind (kind.toBits value)⟩

theorem integerCode_decodes {kind : IntegerType} {literal : String} {code : Nat}
    (parsed : integerCode kind literal = .ok code) :
    ∃ value, (packedInteger kind).decodeCode code = some value ∧ value.val.toNat = code := by
  obtain ⟨number, value, _, _, _, same, valid⟩ := integerCode_sound parsed
  have bound : code < 2 ^ (packedInteger kind).width := by
    rw [same]
    have widths : (packedInteger kind).width = kind.bits := by
      cases kind <;> simp [packedInteger, PackedType.width, IntegerType.bits, IntegerType.width]
    rw [widths]
    exact (kind.toBits value).isLt
  exact PackedType.decodeCode_complete bound valid

private def valueSlot (ty : PackedType) : IntegerSlot :=
  let bytes := (ty.width + 7) / 8
  let alignment := match ty with
    | .addressable alignment _ => alignment
    | _ => naturalAlignment bytes
  ⟨alignUp bytes alignment, alignment⟩

private def carriesAddresses (ty : PackedType) : Bool := !ty.requiredAddresses.isEmpty

private def compactOffsets (offset : Nat) : List PackedType → List Nat
  | [] => []
  | first :: rest => offset :: compactOffsets (offset + first.width) rest

private def componentCode (offset code : Nat) : Nat :=
  code * 2 ^ offset

private theorem compactProduct_code (fields : List (PackedType × Nat)) (offset : Nat)
    (valid : ∀ field ∈ fields, field.2 < 2 ^ field.1.width ∧ field.1.Represents field.2) :
    let types := fields.map Prod.fst
    let product := types.foldr PackedType.product (.raw 0)
    let code := (List.zipWith componentCode (compactOffsets offset types) (fields.map Prod.snd)).sum
    ∃ unshifted, code = unshifted * 2 ^ offset ∧
      unshifted < 2 ^ product.width ∧ product.Represents unshifted := by
  induction fields generalizing offset with
  | nil =>
    exact ⟨0, by simp [compactOffsets], by simp [PackedType.width], by simp [PackedType.Represents]⟩
  | cons field rest ih =>
    obtain ⟨fits, represents⟩ := valid field (by simp)
    obtain ⟨tail, tailShift, tailFits, tailRepresents⟩ :=
      ih (offset + field.1.width) (fun child member => valid child (by simp [member]))
    refine ⟨field.2 + tail * 2 ^ field.1.width, ?_,
      PackedType.product_code_fits fits tailFits,
      PackedType.product_represents fits represents tailRepresents⟩
    simp only [List.map_cons, compactOffsets, List.zipWith_cons_cons, List.sum_cons, componentCode]
    rw [tailShift, Nat.pow_add, Nat.add_mul]
    ac_rfl

private structure AlignedProductState where
  body : PackedType := .raw 0
  ending : Nat := 0
  alignment : Nat := 1
  offsets : List Nat := []

private def AlignedProductState.push (state : AlignedProductState) (ty : PackedType) :
    AlignedProductState :=
  let slot := valueSlot ty
  let start := alignUp state.ending slot.alignment
  let placed := PackedType.padding ((start - state.ending) * 8) (slot.size * 8 - ty.width)
    (.addressable slot.alignment ty)
  ⟨.product state.body placed, start + slot.size, max state.alignment slot.alignment,
    (start * 8) :: state.offsets⟩

private def AlignedProductState.finish (state : AlignedProductState) : PackedType :=
  let tail := (alignUp state.ending state.alignment - state.ending) * 8
  .addressable state.alignment (.padding 0 tail state.body)

private theorem AlignedProductState.push_width (state : AlignedProductState) (ty : PackedType)
    (width : state.body.width = state.ending * 8) :
    (state.push ty).body.width = (state.push ty).ending * 8 := by
  have capacity : ty.width ≤ (valueSlot ty).size * 8 := by
    unfold valueSlot alignUp
    dsimp only
    omega
  simp only [push, PackedType.width, width]
  unfold alignUp
  omega

private def alignedProduct (flat : Bool) (fields : List PackedType) : Bool :=
  flat || fields.any carriesAddresses

/-- An explicitly flat record or a variant product with a protected child
gives each child its aligned byte slot. Other products use contiguous bits. -/
private def productEncoding (flat : Bool) (fields : List PackedType) : PackedType × List Nat :=
  if alignedProduct flat fields then
    let state := fields.foldl AlignedProductState.push {}
    (state.finish, state.offsets.reverse)
  else
    (fields.foldr .product (.raw 0), compactOffsets 0 fields)

private theorem AlignedProductState.push_code (state : AlignedProductState)
    (ty : PackedType) (previous code : Nat) (width : state.body.width = state.ending * 8)
    (previousFits : previous < 2 ^ state.body.width) (previousValid : state.body.Represents previous)
    (codeFits : code < 2 ^ ty.width) (codeValid : ty.Represents code) :
    let next := state.push ty
    let appended := previous + componentCode (alignUp state.ending (valueSlot ty).alignment * 8) code
    next.body.width = next.ending * 8 ∧
      appended < 2 ^ next.body.width ∧ next.body.Represents appended := by
  let slot := valueSlot ty
  let start := alignUp state.ending slot.alignment
  let before := (start - state.ending) * 8
  let payload := PackedType.addressable slot.alignment ty
  let placed := PackedType.padding before (slot.size * 8 - ty.width) payload
  have leStart : state.ending ≤ start := by
    unfold start alignUp
    omega
  have shift : before + state.body.width = start * 8 := by
    unfold before
    omega
  have paddedFits : code * 2 ^ before < 2 ^ placed.width :=
    PackedType.padding_code_fits (payload := payload) (by simpa [payload, PackedType.width] using codeFits)
  have paddedValid : placed.Represents (code * 2 ^ before) :=
    PackedType.padding_represents (payload := payload) (by simpa [payload, PackedType.width] using codeFits)
      (by simpa [payload, PackedType.Represents] using codeValid)
  change (PackedType.product state.body placed).width = (start + slot.size) * 8 ∧
    previous + code * 2 ^ (start * 8) < 2 ^ (PackedType.product state.body placed).width ∧
    (PackedType.product state.body placed).Represents (previous + code * 2 ^ (start * 8))
  rw [← shift, Nat.pow_add, ← Nat.mul_assoc]
  exact ⟨state.push_width ty width, PackedType.product_code_fits previousFits paddedFits,
    PackedType.product_represents previousFits previousValid paddedValid⟩

private theorem AlignedProductState.fold_code (fields : List (PackedType × Nat))
    (state : AlignedProductState) (previous : List Nat)
    (length : state.offsets.length = previous.length) (width : state.body.width = state.ending * 8)
    (valid : ∀ field ∈ fields, field.2 < 2 ^ field.1.width ∧ field.1.Represents field.2)
    (previousValid :
      let code := (List.zipWith componentCode state.offsets.reverse previous.reverse).sum
      code < 2 ^ state.body.width ∧ state.body.Represents code) :
    let final := (fields.map Prod.fst).foldl AlignedProductState.push state
    let code := (List.zipWith componentCode final.offsets.reverse (previous.reverse ++ fields.map Prod.snd)).sum
    code < 2 ^ final.body.width ∧ final.body.Represents code := by
  induction fields generalizing state previous with
  | nil => simpa using previousValid
  | cons field rest ih =>
    let next := state.push field.1
    let code := (List.zipWith componentCode state.offsets.reverse previous.reverse).sum
    obtain ⟨fits, represents⟩ := valid field (by simp)
    obtain ⟨nextWidth, nextFits, nextValid⟩ :=
      state.push_code field.1 code field.2 width previousValid.1 previousValid.2 fits represents
    have nextLength : next.offsets.length = (field.2 :: previous).length := by
      simp [next, push, length]
    have nextCode :
        (List.zipWith componentCode next.offsets.reverse (field.2 :: previous).reverse).sum =
          code + componentCode (alignUp state.ending (valueSlot field.1).alignment * 8) field.2 := by
      change (List.zipWith componentCode
        ((alignUp state.ending (valueSlot field.1).alignment * 8) :: state.offsets).reverse
        (field.2 :: previous).reverse).sum = _
      rw [List.reverse_cons, List.reverse_cons, List.zipWith_append (by simpa using length)]
      simp [code, List.sum_append]
    have result := ih next (field.2 :: previous) nextLength nextWidth
      (fun child member => valid child (by simp [member])) (by rw [nextCode]; exact ⟨nextFits, nextValid⟩)
    simpa only [next, List.map_cons, List.foldl_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append] using result

theorem productEncoding_decodes (flat : Bool) (fields : List (PackedType × Nat))
    (valid : ∀ field ∈ fields, field.2 < 2 ^ field.1.width ∧ field.1.Represents field.2) :
    let (ty, offsets) := productEncoding flat (fields.map Prod.fst)
    let code := (List.zipWith componentCode offsets (fields.map Prod.snd)).sum
    ∃ value, ty.decodeCode code = some value ∧ value.val.toNat = code := by
  generalize eq : productEncoding flat (fields.map Prod.fst) = encoding
  by_cases aligned : alignedProduct flat (fields.map Prod.fst)
  · rw [productEncoding, ite_eq_left aligned] at eq
    subst encoding
    let state := (fields.map Prod.fst).foldl AlignedProductState.push {}
    let code := (List.zipWith componentCode state.offsets.reverse (fields.map Prod.snd)).sum
    have initialWidth : ({} : AlignedProductState).body.width = ({} : AlignedProductState).ending * 8 := by
      simp [PackedType.width]
    have represented : code < 2 ^ state.body.width ∧ state.body.Represents code := by
      have preserved := AlignedProductState.fold_code fields {} [] rfl initialWidth valid
        (by simp [PackedType.width, PackedType.Represents])
      simpa [code, state] using preserved
    change ∃ value, state.finish.decodeCode code = some value ∧ value.val.toNat = code
    apply PackedType.decodeCode_complete
    · simpa [AlignedProductState.finish, PackedType.width] using
        (PackedType.padding_code_fits (before := 0)
          (after := (alignUp state.ending state.alignment - state.ending) * 8) represented.1)
    · simpa [AlignedProductState.finish, PackedType.Represents.eq_6] using
        (PackedType.padding_represents (before := 0)
          (after := (alignUp state.ending state.alignment - state.ending) * 8) represented.1 represented.2)
  · rw [productEncoding, ite_eq_right aligned] at eq
    subst encoding
    obtain ⟨code, eqCode, fits, represents⟩ := compactProduct_code fields 0 valid
    simp only [Nat.pow_zero, Nat.mul_one] at eqCode
    dsimp only
    rw [eqCode]
    exact PackedType.decodeCode_complete fits represents

private def compactFieldSteps (index : Nat) : List PackedType.FieldStep :=
  List.replicate index .right ++ [.left]

private def alignedBodyFieldSteps (length index : Nat) : List PackedType.FieldStep :=
  List.replicate (length - 1 - index) .left ++ [.right, .unpad, .unwrapAddressable]

private def productFieldSteps (flat : Bool) (fields : List PackedType) (index : Fin fields.length) :
    List PackedType.FieldStep :=
  if alignedProduct flat fields then
    [.unwrapAddressable, .unpad] ++ alignedBodyFieldSteps fields.length index.val
  else compactFieldSteps index.val

private theorem compactProduct_field (fields : List PackedType) (base index : Nat) {field : PackedType}
    (declared : fields[index]? = some field) :
    ∃ offset, (compactOffsets base fields)[index]? = some (base + offset) ∧
      (fields.foldr PackedType.product (.raw 0)).fieldAt (compactFieldSteps index) =
        some (offset, field) := by
  induction fields generalizing base index with
  | nil => simp at declared
  | cons first rest ih =>
    cases index with
    | zero =>
      cases Option.some.inj declared
      exact ⟨0, by simp [compactOffsets], rfl⟩
    | succ index =>
      obtain ⟨offset, located, projected⟩ := ih (base + first.width) index declared
      exact ⟨first.width + offset, by simpa [compactOffsets, Nat.add_assoc] using located, by
        change (first.product (rest.foldr PackedType.product (.raw 0))).fieldAt
          (.right :: compactFieldSteps index) = _
        simp [PackedType.fieldAt, PackedType.fieldStep, bind, pure, projected]⟩

private theorem AlignedProductState.fold_width (fields : List PackedType) (state : AlignedProductState)
    (width : state.body.width = state.ending * 8) :
    (fields.foldl AlignedProductState.push state).body.width =
      (fields.foldl AlignedProductState.push state).ending * 8 := by
  induction fields generalizing state with
  | nil => exact width
  | cons head rest ih => exact ih _ (state.push_width head width)

private theorem AlignedProductState.fold_offsets_length (fields : List PackedType) (state : AlignedProductState) :
    (fields.foldl AlignedProductState.push state).offsets.length = state.offsets.length + fields.length := by
  induction fields generalizing state with
  | nil => simp
  | cons head rest ih =>
    rw [List.foldl_cons, ih]
    simp only [push, List.length_cons]
    omega

private theorem alignedProduct_field (fields : List PackedType) (index : Nat) {field : PackedType}
    (declared : fields[index]? = some field) :
    let state := fields.foldl AlignedProductState.push {}
    ∃ offset, state.offsets.reverse[index]? = some offset ∧
      state.body.fieldAt (alignedBodyFieldSteps fields.length index) = some (offset, field) := by
  generalize reversedEq : fields.reverse = reversed
  have original : reversed.reverse = fields := by simp [← reversedEq]
  subst fields
  clear reversedEq
  induction reversed with
  | nil => simp at declared
  | cons last reversed ih =>
    rw [List.reverse_cons] at declared ⊢
    dsimp only
    let state := reversed.reverse.foldl AlignedProductState.push {}
    have width : state.body.width = state.ending * 8 :=
      AlignedProductState.fold_width _ _ (by simp [PackedType.width])
    have length : state.offsets.reverse.length = reversed.reverse.length := by
      rw [List.length_reverse, AlignedProductState.fold_offsets_length]
      exact Nat.zero_add _
    let start := alignUp state.ending (valueSlot last).alignment
    rw [List.foldl_append]
    change ∃ offset, (state.push last).offsets.reverse[index]? = some offset ∧
      (state.push last).body.fieldAt (alignedBodyFieldSteps (reversed.reverse ++ [last]).length index) =
        some (offset, field)
    have offsets : (state.push last).offsets.reverse = state.offsets.reverse ++ [start * 8] := by
      simp only [AlignedProductState.push, List.reverse_cons, start]
    by_cases beforeLast : index < reversed.reverse.length
    · rw [List.getElem?_append_left beforeLast] at declared
      obtain ⟨offset, located, projected⟩ := ih declared
      refine ⟨offset, ?_, ?_⟩
      · rw [offsets, List.getElem?_append_left (by omega)]
        exact located
      · have shifted : (reversed.reverse ++ [last]).length - 1 - index =
            (reversed.reverse.length - 1 - index) + 1 := by
          simp only [List.length_append, List.length_singleton]
          omega
        change state.body.fieldAt (alignedBodyFieldSteps reversed.reverse.length index) =
          some (offset, field) at projected
        simp only [alignedBodyFieldSteps] at projected
        simp only [alignedBodyFieldSteps, shifted, List.replicate_succ, List.cons_append,
          AlignedProductState.push, PackedType.fieldAt, PackedType.fieldStep, bind, pure, Option.bind_some,
          Nat.zero_add, projected]
    · have lastIndex : index = reversed.reverse.length := by
        have within := (List.getElem?_eq_some_iff.mp declared).1
        simp only [List.length_append, List.length_singleton] at within
        omega
      rw [List.getElem?_append_right (by omega), lastIndex, Nat.sub_self] at declared
      have same : last = field := Option.some.inj declared
      subst field
      refine ⟨start * 8, ?_, ?_⟩
      · rw [offsets, List.getElem?_append_right (by omega)]
        simp [lastIndex, length]
      · have noLeft : (reversed.reverse ++ [last]).length - 1 - index = 0 := by
          simp [lastIndex]
        have aligned : state.ending ≤ start := by unfold start alignUp; omega
        rw [alignedBodyFieldSteps, noLeft]
        simp [AlignedProductState.push, PackedType.fieldAt,
          PackedType.fieldStep, bind, pure, width]
        change state.ending * 8 + (start - state.ending) * 8 = start * 8
        omega

/-- The structural selector for a declaration index resolves to the same bit
offset and field type used to encode that component. -/
theorem productFieldSteps_correct (flat : Bool) (fields : List PackedType) (index : Nat)
    {field : PackedType} (declared : fields[index]? = some field) :
    ∃ offset, (productEncoding flat fields).2[index]? = some offset ∧
      (productEncoding flat fields).1.fieldAt
        (productFieldSteps flat fields ⟨index, (List.getElem?_eq_some_iff.mp declared).1⟩) =
          some (offset, field) := by
  by_cases aligned : alignedProduct flat fields
  · simp only [productEncoding, productFieldSteps, ite_eq_left aligned]
    obtain ⟨offset, located, projected⟩ := alignedProduct_field fields index declared
    exact ⟨offset, located, by
      simp [AlignedProductState.finish, PackedType.fieldAt, PackedType.fieldStep, bind, pure, projected]⟩
  · simp only [productEncoding, productFieldSteps, ite_eq_right aligned]
    obtain ⟨offset, located, projected⟩ := compactProduct_field fields 0 index declared
    exact ⟨offset, by simpa using located, projected⟩

private def variantSlot (variants : List PackedType) (tagBytes : Nat) : Nat × Nat :=
  variants.foldl (fun (largest, alignment) ty =>
    let slot := valueSlot ty
    (max largest slot.size, max alignment slot.alignment)) (0, naturalAlignment tagBytes)

/-- Keep the tag first and place the union payload at its common alignment.
The constructor's value occupies the front of that payload and padding is zero. -/
private def variantEncoding (variants : List PackedType) : PackedType × Nat :=
  let tag := ADTLayout.minTagBits variants.length
  if variants.any carriesAddresses then
    let (largest, alignment) := variantSlot variants ((tag + 7) / 8)
    let start := alignUp ((tag + 7) / 8) alignment
    let ending := alignUp (start + largest) alignment
    let padded := variants.map (fun ty =>
      PackedType.padding (start * 8 - tag) ((ending - start) * 8 - ty.width) ty)
    (.addressable alignment (.tagged padded), start * 8)
  else
    (.tagged variants, tag)

theorem variantEncoding_decodes {variants : List PackedType} {tag code : Nat} {payload : PackedType}
    (selected : variants[tag]? = some payload)
    (fits : code < 2 ^ payload.width) (valid : payload.Represents code) :
    let (ty, start) := variantEncoding variants
    ∃ value, ty.decodeCode (tag + code * 2 ^ start) = some value ∧
      value.val.toNat = tag + code * 2 ^ start := by
  generalize eq : variantEncoding variants = encoding
  by_cases addresses : variants.any carriesAddresses
  · rw [variantEncoding, ite_eq_left addresses] at eq
    subst encoding
    let bits := ADTLayout.minTagBits variants.length
    let (largest, alignment) := variantSlot variants ((bits + 7) / 8)
    let start := alignUp ((bits + 7) / 8) alignment
    let ending := alignUp (start + largest) alignment
    let pad := fun ty : PackedType =>
      PackedType.padding (start * 8 - bits) ((ending - start) * 8 - ty.width) ty
    change ∃ value, (PackedType.addressable alignment (.tagged (variants.map pad))).decodeCode
        (tag + code * 2 ^ (start * 8)) = some value ∧ value.val.toNat = tag + code * 2 ^ (start * 8)
    have startBound : bits ≤ start * 8 := by
      unfold start alignUp
      omega
    have padSelected : (variants.map pad)[tag]? = some (pad payload) := by
      simp [List.getElem?_map, selected]
    have power : 2 ^ (start * 8) = 2 ^ (start * 8 - bits) * 2 ^ bits := by
      rw [← Nat.pow_add, Nat.sub_add_cancel startBound]
    have padFits : code * 2 ^ (start * 8 - bits) < 2 ^ (pad payload).width :=
      PackedType.padding_code_fits fits
    have padValid : (pad payload).Represents (code * 2 ^ (start * 8 - bits)) :=
      PackedType.padding_represents fits valid
    have sameLength : (variants.map pad).length = variants.length := List.length_map ..
    rw [power, ← Nat.mul_assoc]
    apply PackedType.decodeCode_complete
    · simpa only [PackedType.width, sameLength] using PackedType.tagged_code_fits padSelected padFits
    · simpa only [PackedType.Represents.eq_6, sameLength] using PackedType.tagged_represents padSelected padValid
  · rw [variantEncoding, ite_eq_right addresses] at eq
    subst encoding
    exact PackedType.tagged_decodeCode selected fits valid

private def FieldType.encoding : FieldType → Bool → PackedType
  | .integer kind, _ => packedInteger kind
  | .bool, _ => .raw 1
  | .unit, _ => .raw 0
  | .binary32, _ => .raw 32
  | .binary64, _ => .raw 64
  | .record _ flat fields, inherited =>
    let forceFlat := flat || inherited
    (productEncoding forceFlat (fields.attach.map fun field => encoding field.val.2 forceFlat)).1
  | .tagged _ variants, _ =>
    (variantEncoding (variants.attach.map fun variant => encoding variant.val.2 false)).1
termination_by ty _ => sizeOf ty
decreasing_by
  · have within := List.sizeOf_lt_of_mem field.property
    have child : sizeOf field.val.2 < sizeOf field.val := by
      cases field.val
      simp
      omega
    simp_wf
    omega
  · have within := List.sizeOf_lt_of_mem variant.property
    have child : sizeOf variant.val.2 < sizeOf variant.val := by
      cases variant.val
      simp
      omega
    simp_wf
    omega

private theorem FieldType.record_encoding (name : String) (flat inherited : Bool)
    (fields : List (String × FieldType)) :
    (FieldType.record name flat fields).encoding inherited =
      (productEncoding (flat || inherited)
        (fields.map fun field => field.2.encoding (flat || inherited))).1 := by
  rw [FieldType.encoding]
  rw [List.attach_map_val (f := fun field : String × FieldType => field.2.encoding (flat || inherited))]

private def decimalParts (suffix : String) : Tokens →
    Except Error ((Bool × Nat × Int) × Tokens)
  | literal :: rest => do
    let [whole, fraction] := literal.splitOn "."
      | throw (.syntax s!"decimal {suffix} literal")
    let negative := whole.startsWith "-"
    let digits := if negative then String.ofList whole.toList.tail else whole
    if digits.isEmpty || fraction.isEmpty then throw (.syntax "decimal significand digits")
    let some significand := (digits ++ fraction).toNat? | throw (.syntax s!"decimal {suffix} literal")
    let rest ← match rest with
      | "as" :: tyTok :: more =>
        if tyTok == suffix then pure more else throw (.syntax s!"decimal {suffix} literal")
      | _ => pure rest
    return ((negative, significand, -(Int.ofNat fraction.length)), rest)
  | _ => .error (.syntax s!"decimal {suffix} literal")

private def parseComponents (parse : Bool → α → Tokens → Except Error (Nat × Tokens)) :
    List α → List Nat → Nat → Tokens → Except Error (Nat × Tokens)
  | [], _, code, input => .ok (code, input)
  | field :: fields, offset :: offsets, code, input => do
    let (next, rest) ← parse fields.isEmpty field input
    parseComponents parse fields offsets (code + componentCode offset next) rest
  | _ :: _, [], _, _ => .error (.syntax "missing component encoding offset")

private theorem parseComponents_codes {α : Type}
    {parse : Bool → α → Tokens → Except Error (Nat × Tokens)} {encode : α → PackedType}
    (componentValid : ∀ last field input code rest, parse last field input = .ok (code, rest) →
      code < 2 ^ (encode field).width ∧ (encode field).Represents code)
    {fields : List α} {offsets : List Nat} {accumulator code : Nat} {input rest : Tokens}
    (parsed : parseComponents parse fields offsets accumulator input = .ok (code, rest)) :
    ∃ values : List (PackedType × Nat), values.map Prod.fst = fields.map encode ∧
      (∀ field ∈ values, field.2 < 2 ^ field.1.width ∧ field.1.Represents field.2) ∧
      code = accumulator + (List.zipWith componentCode offsets (values.map Prod.snd)).sum := by
  induction fields generalizing offsets accumulator input with
  | nil =>
    cases parsed
    exact ⟨[], rfl, by simp, by simp⟩
  | cons field fields ih =>
    cases offsets with
    | nil => simp [parseComponents] at parsed
    | cons offset offsets =>
      cases child : parse fields.isEmpty field input with
      | error error => simp [parseComponents, child, bind, Except.bind] at parsed
      | ok result =>
        obtain ⟨next, remainder⟩ := result
        have nextValid := componentValid fields.isEmpty field input next remainder child
        obtain ⟨values, sameTypes, valid, encoded⟩ := ih (by
          simpa [parseComponents, child, bind, Except.bind] using parsed)
        refine ⟨(encode field, next) :: values, by simp [sameTypes], ?_, ?_⟩
        · intro other member
          rcases List.mem_cons.mp member with rfl | tail
          · exact nextValid
          · exact valid other tail
        · simpa [Nat.add_assoc] using encoded

private def parseProduct (flat : Bool) (fields : List (String × FieldType))
    (parse : Bool → String × FieldType → Tokens → Except Error (Nat × Tokens))
    (input : Tokens) : Except Error (Nat × Tokens) :=
  let (_, offsets) := productEncoding flat (fields.map fun field => field.2.encoding flat)
  parseComponents parse fields offsets 0 input

private theorem parseProduct_decodes {flat : Bool} {fields : List (String × FieldType)}
    {parse : Bool → String × FieldType → Tokens → Except Error (Nat × Tokens)}
    (componentValid : ∀ last field input code rest, parse last field input = .ok (code, rest) →
      code < 2 ^ (field.2.encoding flat).width ∧ (field.2.encoding flat).Represents code)
    {input rest : Tokens} {code : Nat} (parsed : parseProduct flat fields parse input = .ok (code, rest)) :
    let ty := (productEncoding flat (fields.map fun field => field.2.encoding flat)).1
    ∃ value, ty.decodeCode code = some value ∧ value.val.toNat = code := by
  unfold parseProduct at parsed
  obtain ⟨values, sameTypes, valid, sameCode⟩ := parseComponents_codes componentValid parsed
  have decoded := productEncoding_decodes flat values valid
  rw [sameTypes] at decoded
  dsimp only at decoded ⊢
  rw [Nat.zero_add] at sameCode
  rw [sameCode]
  exact decoded

private theorem except_bind_ok {value : Except Error α} {next : α → Except Error β} {result : β}
    (ran : value.bind next = .ok result) : ∃ input, value = .ok input ∧ next input = .ok result := by
  cases value with
  | error err => cases ran
  | ok input => exact ⟨input, rfl, ran⟩

private theorem literalCode_valid {ty : PackedType} {code : Nat}
    (decoded : ∃ value, ty.decodeCode code = some value ∧ value.val.toNat = code) :
    code < 2 ^ ty.width ∧ ty.Represents code := by
  obtain ⟨value, _, same⟩ := decoded
  rw [← same]
  exact ⟨value.val.isLt, value.property⟩

private def consumeOptionalAs (expected : String) : Tokens → Except Error Tokens
  | "as" :: tyTok :: more =>
    if tyTok == expected then .ok more else .error (.syntax s!"literal of type {expected}")
  | rest => .ok rest

private def parseCode : Nat → FieldType → Bool → Tokens → Except Error (Nat × Tokens)
  | _ + 1, .integer kind, _, literal :: rest => do
    let code ← integerCode kind literal
    let rest ← consumeOptionalAs kind.spelling rest
    return (code, rest)
  | _ + 1, .bool, _, "true" :: rest => .ok (1, rest)
  | _ + 1, .bool, _, "false" :: rest => .ok (0, rest)
  | _ + 1, .unit, _, "(" :: ")" :: rest => .ok (0, rest)
  | _ + 1, .binary32, _, input => do
    let ((negative, significand, exponent), rest) ← decimalParts "f32" input
    let float := Float32.Model.ofScientific significand exponent
    return ((if negative then -float else float).toBits.toNat, rest)
  | _ + 1, .binary64, _, input => do
    let ((negative, significand, exponent), rest) ← decimalParts "f64" input
    let float := Float.Model.ofScientific significand exponent
    return ((if negative then -float else float).toBits.toNat, rest)
  | fuel + 1, .record name flat fields, inherited, input => do
    let start ← expect [name, "{"] input
    let forceFlat := flat || inherited
    let (encoded, rest) ← parseProduct forceFlat fields (fun _ (name, ty) rest => do
      let (next, rest) ← parseCode fuel ty forceFlat (← expect [name, ":"] rest)
      pure (next, ← expect [","] rest)) start
    return (encoded, ← expect ["}"] rest)
  | fuel + 1, .tagged _ variants, _, input => do
    let (name, rest) ← readName true input
    let some tag := variants.findIdx? (fun variant => variant.1 == name)
      | throw (.syntax s!"unknown variant {name}")
    let some (_, .record _ flat components) := variants[tag]?
      | throw (.syntax "invalid variant payload")
    if components.isEmpty then return (tag, rest)
    let start ← expect ["("] rest
    let (payload, rest) ← parseProduct flat components
      (fun last (_, ty) rest => do
        let (next, rest) ← parseCode fuel ty flat rest
        let delimiter := if last then .ok rest else expect [","] rest
        let rest ← delimiter
        pure (next, rest)) start
    let (_, payloadStart) := variantEncoding (variants.map (fun (_, variant) => variant.encoding false))
    return (tag + payload * 2^payloadStart, ← expect [")"] rest)
  | _, _, _, _ => .error (.syntax "fixed-width initializer")

/-- Every accepted fixed-width literal fits and represents its declared packed type. -/
theorem parseCode_valid (fuel : Nat) (ty : FieldType) (flat : Bool) (input : Tokens)
    {code : Nat} {rest : Tokens} (parsed : parseCode fuel ty flat input = .ok (code, rest)) :
    code < 2 ^ (ty.encoding flat).width ∧ (ty.encoding flat).Represents code := by
  induction fuel generalizing ty flat input code rest with
  | zero => simp [parseCode] at parsed
  | succ fuel ih =>
    cases ty with
    | integer kind =>
      cases input with
      | nil => simp [parseCode] at parsed
      | cons literal remaining =>
        simp only [parseCode] at parsed
        obtain ⟨number, read, next⟩ := except_bind_ok parsed
        obtain ⟨rem, _, eq⟩ := except_bind_ok next
        cases eq
        simpa only [FieldType.encoding] using literalCode_valid (integerCode_decodes read)
    | bool =>
      cases input with
      | nil => simp [parseCode] at parsed
      | cons token remaining =>
        by_cases yes : token = "true"
        · subst token
          simp only [parseCode, Except.ok.injEq, Prod.mk.injEq] at parsed
          obtain ⟨rfl, _⟩ := parsed
          simp [FieldType.encoding, PackedType.width, PackedType.Represents]
        · by_cases no : token = "false"
          · subst token
            simp only [parseCode, Except.ok.injEq, Prod.mk.injEq] at parsed
            obtain ⟨rfl, _⟩ := parsed
            simp [FieldType.encoding, PackedType.width, PackedType.Represents]
          · rw [parseCode.eq_9] at parsed <;> simp_all
    | unit =>
      cases input with
      | nil => simp [parseCode] at parsed
      | cons openParen input =>
        cases input with
        | nil => simp [parseCode] at parsed
        | cons closeParen remaining =>
          by_cases opened : openParen = "("
          · subst openParen
            by_cases closed : closeParen = ")"
            · subst closeParen
              simp only [parseCode, Except.ok.injEq, Prod.mk.injEq] at parsed
              obtain ⟨rfl, _⟩ := parsed
              simp [FieldType.encoding, PackedType.width, PackedType.Represents]
            · rw [parseCode.eq_9] at parsed <;> simp_all
          · rw [parseCode.eq_9] at parsed <;> simp_all
    | binary32 =>
      simp only [parseCode] at parsed
      obtain ⟨⟨⟨negative, significand, exponent⟩, remaining⟩, _, eq⟩ := except_bind_ok parsed
      cases eq
      simp only [FieldType.encoding, PackedType.width, PackedType.Represents]
      exact ⟨UInt32.toNat_lt _, UInt32.toNat_lt _⟩
    | binary64 =>
      simp only [parseCode] at parsed
      obtain ⟨⟨⟨negative, significand, exponent⟩, remaining⟩, _, eq⟩ := except_bind_ok parsed
      cases eq
      simp only [FieldType.encoding, PackedType.width, PackedType.Represents]
      exact ⟨UInt64.toNat_lt _, UInt64.toNat_lt _⟩
    | record name force fields =>
      simp only [parseCode] at parsed
      obtain ⟨start, _, next⟩ := except_bind_ok parsed
      obtain ⟨⟨assembled, remaining⟩, product, next⟩ := except_bind_ok next
      obtain ⟨endTokens, _, eq⟩ := except_bind_ok next
      cases eq
      have decoded := parseProduct_decodes (fun last field tokens value remainder accepted => by
        rcases field with ⟨fieldName, fieldType⟩
        obtain ⟨start, _, next⟩ := except_bind_ok accepted
        obtain ⟨⟨number, remaining⟩, child, next⟩ := except_bind_ok next
        obtain ⟨endTokens, _, eq⟩ := except_bind_ok next
        cases eq
        exact ih fieldType (force || flat) start child) product
      simpa only [FieldType.record_encoding] using literalCode_valid decoded
    | tagged name variants =>
      simp only [parseCode] at parsed
      obtain ⟨⟨constructor, afterName⟩, _, next⟩ := except_bind_ok parsed
      cases found : variants.findIdx? (fun variant => variant.1 == constructor) with
      | none => simp [found] at next
      | some tag =>
        simp only [found] at next
        cases selected : variants[tag]? with
        | none => simp [selected] at next
        | some entry =>
          obtain ⟨label, payloadType⟩ := entry
          cases payloadType with
          | record payloadName payloadFlat components =>
            simp only [selected] at next
            let encode := fun entry : String × FieldType => entry.2.encoding false
            have chosen : (variants.map encode)[tag]? =
                some ((FieldType.record payloadName payloadFlat components).encoding false) := by
              simp [List.getElem?_map, selected, encode]
            have variantTypes : (variants.attach.map fun entry => entry.val.2.encoding false) =
                variants.map encode := by
              exact List.attach_map_val (f := encode)
            have payloadEncoding : (FieldType.record payloadName payloadFlat components).encoding false =
                (productEncoding payloadFlat (components.map fun field => field.2.encoding payloadFlat)).1 := by
              simp only [FieldType.record_encoding, Bool.or_false]
            by_cases empty : components.isEmpty
            · simp only [ite_eq_left empty] at next
              have eq : (tag, afterName) = (code, rest) := Except.ok.inj next
              have sameCode : tag = code := congrArg Prod.fst eq
              rw [← sameCode]
              have emptyComponents : components = [] := List.isEmpty_iff.mp empty
              have emptyCode :
                  0 < 2 ^ ((FieldType.record payloadName payloadFlat components).encoding false).width ∧
                    ((FieldType.record payloadName payloadFlat components).encoding false).Represents 0 := by
                apply literalCode_valid
                rw [payloadEncoding, emptyComponents]
                have decoded := productEncoding_decodes payloadFlat [] (by simp)
                let ty := (productEncoding payloadFlat []).1
                let offsets := (productEncoding payloadFlat []).2
                change ∃ value, ty.decodeCode 0 = some value ∧ value.val.toNat = 0
                change ∃ value, ty.decodeCode (List.zipWith componentCode offsets []).sum = some value ∧
                  value.val.toNat = (List.zipWith componentCode offsets []).sum at decoded
                simpa only [List.zipWith_nil_right, List.sum_nil] using decoded
              have decoded := variantEncoding_decodes chosen emptyCode.1 emptyCode.2
              simpa only [FieldType.encoding, variantTypes, Nat.zero_mul, Nat.add_zero] using
                literalCode_valid (by
                  change ∃ value, (variantEncoding (variants.map encode)).1.decodeCode tag = some value ∧
                    value.val.toNat = tag
                  simpa only [Nat.zero_mul, Nat.add_zero] using decoded)
            · simp only [ite_eq_right empty] at next
              obtain ⟨start, _, next⟩ := except_bind_ok next
              obtain ⟨⟨payload, afterPayload⟩, product, next⟩ := except_bind_ok next
              obtain ⟨endTokens, _, eq⟩ := except_bind_ok next
              cases eq
              have decoded := parseProduct_decodes (fun last field tokens value remainder accepted => by
                obtain ⟨⟨number, remaining⟩, child, next⟩ := except_bind_ok accepted
                obtain ⟨_, _, eq⟩ := except_bind_ok next
                cases eq
                exact ih field.2 payloadFlat tokens child) product
              have child := literalCode_valid decoded
              rw [← payloadEncoding] at child
              have decodedVariant := variantEncoding_decodes chosen child.1 child.2
              simpa only [FieldType.encoding, variantTypes] using
                literalCode_valid (by dsimp only at decodedVariant; exact decodedVariant)
          | _ => simp [selected] at next

private def collectInitial (read : α → Tokens → Except Error (List (List Nat × Nat) × Tokens))
    (state : List (List Nat × Nat) × Tokens) (field : α) :
    Except Error (List (List Nat × Nat) × Tokens) := do
  let (next, rest) ← read field state.2
  pure (state.1 ++ next, rest)

private theorem collectInitial_sound
    {read : α → Tokens → Except Error (List (List Nat × Nat) × Tokens)}
    {paths : α → List (List Nat)} {valid : List Nat × Nat → Prop}
    {fields : List α} {previous values : List (List Nat × Nat)} {input rest : Tokens}
    (each : ∀ field ∈ fields, ∀ tokens child remaining, read field tokens = .ok (child, remaining) →
      child.map Prod.fst = paths field ∧ ∀ entry ∈ child, valid entry)
    (earlier : ∀ entry ∈ previous, valid entry)
    (parsed : fields.foldlM (collectInitial read) (previous, input) = .ok (values, rest)) :
    values.map Prod.fst = previous.map Prod.fst ++ fields.flatMap paths ∧
      ∀ entry ∈ values, valid entry := by
  induction fields generalizing previous input with
  | nil =>
    cases parsed
    exact ⟨by simp, earlier⟩
  | cons field fields ih =>
    rw [List.foldlM_cons] at parsed
    cases step : read field input with
    | error error => simp [collectInitial, step, bind, Except.bind] at parsed
    | ok child =>
      obtain ⟨next, remainder⟩ := child
      have folded : fields.foldlM (collectInitial read) (previous ++ next, remainder) =
          .ok (values, rest) := by
        simpa [collectInitial, step, bind, Except.bind, pure, Except.pure] using parsed
      obtain ⟨nextPaths, nextValid⟩ := each field (by simp) input next remainder step
      obtain ⟨resultPaths, resultValid⟩ := ih
        (fun field member => each field (by simp [member]))
        (fun entry member => (List.mem_append.mp member).elim (earlier entry) (nextValid entry)) folded
      exact ⟨by simpa only [List.map_append, nextPaths, List.flatMap_cons, List.append_assoc] using
        resultPaths, resultValid⟩

private def parseInitial : Nat → FieldType → List Nat → Tokens →
    Except Error (List (List Nat × Nat) × Tokens)
  | 0, _, _, _ => .error (.syntax "packed initializer depth")
  | fuel + 1, .record name _ fields, path, input => do
    let rest ← expect [name, "{"] input
    let (values, rest) ← fields.zipIdx.foldlM (collectInitial fun ((name, ty), index) input => do
      let (next, rest) ← parseInitial fuel ty (path ++ [index]) (← expect [name, ":"] input)
      pure (next, ← expect [","] rest)) ([], rest)
    return (values, ← expect ["}"] rest)
  | fuel + 1, ty, path, input => do
    let (code, rest) ← parseCode (fuel + 1) ty false input
    return ([(path, code)], rest)

private def parseProjections : Nat → Tokens → Except Error (List String × Tokens)
  | fuel + 1, "." :: rest => do
    let (field, rest) ← readName false rest
    let (suffix, rest) ← parseProjections fuel rest
    return (field :: suffix, rest)
  | _, rest => .ok ([], rest)

private def parsePlace (input : Tokens) : Except Error (Place × Tokens) := do
  let (name, rest) ← readName false input
  let (fields, rest) ← parseProjections rest.length rest
  return (⟨name, fields⟩, rest)

private def parseResultPlace (input : Tokens) : Except Error (ResultPlace × Tokens) := do
  let (place, rest) ← parsePlace input
  match rest with
  | "as" :: input =>
    let (constructorName, rest) ← readName true input
    let number :: "]" :: rest ← expect ["["] rest | throw (.syntax "variant component index")
    let some index := number.toNat? | throw (.syntax "variant component index")
    let (fields, rest) ← parseProjections rest.length rest
    return (⟨place, some ⟨constructorName, index, fields⟩⟩, rest)
  | _ => return (⟨place, none⟩, rest)

private def takeLiteral (input : Tokens) : Except Error (Tokens × Tokens) := do
  let literal := input.takeWhile (· != ";")
  if literal.isEmpty then throw (.syntax "packed assignment literal")
  return (literal, ← expect [";"] (input.drop literal.length))

private def parseTasks : Nat → Tokens → Except Error (List Task × Tokens)
  | _, "}" :: rest => .ok ([], rest)
  | fuel + 1, "{" :: input => do
    let taskAndRest : Task × Tokens ← match input with
      | "let" :: "_" :: "=" :: input => do
        let (place, rest) ← parsePlace input
        pure ((place, none), ← expect [";"] rest)
      | _ => do
        let (place, rest) ← parsePlace input
        let (literal, rest) ← takeLiteral (← expect ["="] rest)
        pure ((place, some literal), rest)
    let (task, rest) := taskAndRest
    let (tasks, rest) ← parseTasks fuel (← expect ["}"] rest)
    return (task :: tasks, rest)
  | _, _ => .error (.syntax "one field access per packed fork task")

private def parseBody : Nat → Tokens → Except Error (Body × Tokens)
  | 0, _ => .error (.syntax "end of packed block")
  | fuel + 1, input => do
    match input with
    | "view" :: rest =>
      let (mode, rest) ← parseMode rest
      let (name, rest) ← readName false rest
      let (target, rest) ← parsePlace (← expect ["="] rest)
      let (inside, rest) ← parseBody fuel (← expect ["{"] rest)
      let (suffix, rest) ← parseBody fuel (← expect ["}", ";"] rest)
      return (.borrow name target mode inside suffix, rest)
    | "fork" :: rest =>
      let (tasks, rest) ← parseTasks fuel (← expect ["{"] rest)
      let (suffix, rest) ← parseBody fuel (← expect ["join", ";"] rest)
      return (.fork tasks suffix, rest)
    | _ =>
      match parsePlace input with
      | .ok (target, "=" :: rest) =>
        let (literal, rest) ← takeLiteral rest
        let (suffix, rest) ← parseBody fuel rest
        return (.assign target literal suffix, rest)
      | _ => return (.done, input)

def parse (input : Tokens) : Except Error Source := do
  let (definitions, body) ← parseDefinitions input.length [] input
  let (resultKind, body) ← parseKind (← expect ["fn", "main", "(", ")", "->"] body)
  let (root, body) ← readName false (← expect ["{", "let", "mut"] body)
  let body ← expect ["="] body
  let name :: _ := body | throw (.syntax "record initializer")
  let some (_, record) := definitions.find? (fun declaration => declaration.1 == name)
    | throw (.syntax "unknown record initializer")
  let (initial, body) ← parseInitial input.length record [] body
  let (code, body) ← parseBody input.length (← expect [";"] body)
  let (result, tail) ← parseResultPlace body
  let [] ← expect ["}"] tail | throw (.syntax "end of file")
  return ⟨record, root, initial, code, result, resultKind⟩

private def FieldType.schemaAt (addressable : List (List Nat)) (path : List Nat) :
    FieldType → PackedSchema
  | .integer kind => .value (packedInteger kind) (TargetIntegerABI.natural.slot kind)
  | .record _ flat fields =>
    let children := fields.attach.zipIdx.map fun (field, index) =>
      let childPath := path ++ [index]
      (if addressable.contains childPath then .addressable else .mayShareByte,
        schemaAt addressable childPath field.val.2)
    if flat then .flatRecord children else .record children
  | ty =>
    let codec := ty.encoding false
    .value codec (valueSlot codec)
termination_by ty => sizeOf ty
decreasing_by
  have smaller := List.sizeOf_lt_of_mem field.property
  have childSmaller : sizeOf field.val.2 < sizeOf field.val := by
    cases field.val
    simp
    omega
  simp_wf
  omega

def Source.schema (source : Source) (addressable : List (List Nat)) : PackedSchema :=
  source.record.schemaAt addressable []

private theorem zipIdx_attach_val (fields : List α) :
    fields.attach.zipIdx.map (Prod.map Subtype.val id) = fields.zipIdx := by
  rw [List.map_zipIdx, List.attach_map_subtype_val]

private theorem FieldType.record_schemaAt (name : String) (flat : Bool)
    (fields : List (String × FieldType)) (addressable : List (List Nat)) (path : List Nat) :
    let children := fields.zipIdx.map fun (field, index) =>
      let childPath := path ++ [index]
      (if addressable.contains childPath then StoragePolicy.addressable else .mayShareByte,
        field.2.schemaAt addressable childPath)
    (FieldType.record name flat fields).schemaAt addressable path =
      if flat then .flatRecord children else .record children := by
  rw [FieldType.schemaAt]
  dsimp only
  conv => rhs; rw [← zipIdx_attach_val fields, List.map_map]
  rfl

private theorem record_paths (fields : List (StoragePolicy × PackedSchema)) (flat : Bool) :
    (if flat then PackedSchema.flatRecord fields else .record fields).paths =
      fields.zipIdx.flatMap (fun (field, index) => field.2.paths.map (List.cons index)) := by
  cases flat <;> simp only [Bool.false_eq_true, ↓reduceIte, PackedSchema.paths] <;>
    (conv => rhs; rw [← zipIdx_attach_val fields, List.flatMap_map])
  all_goals rfl

private theorem zipIdx_map_indexed (fields : List α) (f : α × Nat → β) :
    (fields.zipIdx.map f).zipIdx = fields.zipIdx.map fun entry => (f entry, entry.2) := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_zipIdx, List.getElem?_map, Nat.zero_add]
  cases fields[index]? <;> rfl

private theorem FieldType.record_schema_paths (name : String) (flat : Bool)
    (fields : List (String × FieldType)) (addressable : List (List Nat)) (path : List Nat) :
    ((FieldType.record name flat fields).schemaAt addressable path).paths.map (path ++ ·) =
      fields.zipIdx.flatMap fun (field, index) =>
        let childPath := path ++ [index]
        (field.2.schemaAt addressable childPath).paths.map (childPath ++ ·) := by
  rw [FieldType.record_schemaAt, record_paths, zipIdx_map_indexed, List.flatMap_map, List.map_flatMap]
  congr 1
  funext entry
  simp only [List.map_map]
  congr 1
  funext suffix
  simp

private theorem FieldType.record_schema_typeAt (name : String) (flat : Bool)
    (fields : List (String × FieldType)) (addressable : List (List Nat)) (path : List Nat)
    {index : Nat} {entry : String × FieldType} (selected : fields[index]? = some entry) (suffix : List Nat) :
    ((FieldType.record name flat fields).schemaAt addressable path).typeAt (index :: suffix) =
      (entry.2.schemaAt addressable (path ++ [index])).typeAt suffix := by
  rw [FieldType.record_schemaAt]
  cases flat <;> simp [PackedSchema.typeAt, selected]

/-- The paths and typed codes produced by a successful initializer agree with its schema,
independently of the physical layout and the selected addressable fields. -/
theorem parseInitial_typed (fuel : Nat) (ty : FieldType) (path : List Nat)
    (addressable : List (List Nat)) (input : Tokens)
    {values : List (List Nat × Nat)} {rest : Tokens}
    (parsed : parseInitial fuel ty path input = .ok (values, rest)) :
    let schema := ty.schemaAt addressable path
    values.map Prod.fst = schema.paths.map (path ++ ·) ∧
      ∀ entry ∈ values, ∃ suffix encoding, entry.1 = path ++ suffix ∧
        schema.typeAt suffix = some encoding ∧ entry.2 < 2 ^ encoding.width ∧ encoding.Represents entry.2 := by
  induction fuel generalizing ty path input values rest with
  | zero => simp [parseInitial] at parsed
  | succ fuel ih =>
    cases ty with
    | record name flat fields =>
      simp only [parseInitial] at parsed
      obtain ⟨start, _, next⟩ := except_bind_ok parsed
      obtain ⟨⟨entries, remainder⟩, collected, next⟩ := except_bind_ok next
      obtain ⟨_, _, eq⟩ := except_bind_ok next
      cases eq
      dsimp only
      rw [FieldType.record_schema_paths]
      have valid := collectInitial_sound (paths := fun (field, index) =>
        let childPath := path ++ [index]
        (field.2.schemaAt addressable childPath).paths.map (childPath ++ ·))
        (valid := fun entry => ∃ suffix encoding, entry.1 = path ++ suffix ∧
          ((FieldType.record name flat fields).schemaAt addressable path).typeAt suffix = some encoding ∧
          entry.2 < 2 ^ encoding.width ∧ encoding.Represents entry.2)
        (fun ⟨⟨fieldName, fieldType⟩, index⟩ member input child remaining ran => by
          obtain ⟨childStart, _, next⟩ := except_bind_ok ran
          obtain ⟨⟨childValues, afterChild⟩, parsedChild, next⟩ := except_bind_ok next
          obtain ⟨_, _, eq⟩ := except_bind_ok next
          cases eq
          obtain ⟨paths, typed⟩ := ih fieldType (path ++ [index]) childStart parsedChild
          refine ⟨paths, ?_⟩
          intro entry present
          obtain ⟨suffix, encoding, located, found, fits, represents⟩ := typed entry present
          have selected := List.mk_mem_zipIdx_iff_getElem?.mp member
          exact ⟨index :: suffix, encoding, by simpa [List.append_assoc] using located,
            (FieldType.record_schema_typeAt name flat fields addressable path selected suffix).trans found,
            fits, represents⟩) (by simp) collected
      simpa only [List.map_nil, List.nil_append] using valid
    | _ =>
      simp only [parseInitial] at parsed
      obtain ⟨⟨code, remaining⟩, literal, eq⟩ := except_bind_ok parsed
      cases eq
      have valid := parseCode_valid (fuel + 1) _ false input literal
      simp only [FieldType.schemaAt, PackedSchema.paths, FieldType.encoding] at valid ⊢
      exact ⟨by simp, fun entry member => by
        cases List.mem_singleton.mp member
        exact ⟨[], _, by simp, rfl, valid.1, valid.2⟩⟩

/-- A parsed module initializes every schema leaf once in declaration order,
with a code accepted by that leaf's independent representation. -/
theorem parse_initializer_typed {input : Tokens} {source : Source} (parsed : parse input = .ok source)
    (addressable : List (List Nat)) :
    source.initial.map Prod.fst = (source.schema addressable).paths ∧
      ∀ entry ∈ source.initial, ∃ encoding, (source.schema addressable).typeAt entry.1 = some encoding ∧
        entry.2 < 2 ^ encoding.width ∧ encoding.Represents entry.2 := by
  unfold parse at parsed
  obtain ⟨⟨definitions, afterDefinitions⟩, _, next⟩ := except_bind_ok parsed
  obtain ⟨_, _, next⟩ := except_bind_ok next
  obtain ⟨⟨kind, afterKind⟩, _, next⟩ := except_bind_ok next
  obtain ⟨_, _, next⟩ := except_bind_ok next
  obtain ⟨⟨root, afterRoot⟩, _, next⟩ := except_bind_ok next
  obtain ⟨initializer, _, next⟩ := except_bind_ok next
  cases initializer with
  | nil => simp at next
  | cons name initializer =>
    cases found : definitions.find? (fun declaration => declaration.1 == name) with
    | none => simp [found] at next
    | some definition =>
      obtain ⟨label, record⟩ := definition
      simp only [found] at next
      obtain ⟨⟨values, afterValues⟩, initialized, next⟩ := except_bind_ok next
      obtain ⟨_, _, next⟩ := except_bind_ok next
      obtain ⟨⟨body, afterBody⟩, _, next⟩ := except_bind_ok next
      obtain ⟨⟨result, tail⟩, _, next⟩ := except_bind_ok next
      obtain ⟨ending, _, next⟩ := except_bind_ok next
      cases ending with
      | cons _ _ => simp at next
      | nil =>
        cases next
        obtain ⟨paths, typed⟩ := parseInitial_typed input.length record [] addressable _ initialized
        refine ⟨by simpa [Source.schema, List.nil_append] using paths, ?_⟩
        intro entry present
        obtain ⟨suffix, encoding, located, found, fits, represents⟩ := typed entry present
        exact ⟨encoding, by simpa [Source.schema, located] using found, fits, represents⟩

private structure Binding where
  name : String
  scope : Nat
  path : List Nat
  ty : FieldType

private def FieldType.project : List String → FieldType → Except Error (List Nat × FieldType)
  | [], ty => .ok ([], ty)
  | field :: rest, .record _ _ fields => do
    let some index := fields.findIdx? (fun entry => entry.1 == field)
      | throw (.syntax s!"unknown field {field}")
    let some (_, ty) := fields[index]? | throw (.syntax "field index")
    let (path, projected) ← project rest ty
    return (index :: path, projected)
  | _ :: _, _ => .error (.syntax "cannot project a packed scalar or tagged value as a record")

private theorem FieldType.project_schema {names : List String} {base ty : FieldType} {path : List Nat}
    (resolved : base.project names = .ok (path, ty)) (addressable : List (List Nat)) (basePath tail : List Nat) :
    (base.schemaAt addressable basePath).typeAt (path ++ tail) =
      (ty.schemaAt addressable (basePath ++ path)).typeAt tail := by
  induction names generalizing base ty path basePath with
  | nil => cases resolved; simp
  | cons name names ih =>
    cases base
    case record label flat fields =>
      simp only [project] at resolved
      cases selected : fields.findIdx? (fun field => field.1 == name) with
      | none => simp [selected] at resolved
      | some index =>
        simp only [selected] at resolved
        cases nth : fields[index]? with
        | none => simp [nth] at resolved
        | some entry =>
          obtain ⟨label', child⟩ := entry
          simp only [nth] at resolved
          obtain ⟨⟨suffix, projected⟩, below, eq⟩ := except_bind_ok resolved
          cases eq
          rw [List.cons_append, FieldType.record_schema_typeAt label flat fields addressable basePath nth]
          simpa [List.append_assoc] using ih below (basePath ++ [index])
    all_goals simp [project] at resolved

private def Source.place (source : Source) (scopes : List Binding)
    (place : Place) : Except Error (Nat × List Nat × FieldType) := do
  let binding ← match scopes.find? (fun binding => binding.name == place.root) with
    | some binding => pure binding
    | none =>
      if source.root = place.root then pure ⟨source.root, 0, [], source.record⟩
      else throw (.syntax s!"unknown record or view {place.root}")
  let (suffix, ty) ← binding.ty.project place.fields
  return (binding.scope, binding.path ++ suffix, ty)

private theorem Source.place_root_schema {source : Source} {place : Place} {scope : Nat}
    {path : List Nat} {ty : FieldType} (resolved : source.place [] place = .ok (scope, path, ty))
    (addressable : List (List Nat)) :
    scope = 0 ∧ (source.schema addressable).typeAt path = (ty.schemaAt addressable path).typeAt [] := by
  unfold Source.place at resolved
  by_cases named : source.root = place.root
  · simp only [List.find?_nil, ite_eq_left named, bind, Except.bind, pure, Except.pure] at resolved
    obtain ⟨⟨suffix, projected⟩, located, eq⟩ := except_bind_ok resolved
    cases eq
    exact ⟨rfl, by simpa [Source.schema] using FieldType.project_schema located addressable [] []⟩
  · simp [named, bind, Except.bind] at resolved

private def offsets (record : PackedRecord abi schema) (path : List Nat) : Except Error (List Nat) :=
  match record.field path with
  | some field => .ok field.2.byteOffsets
  | none => .error (.syntax "unresolved packed field")

private def componentSelection (flat : Bool) (fields : List (String × FieldType)) (index : Nat) :
    Except Error (FieldType × List PackedType.FieldStep) := do
  match found : fields[index]? with
  | none => throw (.syntax "variant component index out of range")
  | some (_, ty) =>
    let types := fields.map (fun field => field.2.encoding flat)
    have inRange : index < types.length := by
      simpa only [types, List.length_map] using (List.getElem?_eq_some_iff.mp found).1
    return (ty, productFieldSteps flat types ⟨index, inRange⟩)

private def FieldType.projectComponent : List String → FieldType → Bool →
    Except Error (FieldType × List PackedType.FieldStep)
  | [], ty, _ => .ok (ty, [])
  | name :: rest, .record _ flat fields, inherited => do
    let some index := fields.findIdx? (fun field => field.1 == name)
      | throw (.syntax s!"unknown payload field {name}")
    let forceFlat := flat || inherited
    let (child, outer) ← componentSelection forceFlat fields index
    let (ty, inner) ← child.projectComponent rest forceFlat
    return (ty, outer ++ inner)
  | _ :: _, _, _ => .error (.syntax "payload field projection requires a record")

private theorem componentSelection_correct (flat : Bool) (fields : List (String × FieldType)) (index : Nat)
    {ty : FieldType} {steps : List PackedType.FieldStep}
    (selected : componentSelection flat fields index = .ok (ty, steps)) :
    let types := fields.map (fun field => field.2.encoding flat)
    ∃ offset, (productEncoding flat types).1.fieldAt steps = some (offset, ty.encoding flat) := by
  unfold componentSelection at selected
  split at selected
  · cases selected
  · rename_i name child found
    cases selected
    let types := fields.map (fun field => field.2.encoding flat)
    have declared : types[index]? = some (ty.encoding flat) := by simp [types, found]
    obtain ⟨offset, _, correct⟩ := productFieldSteps_correct flat types index declared
    exact ⟨offset, correct⟩

private theorem FieldType.projectComponent_correct {names : List String} {base ty : FieldType}
    {flat : Bool} {steps : List PackedType.FieldStep}
    (selected : base.projectComponent names flat = .ok (ty, steps)) :
    ∃ offset inherited, (base.encoding flat).fieldAt steps = some (offset, ty.encoding inherited) := by
  induction names generalizing base ty flat steps with
  | nil =>
    cases selected
    exact ⟨0, flat, rfl⟩
  | cons name names ih =>
    cases base
    case record label force fields =>
      simp only [projectComponent] at selected
      cases found : fields.findIdx? (fun field => field.1 == name) with
      | none => simp [found] at selected
      | some index =>
        simp only [found] at selected
        obtain ⟨⟨child, outer⟩, component, rest⟩ := except_bind_ok selected
        obtain ⟨⟨projected, inner⟩, descended, same⟩ := except_bind_ok rest
        cases same
        obtain ⟨start, outerField⟩ := componentSelection_correct _ _ _ component
        obtain ⟨offset, inherited, innerField⟩ := ih descended
        rw [FieldType.record_encoding, PackedType.fieldAt_append outerField, innerField]
        exact ⟨start + offset, inherited, rfl⟩
    all_goals simp [projectComponent] at selected

private theorem variantEncoding_payloadTypeAt {variants : List PackedType} {payload : PackedType} {tag : Nat}
    (selected : variants[tag]? = some payload) (retained : payload.unionSlot.2 = payload) :
    (variantEncoding variants).1.payloadTypeAt tag = some payload := by
  by_cases addresses : variants.any carriesAddresses
  · simp [variantEncoding, addresses, PackedType.payloadTypeAt, List.getElem?_map, selected,
      PackedType.unionSlot]
  · simp [variantEncoding, addresses, PackedType.payloadTypeAt, selected, retained]

private theorem FieldType.record_unionSlot (name : String) (flat : Bool) (fields : List (String × FieldType)) :
    ((FieldType.record name flat fields).encoding false).unionSlot.2 =
      (FieldType.record name flat fields).encoding false := by
  rw [FieldType.record_encoding, Bool.or_false]
  by_cases aligned : alignedProduct flat (fields.map fun field => field.2.encoding flat)
  · simp only [productEncoding, ite_eq_left aligned, AlignedProductState.finish, PackedType.unionSlot]
  · cases fields <;> simp_all [productEncoding, PackedType.unionSlot]

private def FieldType.selectPayload (base : FieldType) (projection : PayloadProjection) :
    Except Error (FieldType × Nat × List PackedType.FieldStep) := do
  let .tagged _ variants := base | throw (.syntax "constructor projection requires a tagged field")
  let some tag := variants.findIdx? (fun variant => variant.1 == projection.constructorName)
    | throw (.syntax s!"unknown variant {projection.constructorName}")
  let some (_, .record _ flat components) := variants[tag]? | throw (.syntax "invalid variant payload")
  let (child, outer) ← componentSelection flat components projection.index
  let (ty, inner) ← child.projectComponent projection.fields flat
  return (ty, tag, outer ++ inner)

private theorem FieldType.selectPayload_correct {base ty : FieldType} {projection : PayloadProjection}
    {tag : Nat} {steps : List PackedType.FieldStep} (resolved : base.selectPayload projection = .ok (ty, tag, steps)) :
    ∃ payload offset inherited, (base.encoding false).payloadTypeAt tag = some payload ∧
      payload.fieldAt steps = some (offset, ty.encoding inherited) := by
  cases base
  case tagged sumName variants =>
    simp only [selectPayload] at resolved
    cases found : variants.findIdx? (fun alternative => alternative.1 == projection.constructorName) with
    | none => simp [found] at resolved
    | some ordinal =>
      simp only [found] at resolved
      cases lookup : variants[ordinal]? with
      | none => simp [lookup] at resolved
      | some entry =>
        obtain ⟨label, constructorType⟩ := entry
        cases constructorType
        case record name flat components =>
          simp only [lookup] at resolved
          obtain ⟨⟨child, outer⟩, component, next⟩ := except_bind_ok resolved
          obtain ⟨⟨field, inner⟩, below, eq⟩ := except_bind_ok next
          cases eq
          let payload := (FieldType.record name flat components).encoding false
          let encode := fun entry : String × FieldType => entry.2.encoding false
          have picked : (variants.map encode)[tag]? = some payload := by simp [encode, lookup, payload]
          have encoded : (FieldType.tagged sumName variants).encoding false =
              (variantEncoding (variants.map encode)).1 := by
            rw [FieldType.encoding, List.attach_map_val (f := encode)]
          obtain ⟨start, outerField⟩ := componentSelection_correct _ _ _ component
          obtain ⟨offset, inherited, innerField⟩ := FieldType.projectComponent_correct below
          have located : payload.fieldAt outer = some (start, child.encoding flat) := by
            simpa only [payload, FieldType.record_encoding, Bool.or_false] using outerField
          refine ⟨payload, start + offset, inherited, ?_, ?_⟩
          · rw [encoded]
            exact variantEncoding_payloadTypeAt picked (FieldType.record_unionSlot name flat components)
          · rw [PackedType.fieldAt_append located, innerField]
            rfl
        all_goals simp [lookup] at resolved
  all_goals cases resolved

structure ReturnRead where
  scope : Nat
  path : List Nat
  payload : Option (Nat × List PackedType.FieldStep)

private def checkedReturn (kind : IntegerType) (ty : FieldType) (read : ReturnRead) : Except Error ReturnRead :=
  match ty with
  | .integer actual =>
    if actual = kind then .ok read else .error (.syntax "packed result type mismatch")
  | _ => .error (.syntax "packed return requires an integer field")

private theorem checkedReturn_sound {kind : IntegerType} {ty : FieldType} {read result : ReturnRead}
    (checked : checkedReturn kind ty read = .ok result) : ty = .integer kind ∧ read = result := by
  cases ty
  case integer actual =>
    by_cases equal : actual = kind <;> simp_all [checkedReturn]
  all_goals cases checked

private def Source.resolveResult (source : Source) : Except Error ReturnRead := do
  let (scope, path, base) ← source.place [] source.result.place
  let (ty, payload) ← match source.result.payload with
    | none => pure (base, none)
    | some projection => do
      let (ty, tag, steps) ← base.selectPayload projection
      pure (ty, some (tag, steps))
  checkedReturn source.resultKind ty ⟨scope, path, payload⟩

theorem Source.resolveResult_typed {source : Source} {result : ReturnRead}
    (resolved : source.resolveResult = .ok result) (addressable : List (List Nat)) :
    result.scope = 0 ∧ match result.payload with
    | none => (source.schema addressable).typeAt result.path = some (packedInteger source.resultKind)
    | some (tag, steps) => ∃ ty payload offset,
        (source.schema addressable).typeAt result.path = some ty ∧ ty.payloadTypeAt tag = some payload ∧
          payload.fieldAt steps = some (offset, packedInteger source.resultKind) := by
  unfold Source.resolveResult at resolved
  obtain ⟨⟨scope, path, base⟩, located, next⟩ := except_bind_ok resolved
  obtain ⟨scopeZero, schemaLeaf⟩ := Source.place_root_schema located addressable
  cases projection : source.result.payload with
  | none =>
    simp only [projection, bind, pure, Except.bind, Except.pure] at next
    obtain ⟨rfl, rfl⟩ := checkedReturn_sound next
    exact ⟨scopeZero, by simpa [FieldType.schemaAt, PackedSchema.typeAt] using schemaLeaf⟩
  | some request =>
    simp only [projection] at next
    obtain ⟨⟨resultType, tag, steps⟩, picked, next⟩ := except_bind_ok next
    obtain ⟨rfl, rfl⟩ := checkedReturn_sound next
    obtain ⟨payload, offset, _, active, selected⟩ := FieldType.selectPayload_correct picked
    cases base
    case tagged name variants =>
      refine ⟨scopeZero, _, payload, offset, ?_, active, ?_⟩
      · simpa [FieldType.schemaAt, PackedSchema.typeAt] using schemaLeaf
      · simpa only [FieldType.encoding] using selected
    all_goals cases picked

private def ReturnRead.program (result : ReturnRead) (id : Nat) (bytes : List Nat) : List PackedMIR.Op :=
  match result.payload with
  | none => [.load result.scope result.path bytes]
  | some (tag, steps) => [.capturePayload result.scope id result.path bytes,
      .loadPayloadField result.scope id tag steps bytes, .forgetPayload id]

private def ReturnRead.eval (result : ReturnRead) (schema : PackedSchema)
    (state : List Nat → Option Nat) : Option Nat := do
  let code ← state result.path
  match result.payload with
  | none => some code
  | some (tag, steps) =>
    let ty ← schema.typeAt result.path
    ty.projectTaggedCode tag code steps

private def assignment (source : Source) (scopes : List Binding) (target : Place)
    (literal : Tokens) : Except Error (Nat × List (List Nat × Nat)) := do
  let (scope, path, ty) ← source.place scopes target
  let (values, []) ← parseInitial (literal.length + 1) ty path literal
    | throw (.syntax "unexpected tokens after packed assignment literal")
  return (scope, values)

private def Binding.eraseScope (binding : Binding) : Binding := { binding with scope := 0 }

/-- Logical lookup retains lexical names and declaration paths when runtime
scope identities are erased. -/
private theorem Source.place_eraseScope (source : Source) (scopes : List Binding) (place : Place) :
    source.place (scopes.map Binding.eraseScope) place =
      (source.place scopes place).map (fun (_, path, ty) => (0, path, ty)) := by
  unfold Source.place
  rw [List.find?_map]
  simp only [Function.comp_def, Binding.eraseScope]
  cases found : scopes.find? (fun binding => binding.name == place.root) with
  | none =>
    by_cases root : source.root = place.root
    · simp [root, bind, Except.bind, Except.map, pure, Except.pure]
      cases source.record.project place.fields <;> rfl
    · simp [root, bind, Except.bind, Except.map]; rfl
  | some binding =>
    simp only [Option.map_some, bind, Except.bind, pure, Except.pure]
    simp only [Binding.eraseScope]
    cases binding.ty.project place.fields <;> rfl

theorem assignment_eraseScope (source : Source) (scopes : List Binding) (target : Place)
    (literal : Tokens) : assignment source (scopes.map Binding.eraseScope) target literal =
      (assignment source scopes target literal).map (fun (_, values) => (0, values)) := by
  unfold assignment
  rw [Source.place_eraseScope]
  cases placed : source.place scopes target with
  | error err => rfl
  | ok result =>
    obtain ⟨scope, path, ty⟩ := result
    cases parsed : parseInitial (literal.length + 1) ty path literal with
    | error err => simp [Except.map, bind, Except.bind, parsed]
    | ok result =>
      obtain ⟨values, rest⟩ := result
      cases rest <;> simp [Except.map, bind, Except.bind, parsed, pure, Except.pure] <;> rfl

def lowerStores (record : PackedRecord abi schema) (scope : Nat)
    (values : List (List Nat × Nat)) : Except Error (List PackedMIR.Op) :=
  values.mapM fun (leaf, value) => do
    let bytes ← offsets record leaf
    pure (PackedMIR.Op.store scope leaf bytes value)

/-- Source assignments keep declaration paths and literal codes while
attaching the physical footprint of each resolved leaf. -/
inductive StoresLower (record : PackedRecord abi schema) (scope : Nat) :
    List (List Nat × Nat) → List PackedMIR.Op → Prop where
  | nil : StoresLower record scope [] []
  | cons (span : PackedMIR.FootprintClaim record path bytes)
      (rest : StoresLower record scope values operations) :
      StoresLower record scope ((path, code) :: values) (.store scope path bytes code :: operations)

theorem lowerStores_sound {record : PackedRecord abi schema} {scope : Nat}
    {values : List (List Nat × Nat)} {operations : List PackedMIR.Op}
    (lowered : lowerStores record scope values = .ok operations) : StoresLower record scope values operations := by
  induction values generalizing operations with
  | nil => cases lowered; exact .nil
  | cons value values ih =>
    obtain ⟨path, code⟩ := value
    cases found : record.field path with
    | none => simp [lowerStores, List.mapM_cons, offsets, found, bind, Except.bind] at lowered
    | some field =>
      cases tail : lowerStores record scope values with
      | error err =>
        have computed : lowerStores record scope ((path, code) :: values) = .error err := by
          simp only [lowerStores, List.mapM_cons, offsets, found, bind, Except.bind,
            pure, Except.pure] at tail ⊢
          rw [tail]
        rw [computed] at lowered
        cases lowered
      | ok rest =>
        have computed : lowerStores record scope ((path, code) :: values) =
            .ok (.store scope path field.2.byteOffsets code :: rest) := by
          simp only [lowerStores, List.mapM_cons, offsets, found, bind, Except.bind,
            pure, Except.pure] at tail ⊢
          rw [tail]
        rw [computed] at lowered
        cases lowered
        exact .cons ⟨field, found, rfl⟩ (ih tail)

private def addressRequirements (source : Source) (scopes : List Binding) :
    Body → Except Error (List (List Nat))
  | .done => .ok []
  | .assign _ _ suffix => addressRequirements source scopes suffix
  | .borrow name target _ inside suffix => do
    let (_, path, ty) ← source.place scopes target
    let inner ← addressRequirements source (⟨name, 0, path, ty⟩ :: scopes) inside
    return inner ++ (← addressRequirements source scopes suffix)
  | .fork tasks suffix => do
    let rest ← addressRequirements source scopes suffix
    if tasks.length < 2 || !tasks.any (fun task => task.2.isSome) then
      return rest
    let paths ← tasks.mapM fun (place, _) => do
      let (_, path, _) ← source.place scopes place
      pure path
    return paths ++ rest

private def lowerTask (source : Source) (record : PackedRecord .natural schema)
    (scopes : List Binding) : Task → Except Error (Nat × PackedMIR.Task) :=
  fun (place, literal) => do
    let (scope, path, ty) ← source.place scopes place
    let bytes ← offsets record path
    let code ← literal.mapM fun tokens => do
      let (code, []) ← parseCode (tokens.length + 1) ty false tokens
        | throw (.syntax "unexpected tokens after packed task literal")
      pure code
    pure (scope, (⟨path, bytes, code⟩ : PackedMIR.Task))

inductive TaskLowers (source : Source) (record : PackedRecord .natural schema) (scopes : List Binding) :
    Task → (Nat × PackedMIR.Task) → Prop where
  | access (resolved : source.place scopes place = .ok (scope, path, ty))
      (span : PackedMIR.FootprintClaim record path bytes)
      (decoded : (literal : Option Tokens).mapM (fun tokens => do
        let (code, []) ← parseCode (tokens.length + 1) ty false tokens
          | throw (Error.syntax "unexpected tokens after packed task literal")
        pure code) = (Except.ok code : Except Error (Option Nat))) :
      TaskLowers source record scopes (place, literal) (scope, ⟨path, bytes, code⟩)

private theorem lowerTask_sound {source : Source} {record : PackedRecord .natural schema} {scopes : List Binding}
    {task : Task} {entry : Nat × PackedMIR.Task} (lowered : lowerTask source record scopes task = .ok entry) :
    TaskLowers source record scopes task entry := by
  obtain ⟨place, literal⟩ := task
  obtain ⟨⟨scope, path, ty⟩, resolved, remaining⟩ := except_bind_ok lowered
  obtain ⟨bytes, located, remaining⟩ := except_bind_ok remaining
  obtain ⟨code, decoded, same⟩ := except_bind_ok remaining
  cases same
  have span : PackedMIR.FootprintClaim record path bytes := by
    cases found : record.field path with
    | none => simp [offsets, found] at located
    | some field =>
      have exactBytes : field.2.byteOffsets = bytes := by simpa [offsets, found] using located
      exact ⟨field, found, exactBytes.symm⟩
  exact .access resolved span decoded

inductive TasksLower (source : Source) (record : PackedRecord .natural schema) (scopes : List Binding) :
    List Task → List (Nat × PackedMIR.Task) → Prop where
  | nil : TasksLower source record scopes [] []
  | cons : TaskLowers source record scopes task entry → TasksLower source record scopes tasks entries →
      TasksLower source record scopes (task :: tasks) (entry :: entries)

private theorem lowerTasks_sound {source : Source} {record : PackedRecord .natural schema} {scopes : List Binding}
    {tasks : List Task} {entries : List (Nat × PackedMIR.Task)}
    (lowered : tasks.mapM (lowerTask source record scopes) = .ok entries) :
    TasksLower source record scopes tasks entries := by
  induction tasks generalizing entries with
  | nil => cases lowered; exact .nil
  | cons task tasks ih =>
    rw [List.mapM_cons] at lowered
    obtain ⟨entry, first, remaining⟩ := except_bind_ok lowered
    obtain ⟨rest, following, same⟩ := except_bind_ok remaining
    cases same
    exact .cons (lowerTask_sound first) (ih following)

private def lowerBody (source : Source) (record : PackedRecord .natural schema)
    (scopes : List Binding) (fresh : Nat) : Body → Except Error (List PackedMIR.Op × Nat)
  | .done => .ok ([], fresh)
  | .assign target literal rest => do
    let (scope, values) ← assignment source scopes target literal
    let stores ← lowerStores record scope values
    let (suffix, next) ← lowerBody source record scopes fresh rest
    return (stores ++ suffix, next)
  | .borrow name target mode inside rest => do
    let (parent, path, ty) ← source.place scopes target
    let (body, next) ← lowerBody source record (⟨name, fresh, path, ty⟩ :: scopes) (fresh + 1) inside
    let (suffix, next) ← lowerBody source record scopes next rest
    return ([.reborrow fresh parent path mode] ++ body ++ [.closeScope fresh] ++ suffix, next)
  | .fork tasks rest => do
    let entries ← tasks.mapM (lowerTask source record scopes)
    let scope := (entries.head?.map Prod.fst).getD 0
    if entries.any (fun entry => entry.1 != scope) then
      throw (.syntax "packed fork accesses must have a common lexical scope")
    let (suffix, next) ← lowerBody source record scopes fresh rest
    return (.fork scope (entries.map Prod.snd) :: suffix, next)

inductive BodyLowers (source : Source) (record : PackedRecord .natural schema) :
    List Binding → Nat → Body → List PackedMIR.Op → Nat → Prop where
  | done : BodyLowers source record scopes fresh .done [] fresh
  | assign (resolved : assignment source scopes target literal = .ok (scope, values))
      (stores : StoresLower record scope values operations)
      (suffix : BodyLowers source record scopes fresh rest remaining next) :
      BodyLowers source record scopes fresh (.assign target literal rest) (operations ++ remaining) next
  | borrow (resolved : source.place scopes target = .ok (parent, path, ty))
      (body : BodyLowers source record (⟨name, fresh, path, ty⟩ :: scopes) (fresh + 1) inside operations middle)
      (suffix : BodyLowers source record scopes middle rest remaining next) :
      BodyLowers source record scopes fresh (.borrow name target mode inside rest)
        ([.reborrow fresh parent path mode] ++ operations ++ [.closeScope fresh] ++ remaining) next
  | fork (resolved : TasksLower source record scopes tasks entries)
      (common : ∀ entry ∈ entries, entry.1 = (entries.head?.map Prod.fst).getD 0)
      (suffix : BodyLowers source record scopes fresh rest remaining next) :
      BodyLowers source record scopes fresh (.fork tasks rest)
        (.fork ((entries.head?.map Prod.fst).getD 0) (entries.map Prod.snd) :: remaining) next

theorem lowerBody_sound {source : Source} {record : PackedRecord .natural schema} {scopes : List Binding}
    {fresh next : Nat} {body : Body} {operations : List PackedMIR.Op}
    (lowered : lowerBody source record scopes fresh body = .ok (operations, next)) :
    BodyLowers source record scopes fresh body operations next := by
  induction body generalizing scopes fresh next operations with
  | done => cases lowered; exact .done
  | assign target literal rest ih =>
    obtain ⟨⟨scope, values⟩, resolved, remaining⟩ := except_bind_ok lowered
    obtain ⟨stores, emitted, remaining⟩ := except_bind_ok remaining
    obtain ⟨⟨suffix, final⟩, continued, equal⟩ := except_bind_ok remaining
    cases equal
    exact .assign resolved (lowerStores_sound emitted) (ih continued)
  | borrow name target mode inside rest ihInside ihRest =>
    obtain ⟨⟨parent, path, ty⟩, resolved, remaining⟩ := except_bind_ok lowered
    obtain ⟨⟨body, middle⟩, emitted, remaining⟩ := except_bind_ok remaining
    obtain ⟨⟨suffix, final⟩, continued, equal⟩ := except_bind_ok remaining
    cases equal
    exact .borrow resolved (ihInside emitted) (ihRest continued)
  | fork tasks rest ih =>
    obtain ⟨entries, resolved, remaining⟩ := except_bind_ok lowered
    cases common : entries.any (fun entry => entry.1 != (entries.head?.map Prod.fst).getD 0) with
    | true => simp [common, bind, Except.bind] at remaining
    | false =>
      simp only [common, Bool.false_eq_true, ite_false] at remaining
      obtain ⟨⟨suffix, final⟩, continued, equal⟩ := except_bind_ok remaining
      cases equal
      have shared : ∀ entry ∈ entries, entry.1 = (entries.head?.map Prod.fst).getD 0 := by
        simpa using common
      exact .fork (lowerTasks_sound resolved) shared (ih continued)

def lower (source : Source) : Except Error PackedMIR.Module := do
  let addressable ← addressRequirements source [] source.body
  let schema := source.schema addressable
  let some record := PackedRecord.plan .natural schema 0
    | throw (.syntax "invalid packed layout")
  let layout := PackedMIR.describe record
  let (body, next) ← lowerBody source record [] 1 source.body
  let result ← source.resolveResult
  let resultBytes ← offsets record result.path
  return { version := PackedMIR.version
           schema
           layout
           initial := source.initial
           operations := ([.openScope 0 [] .exclusive] ++ body) ++
             (result.program next resultBytes ++ [.closeScope 0]) }

/-- Source values are indexed by declaration path. Logical evaluation never
queries a physical offset or a byte footprint. -/
private abbrev LogicalState := List Nat → Option Nat

private def bindValues (state : LogicalState) (values : List (List Nat × Nat)) : LogicalState :=
  values.foldl (fun state (path, value) query =>
    if query = path then some value else state query) state

private theorem bindValues_outside (values : List (List Nat × Nat)) (state : LogicalState) (key : List Nat)
    (outside : key ∉ values.map Prod.fst) : bindValues state values key = state key := by
  induction values generalizing state with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨path, code⟩ := entry
    have separate : key ≠ path ∧ key ∉ rest.map Prod.fst := by simpa using outside
    exact (ih _ separate.2).trans (ite_eq_right separate.1)

private theorem bindValues_lookup (values : List (List Nat × Nat)) (state : LogicalState) (key : List Nat)
    (unique : (values.map Prod.fst).Nodup) :
    bindValues state values key = ((values.find? (fun entry => entry.1 == key)).map Prod.snd).or (state key) := by
  induction values generalizing state with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨path, code⟩ := entry
    obtain ⟨absent, remaining⟩ := List.nodup_cons.mp unique
    by_cases same : key = path
    · subst key
      change bindValues (fun query => if query = path then some code else state query) rest path = _
      rw [bindValues_outside rest _ path absent]
      simp
    · change bindValues (fun query => if query = path then some code else state query) rest key = _
      rw [ih _ remaining]
      simp [same, Ne.symm same]

theorem initializer_values {source : Source} {mir : PackedMIR.Module} (checked : PackedMIR.Accepted mir)
    (initial : mir.initial = source.initial) :
    ∀ key, bindValues (fun _ => none) source.initial key = mir.initialValue key := by
  have unique : (mir.initial.map Prod.fst).Nodup := checked.initialPaths ▸ mir.schema.paths_nodup
  intro key
  rw [← initial, bindValues_lookup _ _ _ unique]
  unfold PackedMIR.Module.initialValue
  cases mir.initial.find? (fun entry => entry.1 == key) <;> rfl

/-- The assignment relation preserves every logical query, including paths
absent from the assignment and repeated writes to the same path. -/
theorem StoresLower.effects {record : PackedRecord abi schema} {scope : Nat}
    {values : List (List Nat × Nat)} {operations : List PackedMIR.Op}
    (lowered : StoresLower record scope values operations) (state : List Nat → Option Nat) (key : List Nat) :
    operations.foldl (PackedMIR.Op.updateCode key) (state key) = bindValues state values key := by
  induction lowered generalizing state with
  | nil => rfl
  | @cons path bytes values operations code span rest ih =>
    change operations.foldl (PackedMIR.Op.updateCode key) (if key = path then some code else state key) = _
    exact ih (fun query => if query = path then some code else state query)

theorem lowerStores_preserves_values {record : PackedRecord abi schema} {scope : Nat}
    {values : List (List Nat × Nat)} {operations : List PackedMIR.Op}
    (lowered : lowerStores record scope values = .ok operations) (state : List Nat → Option Nat) :
    ∀ key, operations.foldl (PackedMIR.Op.updateCode key) (state key) =
      values.foldl (fun memory (path, code) query => if query = path then some code else memory query) state key :=
  (lowerStores_sound lowered).effects state

theorem lowerStores_refines {record : PackedRecord abi schema} {scope : Nat}
    {values : List (List Nat × Nat)} {operations : List PackedMIR.Op}
    {state final : PackedMIR.Execution record} {before : Image record.layout.size}
    (lowered : lowerStores record scope values = .ok operations)
    (ran : PackedMIR.Runs state operations final)
    (represented : before.InAllocation record.owner state.memory.heap) :
    ∃ after : Image record.layout.size, after.InAllocation record.owner final.memory.heap ∧
      ∀ key, record.readImage after key =
        values.foldl (fun memory (path, code) query => if query = path then some code else memory query)
          (record.readImage before) key := by
  obtain ⟨after, allocated, agrees⟩ := ran.refines_codes represented
  exact ⟨after, allocated, fun key => (agrees key).trans
    (lowerStores_preserves_values lowered (record.readImage before) key)⟩

/-- A fork task writes one resolved value. Logical task evaluation uses only
its declaration path and decoded literal, without consulting layout offsets. -/
private def taskAssignments (source : Source) (scopes : List Binding) : Task → Except Error (List (List Nat × Nat))
  | (_, none) => .ok []
  | (place, some tokens) => do
    let (_, path, ty) ← source.place scopes place
    let (code, []) ← parseCode (tokens.length + 1) ty false tokens
      | throw (.syntax "unexpected tokens after packed task literal")
    return [(path, code)]

private def forkAssignments (source : Source) (scopes : List Binding) (tasks : List Task) :
    Except Error (List (List Nat × Nat)) :=
  (tasks.mapM (taskAssignments source scopes)).map List.flatten

private theorem taskAssignments_eraseScope (source : Source) (scopes : List Binding) (task : Task) :
    taskAssignments source (scopes.map Binding.eraseScope) task = taskAssignments source scopes task := by
  obtain ⟨place, literal⟩ := task
  cases literal with
  | none => rfl
  | some tokens =>
    simp only [taskAssignments, Source.place_eraseScope]
    cases source.place scopes place with
    | error err => rfl
    | ok result => cases result; rfl

private theorem forkAssignments_eraseScope (source : Source) (scopes : List Binding) (tasks : List Task) :
    forkAssignments source (scopes.map Binding.eraseScope) tasks = forkAssignments source scopes tasks := by
  unfold forkAssignments
  have same : taskAssignments source (scopes.map Binding.eraseScope) = taskAssignments source scopes :=
    funext (taskAssignments_eraseScope source scopes)
  rw [same]

private def taskValues (task : PackedMIR.Task) : List (List Nat × Nat) :=
  task.code.toList.map (fun code => (task.path, code))

private theorem TaskLowers.assignments {source : Source} {record : PackedRecord .natural schema}
    {scopes : List Binding} {task : Task} {entry : Nat × PackedMIR.Task}
    (lowered : TaskLowers source record scopes task entry) :
    taskAssignments source scopes task = .ok (taskValues entry.2) := by
  cases lowered with
  | @access place scope path ty bytes literal code resolved _ decoded =>
    cases literal with
    | none => cases decoded; rfl
    | some tokens =>
      simp only [Option.mapM_some, bind, pure, Except.bind, Except.pure] at decoded
      obtain ⟨actual, parsed, same⟩ := except_bind_ok decoded
      cases same
      unfold taskAssignments
      dsimp only
      rw [resolved]
      cases input : parseCode (tokens.length + 1) ty false tokens with
      | error err => simp [input] at parsed
      | ok result =>
        obtain ⟨value, remaining⟩ := result
        cases remaining with
        | nil => simp only [input] at parsed; cases parsed; simp [input, bind, Except.bind, taskValues, pure, Except.pure]
        | cons _ _ => simp only [input] at parsed; cases parsed

private theorem TasksLower.assignments {source : Source} {record : PackedRecord .natural schema}
    {scopes : List Binding} {tasks : List Task} {entries : List (Nat × PackedMIR.Task)}
    (lowered : TasksLower source record scopes tasks entries) :
    forkAssignments source scopes tasks = .ok (entries.flatMap (fun entry => taskValues entry.2)) := by
  have mapped : tasks.mapM (taskAssignments source scopes) = .ok (entries.map (fun entry => taskValues entry.2)) := by
    induction lowered with
    | nil => rfl
    | cons first rest ih => simp [List.mapM_cons, first.assignments, ih, bind, pure, Except.bind, Except.pure]
  simp [forkAssignments, mapped, List.flatMap, Except.map]

private theorem taskValues_effect (tasks : List PackedMIR.Task) (state : LogicalState) (key : List Nat) :
    (PackedMIR.Op.fork scope tasks).updateCode key (state key) =
      bindValues state (tasks.flatMap taskValues) key := by
  induction tasks generalizing state with
  | nil => rfl
  | cons task tasks ih =>
    cases task with
    | mk path bytes code =>
      cases code with
      | none => exact ih state
      | some code =>
        change tasks.foldl _ (if key = path then some code else state key) = _
        simpa [bindValues, taskValues, List.foldl_append, PackedMIR.Op.updateCode] using
          ih (fun query => if query = path then some code else state query)

private inductive LogicalRuns (source : Source) :
    List Binding → Body → LogicalState → LogicalState → Prop where
  | done : LogicalRuns source scopes .done memory memory
  | assign (stored : assignment source scopes target literal = .ok (scope, writes))
      (continued : LogicalRuns source scopes rest (bindValues before writes) after) :
      LogicalRuns source scopes (.assign target literal rest) before after
  | borrow (found : source.place scopes target = .ok (scope, path, ty))
      (insideRun : LogicalRuns source (⟨name, 0, path, ty⟩ :: scopes) inside before middle)
      (continued : LogicalRuns source scopes rest middle after) :
      LogicalRuns source scopes (.borrow name target mode inside rest) before after
  | fork (stored : forkAssignments source scopes tasks = .ok writes)
      (continued : LogicalRuns source scopes rest (bindValues before writes) after) :
      LogicalRuns source scopes (.fork tasks rest) before after

private def evaluate (source : Source) (scopes : List Binding) (memory : LogicalState) :
    Body → Except Error LogicalState
  | .done => .ok memory
  | .assign target literal rest => do
    let (_, writes) ← assignment source scopes target literal
    evaluate source scopes (bindValues memory writes) rest
  | .borrow name target _ inside rest => do
    let (_, path, ty) ← source.place scopes target
    let middle ← evaluate source (⟨name, 0, path, ty⟩ :: scopes) memory inside
    evaluate source scopes middle rest
  | .fork tasks rest => do
    let writes ← forkAssignments source scopes tasks
    evaluate source scopes (bindValues memory writes) rest

theorem evaluate_eraseScope (source : Source) (scopes : List Binding) (memory : List Nat → Option Nat)
    (body : Body) : evaluate source (scopes.map Binding.eraseScope) memory body = evaluate source scopes memory body := by
  induction body generalizing scopes memory with
  | done => rfl
  | assign target literal rest ih =>
    simp only [evaluate, assignment_eraseScope]
    cases assignment source scopes target literal with
    | error err => rfl
    | ok result =>
      obtain ⟨scope, values⟩ := result
      exact ih scopes (bindValues memory values)
  | borrow name target mode inside rest ihInside ihRest =>
    simp only [evaluate, Source.place_eraseScope]
    cases source.place scopes target with
    | error err => rfl
    | ok result =>
      obtain ⟨scope, path, ty⟩ := result
      have inner := ihInside (⟨name, 0, path, ty⟩ :: scopes) memory
      simp only [List.map_cons, Binding.eraseScope] at inner
      simp only [Except.map, bind, Except.bind]
      rw [inner]
      cases evaluate source (⟨name, 0, path, ty⟩ :: scopes) memory inside with
      | error err => rfl
      | ok middle => exact ihRest scopes middle
  | fork tasks rest ih =>
    simp only [evaluate, forkAssignments_eraseScope]
    cases forkAssignments source scopes tasks with
    | error err => rfl
    | ok values => exact ih scopes (bindValues memory values)

theorem BodyLowers.effects {source : Source} {record : PackedRecord .natural schema} {scopes : List Binding}
    {fresh next : Nat} {body : Body} {operations : List PackedMIR.Op}
    (lowered : BodyLowers source record scopes fresh body operations next) (before : List Nat → Option Nat) :
    ∃ after, evaluate source scopes before body = .ok after ∧
      ∀ key, operations.foldl (PackedMIR.Op.updateCode key) (before key) = after key := by
  induction lowered generalizing before with
  | done => exact ⟨before, rfl, fun _ => rfl⟩
  | @assign scopes target literal scope values operations fresh rest remaining next resolved stores suffix ih =>
    obtain ⟨after, evaluated, agrees⟩ := ih (bindValues before values)
    refine ⟨after, by simp [evaluate, resolved, evaluated, bind, Except.bind], ?_⟩
    intro key
    rw [List.foldl_append, stores.effects before key]
    exact agrees key
  | @borrow scopes target parent path ty name fresh inside operations middle rest remaining next mode
      resolved loweredInside loweredRest ihInside ihRest =>
    obtain ⟨between, evaluatedInside, insideAgrees⟩ := ihInside before
    obtain ⟨after, evaluatedRest, restAgrees⟩ := ihRest between
    have erasedInside : evaluate source (⟨name, 0, path, ty⟩ :: scopes) before inside = .ok between := by
      have erased := evaluate_eraseScope source (⟨name, fresh, path, ty⟩ :: scopes) before inside
      rw [evaluatedInside] at erased
      have restored := evaluate_eraseScope source (⟨name, 0, path, ty⟩ :: scopes) before inside
      simpa only [List.map_cons, Binding.eraseScope] using restored.symm.trans erased
    refine ⟨after, by simp [evaluate, resolved, erasedInside, evaluatedRest, bind, Except.bind], ?_⟩
    intro key
    simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil, PackedMIR.Op.updateCode,
      insideAgrees key] using restAgrees key
  | @fork scopes tasks entries fresh rest remaining next resolved common loweredRest ih =>
    let values := entries.flatMap (fun entry => taskValues entry.2)
    obtain ⟨after, evaluated, agrees⟩ := ih (bindValues before values)
    refine ⟨after, by simp [evaluate, resolved.assignments, evaluated, values, bind, Except.bind], ?_⟩
    intro key
    rw [List.foldl_cons, taskValues_effect]
    simpa [values, List.flatMap_map] using agrees key

theorem lowerBody_refines {source : Source} {record : PackedRecord .natural schema} {scopes : List Binding}
    {fresh next : Nat} {body : Body} {operations : List PackedMIR.Op}
    {state final : PackedMIR.Execution record} {before : Image record.layout.size}
    (lowered : lowerBody source record scopes fresh body = .ok (operations, next))
    (ran : PackedMIR.Runs state operations final)
    (represented : before.InAllocation record.owner state.memory.heap) :
    ∃ logicalAfter, evaluate source scopes (record.readImage before) body = .ok logicalAfter ∧
      ∃ after : Image record.layout.size, after.InAllocation record.owner final.memory.heap ∧
        ∀ key, record.readImage after key = logicalAfter key := by
  obtain ⟨logicalAfter, evaluated, effects⟩ := (lowerBody_sound lowered).effects (record.readImage before)
  obtain ⟨after, stored, values⟩ := ran.refines_codes represented
  exact ⟨logicalAfter, evaluated, after, stored, fun key => (values key).trans (effects key)⟩

private theorem lower_inv {source : Source} {mir : PackedMIR.Module}
    (lowered : lower source = .ok mir) :
    ∃ (addressable : List (List Nat)) (record : PackedRecord .natural (source.schema addressable))
      (body : List PackedMIR.Op) (next : Nat) (result : ReturnRead) (bytes : List Nat),
      lowerBody source record [] 1 source.body = .ok (body, next) ∧
      source.resolveResult = .ok result ∧
      mir.version = PackedMIR.version ∧ mir.schema = source.schema addressable ∧
      mir.initial = source.initial ∧
      mir.operations = ([.openScope 0 [] .exclusive] ++ body) ++ (result.program next bytes ++ [.closeScope 0]) ∧
      PackedRecord.plan .natural (source.schema addressable) 0 = some record ∧ mir.layout.Describes record := by
  obtain ⟨addressable, requirements, rest⟩ := except_bind_ok lowered
  cases planned : PackedRecord.plan .natural (source.schema addressable) 0 with
  | none => simp [planned] at rest
  | some record =>
    simp only [planned] at rest
    obtain ⟨⟨body, next⟩, emitted, rest⟩ := except_bind_ok rest
    obtain ⟨result, resolved, rest⟩ := except_bind_ok rest
    obtain ⟨bytes, _, eq⟩ := except_bind_ok rest
    cases eq
    exact ⟨addressable, record, body, next, result, bytes, emitted, resolved, rfl, rfl, rfl, rfl,
      planned, PackedMIR.describe_sound record⟩

theorem lower_effects {source : Source} {mir : PackedMIR.Module}
    (lowered : lower source = .ok mir) (before : List Nat → Option Nat) :
    mir.version = PackedMIR.version ∧ mir.initial = source.initial ∧
      ∃ after, evaluate source [] before source.body = .ok after ∧
        ∀ key, mir.operations.foldl (PackedMIR.Op.updateCode key) (before key) = after key := by
  obtain ⟨_, _, _, next, result, bytes, emitted, _, version, _, initial, operations, _⟩ := lower_inv lowered
  obtain ⟨after, evaluated, agrees⟩ := (lowerBody_sound emitted).effects before
  exact ⟨version, initial, after, evaluated, fun key => by
    cases payload : result.payload with
    | none =>
      simpa only [operations, ReturnRead.program, payload, List.foldl_append, List.foldl_cons,
        List.foldl_nil, PackedMIR.Op.updateCode] using agrees key
    | some selected =>
      cases selected
      simpa only [operations, ReturnRead.program, payload, List.foldl_append, List.foldl_cons,
        List.foldl_nil, PackedMIR.Op.updateCode] using agrees key⟩

theorem lower_result {source : Source} {mir : PackedMIR.Module}
    (lowered : lower source = .ok mir) :
    ∃ body next result bytes, source.resolveResult = .ok result ∧
      mir.operations = ([.openScope 0 [] .exclusive] ++ body) ++ (result.program next bytes ++ [.closeScope 0]) := by
  obtain ⟨_, _, body, next, result, bytes, _, resolved, _, _, _, operations, _⟩ := lower_inv lowered
  exact ⟨body, next, result, bytes, resolved, operations⟩

theorem lower_layout_describes {source : Source} {mir : PackedMIR.Module} (lowered : lower source = .ok mir) :
    ∃ record : PackedRecord .natural mir.schema,
      PackedRecord.plan .natural mir.schema 0 = some record ∧ mir.layout.Describes record := by
  obtain ⟨_, record, _, _, _, _, _, _, _, schema, _, _, planned, described⟩ := lower_inv lowered
  rw [schema]
  exact ⟨record, planned, described⟩

/-- Source lowering preserves the initial values and their packed types before MIR admission. -/
theorem lower_initializer_typed {input : Tokens} {source : Source} {mir : PackedMIR.Module}
    (parsed : parse input = .ok source) (lowered : lower source = .ok mir) :
    mir.initial.map Prod.fst = mir.schema.paths ∧
      ∀ entry ∈ mir.initial, ∃ encoding, mir.schema.typeAt entry.1 = some encoding ∧
        entry.2 < 2 ^ encoding.width ∧ encoding.Represents entry.2 := by
  obtain ⟨addressable, _, _, _, _, _, _, _, _, schema, initial, _⟩ := lower_inv lowered
  rw [schema, initial]
  exact parse_initializer_typed parsed addressable

theorem lower_initial_allocates {input : Tokens} {source : Source} {mir : PackedMIR.Module}
    (parsed : parse input = .ok source) (lowered : lower source = .ok mir)
    (record : PackedRecord .natural mir.schema) :
    ∃ memory, record.allocate {} mir.initialValue = some memory := by
  obtain ⟨paths, typed⟩ := lower_initializer_typed parsed lowered
  exact mir.initial_allocates record paths typed

theorem lower_refines {source : Source} {mir : PackedMIR.Module} (checked : PackedMIR.Accepted mir)
    {before : Image checked.record.layout.size} (lowered : lower source = .ok mir)
    (represented : before.InAllocation checked.record.owner checked.initial.heap) :
    ∃ logicalAfter, evaluate source [] (checked.record.readImage before) source.body = .ok logicalAfter ∧
      ∃ after : Image checked.record.layout.size, after.InAllocation checked.record.owner checked.final.memory.heap ∧
        ∀ key, checked.record.readImage after key = logicalAfter key := by
  obtain ⟨_, _, logicalAfter, evaluated, effects⟩ := lower_effects lowered (checked.record.readImage before)
  obtain ⟨after, stored, values⟩ := checked.runs.refines_codes represented
  exact ⟨logicalAfter, evaluated, after, stored, fun key => (values key).trans (effects key)⟩

private theorem evaluate_sound (source : Source) {scopes : List Binding} {before after : LogicalState}
    {body : Body} (ran : evaluate source scopes before body = .ok after) :
    LogicalRuns source scopes body before after := by
  induction body generalizing scopes before after with
  | done => cases ran; exact .done
  | assign target literal rest ih =>
    cases found : assignment source scopes target literal with
    | error err => simp [evaluate, found, bind, Except.bind] at ran
    | ok result =>
      obtain ⟨scope, writes⟩ := result
      exact .assign found (ih (by simpa [evaluate, found, bind, Except.bind] using ran))
  | borrow name target mode inside rest ihInside ihRest =>
    cases found : source.place scopes target with
    | error err => simp [evaluate, found, bind, Except.bind] at ran
    | ok place =>
      obtain ⟨scope, path, ty⟩ := place
      cases insideRun : evaluate source (⟨name, 0, path, ty⟩ :: scopes) before inside with
      | error err => simp [evaluate, found, insideRun, bind, Except.bind] at ran
      | ok middle =>
        exact .borrow found (ihInside insideRun)
          (ihRest (by simpa [evaluate, found, insideRun, bind, Except.bind] using ran))
  | fork tasks rest ih =>
    cases found : forkAssignments source scopes tasks with
    | error err => simp [evaluate, found, bind, Except.bind] at ran
    | ok writes =>
      exact .fork found (ih (by simpa [evaluate, found, bind, Except.bind] using ran))

private def Source.initialState (source : Source) : LogicalState :=
  bindValues (fun _ => none) source.initial

theorem lower_initialized_refines {source : Source} {mir : PackedMIR.Module} (checked : PackedMIR.Accepted mir)
    (lowered : lower source = .ok mir) :
    ∃ logicalAfter, evaluate source [] source.initialState source.body = .ok logicalAfter ∧
      ∃ after : Image checked.record.layout.size, after.InAllocation checked.record.owner checked.final.memory.heap ∧
        ∀ key ty, mir.schema.typeAt key = some ty → checked.record.readImage after key = logicalAfter key := by
  obtain ⟨_, initial, logicalAfter, evaluated, effects⟩ := lower_effects lowered source.initialState
  obtain ⟨before, allocated, initialized⟩ := PackedRecord.allocate_on_image checked.starts
  obtain ⟨after, stored, values⟩ := checked.runs.refines_codes allocated
  refine ⟨logicalAfter, evaluated, after, stored, ?_⟩
  intro key ty declared
  obtain ⟨code, supplied, actual⟩ := initialized key ty declared
  have logicalInitial : source.initialState key = some code :=
    (initializer_values checked initial key).trans supplied
  rw [values key, actual, ← logicalInitial]
  exact effects key

theorem lower_return_refines {source : Source} {mir : PackedMIR.Module} (checked : PackedMIR.Accepted mir)
    (lowered : lower source = .ok mir) :
    ∃ logicalAfter result code,
      evaluate source [] source.initialState source.body = .ok logicalAfter ∧
      source.resolveResult = .ok result ∧
      result.eval mir.schema logicalAfter = some code ∧ checked.final.observations.head? = some code ∧
      ∃ after : Image checked.record.layout.size, after.InAllocation checked.record.owner checked.final.memory.heap ∧
        ∀ key ty, mir.schema.typeAt key = some ty → checked.record.readImage after key = logicalAfter key := by
  obtain ⟨logicalAfter, evaluated, after, represented, values⟩ := lower_initialized_refines checked lowered
  obtain ⟨body, next, result, bytes, resolved, tail⟩ := lower_result lowered
  have ran := checked.runs
  rw [tail] at ran
  cases payload : result.payload with
  | none =>
    simp only [ReturnRead.program, payload, List.singleton_append] at ran
    obtain ⟨code, observed, read⟩ := ran.final_load represented
    obtain ⟨ty, declared⟩ := PackedRecord.readImage_declared read
    have logical := (values result.path ty declared).symm.trans read
    exact ⟨logicalAfter, result, code, evaluated, resolved,
      by simp [ReturnRead.eval, logical, payload], observed, after, represented, values⟩
  | some selected =>
    obtain ⟨tag, steps⟩ := selected
    simp only [ReturnRead.program, payload, List.cons_append, List.nil_append] at ran
    obtain ⟨code, ty, whole, observed, declared, read, projected⟩ :=
      ran.final_payload_field (earlier := .openScope 0 [] .exclusive :: body) represented
    have logical := (values result.path ty declared).symm.trans read
    exact ⟨logicalAfter, result, code, evaluated, resolved,
      by simp [ReturnRead.eval, logical, payload, declared, projected], observed, after, represented, values⟩

theorem lower_return_typed {source : Source} {mir : PackedMIR.Module} (checked : PackedMIR.Accepted mir)
    (lowered : lower source = .ok mir) :
    ∃ code, checked.final.observations.head? = some code ∧
      (packedInteger source.resultKind).Represents code := by
  obtain ⟨logicalAfter, result, code, _, resolved, value, observed, image, _, agrees⟩ :=
    lower_return_refines checked lowered
  obtain ⟨addressable, _, _, _, _, _, _, _, _, schema, _, _⟩ := lower_inv lowered
  have typed := (Source.resolveResult_typed resolved addressable).2
  rw [← schema] at typed
  refine ⟨code, observed, ?_⟩
  cases projected : result.payload with
  | none =>
    rw [projected] at typed
    have logical : logicalAfter result.path = some code := by
      simpa [ReturnRead.eval, projected, bind] using value
    exact (PackedRecord.readImage_typed typed ((agrees result.path _ typed).trans logical)).2
  | some pair =>
    obtain ⟨tag, steps⟩ := pair
    rw [projected] at typed
    obtain ⟨ty, selected, offset, declared, active, component⟩ := typed
    obtain ⟨whole, logical, loaded⟩ := Option.bind_eq_some_iff.mp value
    have projectedCode : ty.projectTaggedCode tag whole steps = some code := by
      simpa [projected, declared, bind] using loaded
    have wholeValid := (PackedRecord.readImage_typed declared ((agrees result.path _ declared).trans logical)).2
    obtain ⟨⟨actualTag, data⟩, split, exactCode⟩ := Option.bind_eq_some_iff.mp projectedCode
    by_cases same : actualTag = tag
    · subst actualTag
      obtain ⟨actual, actualType, dataValid⟩ := PackedType.splitTag_typed wholeValid split
      rw [active] at actualType
      cases actualType
      have codeEq : packedCodeSlice data offset (packedInteger source.resultKind).width = code := by
        simpa [PackedType.payloadFieldCode, active, component, bind, pure] using exactCode
      rw [← codeEq]
      exact (PackedType.fieldAt_sound component dataValid).2
    · simp [same] at exactCode

structure Verified (input : String) where
  source : Source
  mir : PackedMIR.Module
  parsed : parse (tokensWithDecimals input) = .ok source
  lowered : lower source = .ok mir
  checked : PackedMIR.Accepted mir
  code : Nat
  logical : ∃ after result,
    LogicalRuns source [] source.body source.initialState after ∧
    source.resolveResult = .ok result ∧ result.eval mir.schema after = some code ∧
    ∃ image : Image checked.record.layout.size,
      image.InAllocation checked.record.owner checked.final.memory.heap ∧
      ∀ key ty, mir.schema.typeAt key = some ty → checked.record.readImage image key = after key
  agreement : checked.final.observations.head? = some code

/-- Logical source correctness is supplied by refinement proofs. The result
code is read from the admitted MIR execution. -/
def Verified.ofLowered {input : String} {source : Source} {mir : PackedMIR.Module}
    (parsed : parse (tokensWithDecimals input) = .ok source) (lowered : lower source = .ok mir)
    (checked : PackedMIR.Accepted mir) : Verified input where
  source := source
  mir := mir
  parsed := parsed
  lowered := lowered
  checked := checked
  code := checked.final.observations.head?.getD 0
  logical := by
    obtain ⟨after, result, code, evaluated, resolved, value, observed, image⟩ := lower_return_refines checked lowered
    refine ⟨after, result, evaluate_sound source evaluated, resolved, ?_, image⟩
    simpa only [observed, Option.getD_some] using value
  agreement := by
    obtain ⟨_, _, code, _, _, _, observed, _⟩ := lower_return_refines checked lowered
    simp only [observed, Option.getD_some]

def verify (input : String) : Except Error (Verified input) :=
  match parsed : parse (tokensWithDecimals input) with
  | .error err => .error err
  | .ok source =>
    match lowered : lower source with
    | .error err => .error err
    | .ok mir =>
      match PackedMIR.validate mir with
      | .error err => .error (.syntax err)
      | .ok checked => .ok (Verified.ofLowered parsed lowered checked)

theorem verify_of_admitted {input : String} {source : Source} {mir : PackedMIR.Module}
    {checked : PackedMIR.Accepted mir} (parsed : parse (tokensWithDecimals input) = .ok source)
    (lowered : lower source = .ok mir) (admitted : PackedMIR.validate mir = .ok checked) :
    verify input = .ok (Verified.ofLowered parsed lowered checked) := by
  unfold verify
  split
  next err failed => rw [parsed] at failed; cases failed
  next actual found =>
    rw [parsed] at found
    cases found
    split
    next err failed => rw [lowered] at failed; cases failed
    next module emitted =>
      rw [lowered] at emitted
      cases emitted
      rw [admitted]

/-- The source entry point accepts precisely the successfully elaborated
modules with an admissible reference trace. -/
theorem verify_correct (input : String) :
    (∃ verified, verify input = .ok verified) ↔
      ∃ source mir, parse (tokensWithDecimals input) = .ok source ∧
        lower source = .ok mir ∧ mir.Admissible := by
  constructor
  · intro accepted
    obtain ⟨verified, _⟩ := accepted
    exact ⟨verified.source, verified.mir, verified.parsed, verified.lowered, verified.checked.admissible⟩
  · intro admissible
    obtain ⟨_, _, parsed, lowered, valid⟩ := admissible
    obtain ⟨checked, admitted⟩ := PackedMIR.validate_complete valid
    exact ⟨Verified.ofLowered parsed lowered checked, verify_of_admitted parsed lowered admitted⟩

def Verified.result {input : String} (proof : Verified input) : Option Int :=
  proof.checked.final.observations.head?.map fun code =>
    match proof.source.resultKind with
    | .signed width => (BitVec.ofNat width.bits code).toInt
    | .unsigned _ => code

structure Matched (input certificate : String) where
  accepted : Verified input
  matchesSource : (Lean.Json.parse certificate).map Lean.Json.compress =
    .ok (Lean.toJson accepted.mir).compress

def verifyMIR (input certificate : String) : Except Error (Matched input certificate) := do
  let accepted ← verify input
  match parsed : Lean.Json.parse certificate with
  | .error err => throw (.syntax err)
  | .ok body =>
    if same : body.compress = (Lean.toJson accepted.mir).compress then
      return ⟨accepted, by
        rw [parsed]
        change Except.ok body.compress = _
        rw [same]⟩
    else throw (.syntax "packed MIR differs from the source operations")

theorem verifyMIR_correct (input certificate : String) :
    (∃ matched, verifyMIR input certificate = .ok matched) ↔
      ∃ source mir, parse (tokensWithDecimals input) = .ok source ∧ lower source = .ok mir ∧
        mir.Admissible ∧ (Lean.Json.parse certificate).map Lean.Json.compress =
          .ok (Lean.toJson mir).compress := by
  constructor
  · rintro ⟨matched, _⟩
    exact ⟨matched.accepted.source, matched.accepted.mir, matched.accepted.parsed, matched.accepted.lowered,
      matched.accepted.checked.admissible, matched.matchesSource⟩
  · rintro ⟨source, mir, parsed, lowered, valid, certified⟩
    obtain ⟨checked, admitted⟩ := PackedMIR.validate_complete valid
    unfold verifyMIR
    rw [verify_of_admitted parsed lowered admitted]
    simp only [bind, Except.bind]
    split
    · rename_i err failed
      simp [failed, Except.map] at certified
    · rename_i body found
      have equal : body.compress = (Lean.toJson mir).compress := by
        simpa [found, Except.map] using certified
      have emitted : body.compress = (Lean.toJson (Verified.ofLowered parsed lowered checked).mir).compress :=
        equal
      rw [dite_eq_left emitted]
      exact ⟨_, rfl⟩

end Aethel.SourcePacked
