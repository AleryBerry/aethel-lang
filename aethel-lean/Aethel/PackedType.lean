import Aethel.PackedValue

namespace Aethel.AutomaticLayout

/-- Serializable fixed-width value descriptions. Products place their first
component in the low bits. Sum tags follow variant declaration order. -/
inductive PackedType where
  | raw (width : Nat)
  | range (width : IntegerWidth) (signed : Bool) (lower upper : Int)
  | product (left right : PackedType)
  | tagged (variants : List PackedType)
  | padding (before after : Nat) (payload : PackedType)
  | addressable (alignment : Nat) (payload : PackedType)
  deriving Repr

def PackedType.width : PackedType → Nat
  | .raw bits => bits
  | .range bits _ _ _ => bits.bits
  | .product left right => left.width + right.width
  | .tagged variants =>
    ADTLayout.minTagBits variants.length +
      ((variants.attach.map fun entry => width entry.val).max?).getD 0
  | .padding before after payload => before + payload.width + after
  | .addressable _ payload => payload.width
termination_by ty => sizeOf ty
decreasing_by
  · decreasing_tactic
  · decreasing_tactic
  · have smaller := List.sizeOf_lt_of_mem entry.property
    simp_wf
    omega
  · decreasing_tactic
  · decreasing_tactic

private def PackedType.numericValue (width : Nat) (signed : Bool) (code : Nat) : Int :=
  if signed then (BitVec.ofNat width code).toInt else code

/-- The independent description of valid codes. A sum payload is checked
against the type of the selected variant, including its unused high bits. -/
def PackedType.Represents : PackedType → Nat → Prop
  | .raw width, code => code < 2 ^ width
  | .range width signed lower upper, code =>
    code < 2 ^ width.bits ∧ lower ≤ numericValue width.bits signed code ∧
      numericValue width.bits signed code ≤ upper
  | .product left right, code =>
    left.Represents (code % 2 ^ left.width) ∧ right.Represents (code / 2 ^ left.width)
  | .tagged variants, code =>
    let tagBound := 2 ^ ADTLayout.minTagBits variants.length
    match variants.attach[code % tagBound]? with
    | none => False
    | some variant => Represents variant.val (code / tagBound)
  | .padding before _ payload, code =>
    code % 2 ^ before = 0 ∧ code < 2 ^ (before + payload.width) ∧
      payload.Represents (code / 2 ^ before)
  | .addressable _ payload, code => payload.Represents code
termination_by ty _ => sizeOf ty
decreasing_by
  · decreasing_tactic
  · decreasing_tactic
  · have smaller := List.sizeOf_lt_of_mem variant.property
    simp_wf
    omega
  · decreasing_tactic
  · decreasing_tactic

theorem PackedType.product_represents {left right : PackedType} {first second : Nat}
    (firstFits : first < 2 ^ left.width) (firstValid : left.Represents first)
    (secondValid : right.Represents second) :
    (PackedType.product left right).Represents (first + second * 2 ^ left.width) := by
  obtain ⟨low, high⟩ := concatCode_split (high := second) firstFits
  rw [Represents, low, high]
  exact ⟨firstValid, secondValid⟩

theorem PackedType.product_code_fits {left right : PackedType} {first second : Nat}
    (firstFits : first < 2 ^ left.width) (secondFits : second < 2 ^ right.width) :
    first + second * 2 ^ left.width < 2 ^ (PackedType.product left right).width := by
  rw [width]
  exact concatCode_fits firstFits secondFits

private theorem PackedType.selected_tag_fits {variants : List PackedType} {tag : Nat}
    {payload : PackedType} (selected : variants[tag]? = some payload) :
    tag < 2 ^ ADTLayout.minTagBits variants.length := by
  obtain ⟨inRange, _⟩ := List.getElem?_eq_some_iff.mp selected
  exact Nat.lt_of_lt_of_le inRange (ADTLayout.minTagBits_le_iff.mp (Nat.le_refl _))

theorem PackedType.tagged_represents {variants : List PackedType} {tag code : Nat}
    {payload : PackedType} (selected : variants[tag]? = some payload)
    (valid : payload.Represents code) :
    (PackedType.tagged variants).Represents
      (tag + code * 2 ^ ADTLayout.minTagBits variants.length) := by
  obtain ⟨inRange, eqPayload⟩ := List.getElem?_eq_some_iff.mp selected
  have attachedInRange : tag < variants.attach.length := by simpa using inRange
  have eqAttached : variants.attach[tag].val = payload :=
    (congrArg Subtype.val (List.getElem_attach attachedInRange)).trans eqPayload
  obtain ⟨low, high⟩ := concatCode_split (high := code) (selected_tag_fits selected)
  rw [Represents, low, high, List.getElem?_eq_getElem attachedInRange]
  simpa only [eqAttached] using valid

theorem PackedType.tagged_code_fits {variants : List PackedType} {tag code : Nat}
    {payload : PackedType} (selected : variants[tag]? = some payload)
    (fits : code < 2 ^ payload.width) :
    tag + code * 2 ^ ADTLayout.minTagBits variants.length < 2 ^ (PackedType.tagged variants).width := by
  have member := List.mem_of_getElem? selected
  have widthMember : payload.width ∈ variants.attach.map (fun entry => entry.val.width) :=
    List.mem_map.mpr ⟨⟨payload, member⟩, by simp, rfl⟩
  have payloadWidth := List.le_max?_getD_of_mem (k := 0) widthMember
  have combined := concatCode_fits (selected_tag_fits selected) fits
  rw [width]
  exact Nat.lt_of_lt_of_le combined
    (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left payloadWidth _))

theorem PackedType.padding_represents {payload : PackedType} {code before after : Nat}
    (fits : code < 2 ^ payload.width) (valid : payload.Represents code) :
    (PackedType.padding before after payload).Represents (code * 2 ^ before) := by
  have positive : 0 < 2 ^ before := Nat.two_pow_pos _
  have bound := Nat.mul_lt_mul_of_pos_right fits positive
  rw [Represents, Nat.pow_add, Nat.mul_comm (2 ^ before)]
  exact ⟨by simp, bound, by simpa [Nat.mul_div_cancel _ positive] using valid⟩

theorem PackedType.padding_code_fits {payload : PackedType} {code before after : Nat}
    (fits : code < 2 ^ payload.width) :
    code * 2 ^ before < 2 ^ (PackedType.padding before after payload).width := by
  have bound := Nat.mul_lt_mul_of_pos_right fits (Nat.two_pow_pos before)
  have wider : 2 ^ (before + payload.width) ≤ 2 ^ (PackedType.padding before after payload).width :=
    Nat.pow_le_pow_right (by decide) (by simp [width])
  rw [Nat.pow_add, Nat.mul_comm (2 ^ before)] at wider
  exact Nat.lt_of_lt_of_le bound wider

private theorem eraseAttachedVariant {variants : List PackedType} {tag : Nat}
    {variant : { ty // ty ∈ variants }} (selected : variants.attach[tag]? = some variant) :
    variants[tag]? = some variant.val := by
  have erased := congrArg (Option.map Subtype.val) selected
  simpa only [← List.getElem?_map, List.attach_map_subtype_val, Option.map_some] using erased

theorem PackedType.codeFits : (ty : PackedType) → (code : Nat) → ty.Represents code → code < 2 ^ ty.width
  | .raw size, _, valid => by simpa only [Represents, width] using valid
  | .range size signed lower upper, _, valid => by
    rw [Represents] at valid
    simpa only [width] using valid.1
  | .product left right, code, valid => by
    rw [Represents] at valid
    have together := product_code_fits (left := left) (right := right)
      (Nat.mod_lt code (Nat.two_pow_pos _)) (codeFits right _ valid.2)
    simpa only [Nat.mod_add_div'] using together
  | .tagged variants, code, valid => by
    rw [Represents] at valid
    split at valid
    · contradiction
    · rename_i variant selected
      have smaller := List.sizeOf_lt_of_mem variant.property
      have together := tagged_code_fits (eraseAttachedVariant selected) (codeFits variant.val _ valid)
      simpa only [Nat.mod_add_div'] using together
  | .padding before after payload, _, valid => by
    rw [Represents] at valid
    exact Nat.lt_of_lt_of_le valid.2.1 (Nat.pow_le_pow_right (by decide) (by simp [width]))
  | .addressable alignment payload, _, valid => by
    rw [Represents] at valid
    simpa only [width] using codeFits payload _ valid
termination_by ty _ _ => sizeOf ty
decreasing_by all_goals simp_wf; omega

def PackedType.check : PackedType → Nat → Bool
  | .raw width, code => decide (code < 2 ^ width)
  | .range width signed lower upper, code =>
    decide (code < 2 ^ width.bits ∧ lower ≤ numericValue width.bits signed code ∧
      numericValue width.bits signed code ≤ upper)
  | .product left right, code =>
    left.check (code % 2 ^ left.width) && right.check (code / 2 ^ left.width)
  | .tagged variants, code =>
    let tagBound := 2 ^ ADTLayout.minTagBits variants.length
    match variants.attach[code % tagBound]? with
    | none => false
    | some variant => check variant.val (code / tagBound)
  | .padding before _ payload, code =>
    decide (code % 2 ^ before = 0 ∧ code < 2 ^ (before + payload.width)) &&
      payload.check (code / 2 ^ before)
  | .addressable _ payload, code => payload.check code
termination_by ty _ => sizeOf ty
decreasing_by
  · decreasing_tactic
  · decreasing_tactic
  · have smaller := List.sizeOf_lt_of_mem variant.property
    simp_wf
    omega
  · decreasing_tactic
  · decreasing_tactic

theorem PackedType.check_correct (ty : PackedType) (code : Nat) :
    ty.check code = true ↔ ty.Represents code := by
  cases ty with
  | raw _ | range _ _ _ _ => simp [check, Represents]
  | product left right =>
    rw [check, Represents, Bool.and_eq_true, left.check_correct, right.check_correct]
  | tagged variants =>
    rw [check, Represents]
    split
    · simp
    · rename_i variant _
      have smaller := List.sizeOf_lt_of_mem variant.property
      rw [check_correct]
  | padding before after payload =>
    simp only [check, Represents, Bool.and_eq_true, decide_eq_true_eq, payload.check_correct, and_assoc]
  | addressable alignment payload =>
    rw [check, Represents, payload.check_correct]
termination_by sizeOf ty
decreasing_by all_goals simp_wf; omega

instance PackedType.decRepresents (ty : PackedType) (code : Nat) : Decidable (ty.Represents code) :=
  decidable_of_iff (ty.check code = true) (ty.check_correct code)

abbrev PackedType.Value (ty : PackedType) := { bits : BitVec ty.width // ty.Represents bits.toNat }

def PackedType.codec (ty : PackedType) : PackedCodec ty.Value ty.width :=
  (PackedCodec.raw ty.width).refine (fun bits => ty.Represents bits.toNat)

/-- Required addresses are relative to the start of the entire value.
Every possible variant contributes its payload's requirements. -/
inductive PackedType.RequiresAddress : PackedType → Nat → Nat → Prop where
  | here : RequiresAddress (.addressable alignment payload) 0 alignment
  | addressable (inside : RequiresAddress payload offset alignment) :
      RequiresAddress (.addressable outer payload) offset alignment
  | padding (inside : RequiresAddress payload offset alignment) :
      RequiresAddress (.padding before after payload) (before + offset) alignment
  | left (inside : RequiresAddress left offset alignment) :
      RequiresAddress (.product left right) offset alignment
  | right (inside : RequiresAddress right offset alignment) :
      RequiresAddress (.product left right) (left.width + offset) alignment
  | variant (member : payload ∈ variants) (inside : RequiresAddress payload offset alignment) :
      RequiresAddress (.tagged variants) (ADTLayout.minTagBits variants.length + offset) alignment

def PackedType.requiredAddresses : PackedType → List (Nat × Nat)
  | .raw _ | .range .. => []
  | .addressable alignment payload => (0, alignment) :: payload.requiredAddresses
  | .padding before _ payload =>
    payload.requiredAddresses.map fun (offset, alignment) => (before + offset, alignment)
  | .product left right =>
    left.requiredAddresses ++ right.requiredAddresses.map fun (offset, alignment) =>
      (left.width + offset, alignment)
  | .tagged variants =>
    variants.attach.flatMap fun variant =>
      (requiredAddresses variant.val).map fun (offset, alignment) =>
        (ADTLayout.minTagBits variants.length + offset, alignment)
termination_by ty => sizeOf ty
decreasing_by
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · decreasing_tactic
  · have smaller := List.sizeOf_lt_of_mem variant.property
    simp_wf
    omega

theorem PackedType.RequiresAddress.mem_requiredAddresses {ty : PackedType} {offset alignment : Nat}
    (required : ty.RequiresAddress offset alignment) : (offset, alignment) ∈ ty.requiredAddresses := by
  induction required with
  | here => simp [requiredAddresses]
  | addressable _ ih => rw [requiredAddresses]; exact List.mem_cons_of_mem _ ih
  | padding _ ih => rw [requiredAddresses, List.mem_map]; exact ⟨_, ih, rfl⟩
  | left _ ih => rw [requiredAddresses]; exact List.mem_append_left _ ih
  | right _ ih =>
    rw [requiredAddresses]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩)
  | variant member _ ih =>
    rw [requiredAddresses, List.mem_flatMap]
    exact ⟨⟨_, member⟩, List.mem_attach _ _, List.mem_map_of_mem ih⟩

theorem PackedType.RequiresAddress.within {ty : PackedType} {offset alignment : Nat}
    (required : ty.RequiresAddress offset alignment) : offset ≤ ty.width := by
  induction required with
  | here => exact Nat.zero_le _
  | addressable _ ih => simpa only [width] using ih
  | padding _ ih | left _ ih | right _ ih => rw [width]; omega
  | variant member _ ih =>
    rw [width]
    apply Nat.add_le_add_left (Nat.le_trans ih _)
    exact List.le_max?_getD_of_mem
      (List.mem_map.mpr ⟨⟨_, member⟩, List.mem_attach _ _, rfl⟩)

def PackedType.unionSlot : PackedType → Nat × PackedType
  | .padding before _ payload => (before, payload)
  | ty => (0, ty)

private theorem PackedType.unionSlot_represents {ty : PackedType} {code : Nat}
    (valid : ty.Represents code) : ty.unionSlot.2.Represents (code / 2 ^ ty.unionSlot.1) := by
  cases ty <;> simp only [unionSlot, Nat.pow_zero, Nat.div_one] at *
  all_goals first | exact valid | rw [Represents] at valid; exact valid.2.2

def PackedType.payloadTypeAt : PackedType → Nat → Option PackedType
  | .addressable _ payload, tag => payload.payloadTypeAt tag
  | .tagged variants, tag => variants[tag]?.map (fun variant => variant.unionSlot.2)
  | _, _ => none

/-- The selector and the payload code exclude padding around the union.
Padding inside the enclosing payload's own representation is retained. -/
def PackedType.splitTag : PackedType → Nat → Option (Nat × Nat)
  | .addressable _ payload, code => payload.splitTag code
  | .tagged variants, code =>
    let bound := 2 ^ ADTLayout.minTagBits variants.length
    let tag := code % bound
    variants[tag]?.map (fun variant => (tag, code / bound / 2 ^ variant.unionSlot.1))
  | _, _ => none

theorem PackedType.splitTag_typed {ty : PackedType} {code tag data : Nat}
    (valid : ty.Represents code) (split : ty.splitTag code = some (tag, data)) :
    ∃ payload, ty.payloadTypeAt tag = some payload ∧ payload.Represents data := by
  cases ty with
  | addressable alignment payload =>
    exact splitTag_typed (ty := payload) (by simpa only [Represents] using valid) split
  | tagged variants =>
    rw [Represents] at valid
    split at valid
    · contradiction
    · rename_i variant selected
      have found := eraseAttachedVariant selected
      simp only [splitTag, found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at split
      obtain ⟨rfl, rfl⟩ := split
      exact ⟨variant.val.unionSlot.2, by simp [payloadTypeAt, found], unionSlot_represents valid⟩
  | _ => simp [splitTag] at split
termination_by sizeOf ty

theorem PackedType.splitTag_padding {variants : List PackedType} {tag before after : Nat}
    {payload : PackedType} (selected : variants[tag]? = some (.padding before after payload))
    (tagFits : tag < 2 ^ ADTLayout.minTagBits variants.length) (code : Nat) :
    (PackedType.tagged variants).splitTag
      (tag + code * 2 ^ (ADTLayout.minTagBits variants.length + before)) = some (tag, code) := by
  have encoded : tag + code * 2 ^ (ADTLayout.minTagBits variants.length + before) =
      tag + (code * 2 ^ before) * 2 ^ ADTLayout.minTagBits variants.length := by
    rw [Nat.pow_add]
    ac_rfl
  obtain ⟨low, high⟩ := concatCode_split (high := code * 2 ^ before) tagFits
  rw [encoded, splitTag, low, high, selected]
  simp only [Option.map_some, unionSlot]
  simp only [Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- Steps address the encoded product shape. Padding and addressability
wrappers are explicit so a selector can stop at the intact child type. -/
inductive PackedType.FieldStep where
  | left | right | unpad | unwrapAddressable
  deriving Repr, DecidableEq

def PackedType.fieldStep : PackedType → FieldStep → Option (Nat × PackedType)
  | .product left _, .left => some (0, left)
  | .product left right, .right => some (left.width, right)
  | .padding before _ payload, .unpad => some (before, payload)
  | .addressable _ payload, .unwrapAddressable => some (0, payload)
  | _, _ => none

def PackedType.fieldAt (ty : PackedType) : List FieldStep → Option (Nat × PackedType)
  | [] => some (0, ty)
  | step :: rest => do
    let (offset, field) ← ty.fieldStep step
    let (inner, selected) ← field.fieldAt rest
    return (offset + inner, selected)

theorem PackedType.fieldAt_append {ty middle : PackedType} {first rest : List FieldStep} {start : Nat}
    (located : ty.fieldAt first = some (start, middle)) :
    ty.fieldAt (first ++ rest) = (middle.fieldAt rest).map (fun (offset, field) => (start + offset, field)) := by
  induction first generalizing ty start with
  | nil =>
    cases located
    simp
  | cons step first ih =>
    obtain ⟨⟨offset, child⟩, selected, nested⟩ := Option.bind_eq_some_iff.mp located
    obtain ⟨⟨inner, _⟩, below, equal⟩ := Option.bind_eq_some_iff.mp nested
    cases equal
    rw [List.cons_append]
    simp only [fieldAt, bind, selected, Option.bind_some, ih below]
    cases middle.fieldAt rest with
    | none => rfl
    | some result =>
      obtain ⟨position, field⟩ := result
      simp [Nat.add_assoc, pure]

def packedCodeSlice (code offset width : Nat) : Nat :=
  code / 2 ^ offset % 2 ^ width

theorem packedCodeSlice_slice {code offset outer inner width : Nat} (fits : inner + width ≤ outer) :
    packedCodeSlice (packedCodeSlice code offset outer) inner width =
      packedCodeSlice code (offset + inner) width := by
  have outerPow : 2 ^ outer = 2 ^ inner * 2 ^ (outer - inner) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (by omega : inner ≤ outer)]
  have divides : 2 ^ width ∣ 2 ^ (outer - inner) := Nat.pow_dvd_pow _ (by omega)
  unfold packedCodeSlice
  rw [outerPow, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ divides,
    Nat.div_div_eq_div_mul, Nat.pow_add]

private theorem PackedType.fieldStep_sound {ty field : PackedType} {step : FieldStep} {offset code : Nat}
    (found : ty.fieldStep step = some (offset, field)) (valid : ty.Represents code) :
    offset + field.width ≤ ty.width ∧ field.Represents (packedCodeSlice code offset field.width) := by
  cases ty <;> cases step <;> simp only [fieldStep, Option.some.injEq, Prod.mk.injEq] at found
  all_goals try contradiction
  · obtain ⟨rfl, rfl⟩ := found
    rw [Represents] at valid
    exact ⟨by simp [width], by simpa [packedCodeSlice] using valid.1⟩
  · obtain ⟨rfl, rfl⟩ := found
    rw [Represents] at valid
    exact ⟨by simp [width], by
      simpa only [packedCodeSlice, Nat.mod_eq_of_lt (codeFits _ _ valid.2)] using valid.2⟩
  · obtain ⟨rfl, rfl⟩ := found
    rw [Represents] at valid
    exact ⟨by simp [width], by
      simpa only [packedCodeSlice, Nat.mod_eq_of_lt (codeFits _ _ valid.2.2)] using valid.2.2⟩
  · obtain ⟨rfl, rfl⟩ := found
    rw [Represents] at valid
    exact ⟨by simp [width], by
      simpa [packedCodeSlice, Nat.mod_eq_of_lt (codeFits _ _ valid)] using valid⟩

theorem PackedType.fieldAt_sound {ty field : PackedType} {steps : List FieldStep} {offset code : Nat}
    (found : ty.fieldAt steps = some (offset, field)) (valid : ty.Represents code) :
    offset + field.width ≤ ty.width ∧ field.Represents (packedCodeSlice code offset field.width) := by
  induction steps generalizing ty offset code with
  | nil =>
    cases found
    exact ⟨by simp, by simpa [packedCodeSlice, Nat.mod_eq_of_lt (codeFits _ _ valid)] using valid⟩
  | cons step rest ih =>
    obtain ⟨⟨start, child⟩, selected, nested⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨⟨position, field⟩, inside, equal⟩ := Option.bind_eq_some_iff.mp nested
    cases equal
    obtain ⟨bounds, childValid⟩ := fieldStep_sound selected valid
    obtain ⟨innerBounds, fieldValid⟩ := ih inside childValid
    exact ⟨by omega, by rwa [packedCodeSlice_slice innerBounds] at fieldValid⟩

def PackedType.payloadFieldCode (ty : PackedType) (tag data : Nat) (steps : List FieldStep) : Option Nat := do
  let selected ← ty.payloadTypeAt tag
  let (offset, field) ← selected.fieldAt steps
  return packedCodeSlice data offset field.width

/-- Logical evaluation of a constructor-qualified projection on an encoded value. -/
def PackedType.projectTaggedCode (ty : PackedType) (expected code : Nat) (steps : List FieldStep) : Option Nat := do
  let (tag, payload) ← ty.splitTag code
  if tag = expected then ty.payloadFieldCode tag payload steps else none

end Aethel.AutomaticLayout
