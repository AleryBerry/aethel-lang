import Aethel.CoreNormalization
import Aethel.Machine
import Aethel.Functions
import Aethel.ResourceFrame
import Aethel.ADTLayout

namespace Aethel.Representation

open Functional Core Structured CoreAST ADTLayout

/-- Core data with a finite, dense representation. Functions and resources
have separate representation requirements and receive no dense descriptor. -/
inductive DenseData : CoreType → Nat → Type where
  | unit : DenseData .unit 1
  | bool : DenseData .bool 2
  | byte : DenseData .byte 256
  | prod : DenseData left a → DenseData right b → DenseData (.prod left right) (a * b)
  | sum : DenseData left a → DenseData right b → DenseData (.sum left right) (a + b)

def DenseData.ofType : (type : CoreType) → Option (Sigma (DenseData type))
  | .unit => some ⟨1, .unit⟩
  | .bool => some ⟨2, .bool⟩
  | .int false 8 => some ⟨256, .byte⟩
  | .prod left right => do
    let ⟨_, left⟩ ← ofType left
    let ⟨_, right⟩ ← ofType right
    return ⟨_, .prod left right⟩
  | .sum left right => do
    let ⟨_, left⟩ ← ofType left
    let ⟨_, right⟩ ← ofType right
    return ⟨_, .sum left right⟩
  | _ => none

theorem DenseData.ofType_exact {shape : DenseData type count} : DenseData.ofType type = some ⟨count, shape⟩ := by
  induction shape <;> simp [ofType, *, bind, pure]

private def densePair (first : Fin a) (second : Fin b) : Fin (a * b) :=
  ⟨second.val + b * first.val, by
    have below := second.isLt
    have capacity := Nat.mul_le_mul_left b (Nat.succ_le_of_lt first.isLt)
    rw [Nat.mul_succ, Nat.mul_comm b a] at capacity
    omega⟩

private def densePairParts (code : Fin (a * b)) : Fin a × Fin b :=
  have positive : 0 < b := by
    cases b with
    | zero => exact False.elim (Nat.not_lt_zero _ code.isLt)
    | succ => exact Nat.zero_lt_succ _
  (⟨code.val / b, (Nat.div_lt_iff_lt_mul positive).mpr code.isLt⟩,
    ⟨code.val % b, Nat.mod_lt _ positive⟩)

@[simp] private theorem densePair_parts (code : Fin (a * b)) :
    densePair (densePairParts code).1 (densePairParts code).2 = code :=
  Fin.ext (Nat.mod_add_div _ _)

@[simp] private theorem densePairParts_join (first : Fin a) (second : Fin b) :
    densePairParts (densePair first second) = (first, second) := by
  have within := second.isLt
  have positive := Nat.zero_lt_of_lt within
  apply Prod.ext <;> apply Fin.ext
  · change (second.val + b * first.val) / b = first.val
    rw [Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt within, Nat.zero_add]
  · change (second.val + b * first.val) % b = second.val
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt within]

private theorem literalByte_iff (value : Int) : LiteralFits false 8 value ↔ 0 ≤ value ∧ value < 256 := by
  rfl

def DenseData.decode : DenseData ty count → Fin count → CoreExpr
  | .unit, _ => .unit
  | .bool, code => .bool (code.val == 1)
  | .byte, code => .int false 8 code.val
  | .prod left right, code =>
    let (a, b) := densePairParts code
    .pair (left.decode a) (right.decode b)
  | @sum leftTy _ rightTy _ left right, code =>
    match denseVariant code with
    | .inl index => .inject true (leftTy, rightTy) (left.decode index)
    | .inr index => .inject false (leftTy, rightTy) (right.decode index)

def DenseData.encode : DenseData ty count → CoreExpr → Option (Fin count)
  | .unit, .unit => some 0
  | .bool, .bool value => some (if value then 1 else 0)
  | .byte, .int signed width value =>
    if fits : signed = false ∧ width = 8 ∧ LiteralFits false 8 value then
      some ⟨value.toNat, by have := (literalByte_iff value).mp fits.2.2; omega⟩
    else none
  | .prod left right, .pair a b => do
    return densePair (← left.encode a) (← right.encode b)
  | @sum leftTy _ rightTy _ left right, .inject side variants payload =>
    if variants = (leftTy, rightTy) then
      if side then (left.encode payload).map (denseIndex ∘ Sum.inl)
      else (right.encode payload).map (denseIndex ∘ Sum.inr)
    else none
  | _, _ => none

theorem DenseData.decoded_computable (shape : DenseData ty count) (code : Fin count) :
    Computable ty (shape.decode code) := by
  induction shape with
  | unit => exact ⟨.unit, .unit [], trivial⟩
  | bool => exact ⟨.bool _, .bool [] _, trivial⟩
  | byte =>
    refine ⟨.int .., .int [] false 8 _ ((literalByte_iff _).mpr ?_), trivial⟩
    have := code.isLt
    omega
  | prod left right ihLeft ihRight =>
    exact (ihLeft (densePairParts code).1).pair (ihRight (densePairParts code).2)
  | sum left right ihLeft ihRight =>
    rw [decode]
    cases denseVariant code with
    | inl index => exact Computable.inject (side := true) (ihLeft index)
    | inr index => exact Computable.inject (side := false) (ihRight index)

theorem DenseData.decoded_value (shape : DenseData ty count) (code : Fin count) :
    Value (shape.decode code) ∧ WellTyped [] (shape.decode code) ty .empty :=
  ⟨(shape.decoded_computable code).isValue, (shape.decoded_computable code).typed⟩

theorem DenseData.encode_decode (shape : DenseData ty count) (code : Fin count) :
    shape.encode (shape.decode code) = some code := by
  induction shape with
  | unit => exact congrArg some (Fin.ext (by have := code.isLt; omega))
  | bool =>
    have within := code.isLt
    by_cases set : code.val = 1
    · have same : code = 1 := Fin.ext set
      cases same
      rfl
    · have same : code = 0 := Fin.ext (by omega)
      cases same
      rfl
  | byte =>
    have checked : false = false ∧ 8 = 8 ∧ LiteralFits false 8 ↑code.val :=
      ⟨rfl, rfl, (literalByte_iff _).mpr (by have := code.isLt; omega)⟩
    rw [decode, encode, dite_eq_left checked]
    exact congrArg some (Fin.ext (Int.toNat_natCast _))
  | prod left right ihLeft ihRight =>
    simp [decode, encode, ihLeft, ihRight, bind, pure]
  | sum left right ihLeft ihRight =>
    rw [decode]
    have coded := denseIndex_variant code
    cases side : denseVariant code
    · rw [side] at coded
      simp [encode, ihLeft, Function.comp_def, coded]
    · rw [side] at coded
      simp [encode, ihRight, Function.comp_def, coded]

private theorem DenseData.decode_encode (shape : DenseData ty count) {value : CoreExpr} {code : Fin count}
    (encoded : shape.encode value = some code) : shape.decode code = value := by
  induction shape generalizing value with
  | unit => cases value <;> simp [encode] at encoded; rfl
  | bool =>
    cases value <;> simp [encode] at encoded
    case bool flag =>
      subst code
      cases flag <;> rfl
  | byte =>
    cases value <;> simp only [encode, reduceCtorEq] at encoded
    case int =>
      split at encoded
      · rename_i checked
        obtain ⟨rfl, rfl, fit⟩ := checked
        obtain rfl := Option.some.inj encoded
        exact congrArg (CoreExpr.int false 8) (Int.toNat_of_nonneg ((literalByte_iff _).mp fit).1)
      · contradiction
  | prod left right ihLeft ihRight =>
    cases value <;> simp [encode, bind, pure, Option.bind_eq_some_iff] at encoded
    case pair =>
      obtain ⟨a, leftCode, b, rightCode, rfl⟩ := encoded
      simp [decode, ihLeft leftCode, ihRight rightCode]
  | sum left right ihLeft ihRight =>
    cases value <;> simp only [encode, Option.ite_none_right_eq_some, reduceCtorEq] at encoded
    case inject side variants payload =>
      obtain ⟨rfl, encoded⟩ := encoded
      cases side
      · obtain ⟨index, selected, rfl⟩ := Option.map_eq_some_iff.mp encoded
        simp [decode, ihRight selected]
      · obtain ⟨index, selected, rfl⟩ := Option.map_eq_some_iff.mp encoded
        simp [decode, ihLeft selected]

theorem DenseData.encode_correct (shape : DenseData ty count) {value : CoreExpr} {code : Fin count} :
    shape.encode value = some code ↔ shape.decode code = value :=
  ⟨shape.decode_encode, fun same => same ▸ shape.encode_decode code⟩

theorem DenseData.encode_total (shape : DenseData ty count) {value : CoreExpr} {effect : Effect}
    (ready : Value value) (typed : WellTyped [] value ty effect) :
    ∃ code, shape.encode value = some code := by
  induction ready generalizing ty count effect with
  | unit => cases typed; cases shape; exact ⟨_, rfl⟩
  | bool => cases typed; cases shape; exact ⟨_, rfl⟩
  | nat => cases typed; cases shape
  | lam => cases typed; cases shape
  | adt => cases typed; cases shape
  | int signed bits value =>
    cases typed with
    | int _ _ _ _ fits =>
      cases shape
      have within : value.toNat < 256 := by have := (literalByte_iff value).mp fits; omega
      refine ⟨⟨value.toNat, within⟩, ?_⟩
      rw [encode, dite_eq_left (show false = false ∧ 8 = 8 ∧ LiteralFits false 8 value from ⟨rfl, rfl, fits⟩)]
  | pair readyLeft readyRight ihLeft ihRight =>
    cases typed with
    | pair leftTyped rightTyped =>
      cases shape with
      | prod left right =>
        obtain ⟨a, foundLeft⟩ := ihLeft left leftTyped
        obtain ⟨b, foundRight⟩ := ihRight right rightTyped
        exact ⟨densePair a b, by simp [encode, foundLeft, foundRight, bind, pure]⟩
  | inject side variants ready ih =>
    cases variants with
    | mk leftTy rightTy =>
      cases typed with
      | inject _ _ payloadTyped =>
        cases shape with
        | sum left right =>
          cases side
          · obtain ⟨index, encoded⟩ := ih right payloadTyped
            exact ⟨denseIndex (.inr index), by simp [encode, encoded, Function.comp_def]⟩
          · obtain ⟨index, encoded⟩ := ih left payloadTyped
            exact ⟨denseIndex (.inl index), by simp [encode, encoded, Function.comp_def]⟩

theorem DenseData.minimum_width (shape : DenseData ty count) (width : Nat) (encode : CoreExpr → BitVec width)
    (distinct : ∀ {a b}, Value a → WellTyped [] a ty .empty → Value b → WellTyped [] b ty .empty →
      encode a = encode b → a = b) : minTagBits count ≤ width := by
  apply packDenseIndex_minimum (encode ∘ shape.decode)
  intro a b same
  obtain ⟨readyA, typedA⟩ := shape.decoded_value a
  obtain ⟨readyB, typedB⟩ := shape.decoded_value b
  have values := distinct readyA typedA readyB typedB same
  exact Option.some.inj ((shape.encode_decode a).symm.trans (congrArg shape.encode values) |>.trans
    (shape.encode_decode b))

structure DenseDataField (size : Nat) (type : CoreType) where
  count : Nat
  shape : DenseData type count
  slot : DenseIndexField size count

def DenseDataField.load (field : DenseDataField size ty) (image : AutomaticLayout.Image size) : Option CoreExpr :=
  (field.slot.load image).map field.shape.decode

def DenseDataField.store (field : DenseDataField size ty) (image : AutomaticLayout.Image size)
    (value : CoreExpr) : Option (AutomaticLayout.Image size) :=
  (field.shape.encode value).map (field.slot.store image)

def DenseDataField.Represents (field : DenseDataField size ty) (image : AutomaticLayout.Image size)
    (value : CoreExpr) : Prop :=
  ∃ code, field.shape.decode code = value ∧
    image.readBits field.slot.offset (minTagBits field.count) = packDenseIndex code

theorem DenseDataField.load_correct (field : DenseDataField size ty) (image : AutomaticLayout.Image size)
    (value : CoreExpr) : field.load image = some value ↔ field.Represents image value := by
  simp only [load, Represents, Option.map_eq_some_iff, DenseIndexField.load_correct]
  exact exists_congr fun _ => and_comm

theorem DenseDataField.store_roundtrip (field : DenseDataField size ty)
    (image : AutomaticLayout.Image size) {value : CoreExpr} (ready : Value value)
    (typed : WellTyped [] value ty effect) :
    ∃ updated, field.store image value = some updated ∧ field.Represents updated value ∧
      ∀ offset width, offset + width ≤ size * 8 →
        field.slot.offset + minTagBits field.count ≤ offset ∨ offset + width ≤ field.slot.offset →
        updated.readBits offset width = image.readBits offset width := by
  obtain ⟨code, encoded⟩ := field.shape.encode_total ready typed
  refine ⟨field.slot.store image code, by simp [store, encoded], ?_, ?_⟩
  · apply (field.load_correct ..).mp
    simp [load, DenseIndexField.load_store, field.shape.encode_correct.mp encoded]
  · intro offset width fits outside
    exact field.slot.store_frames_bits image code offset width fits outside

/-- Logical-to-physical byte representation relation. -/
inductive Represents : CoreExpr → CoreType → List UInt8 → Prop where
  | unit :
      Represents .unit .unit []
  | bool (b : Bool) :
      Represents (.bool b) .bool [if b then 1 else 0]
  | byte (v : UInt8) :
      Represents (.int false 8 (Int.ofNat v.toNat)) CoreType.byte [v]
  | uint16 (v : UInt16) :
      Represents (.int false 16 (Int.ofNat v.toNat)) CoreType.uint16 [splitLow v, splitHigh v]
  | prod {a b : CoreExpr} {tyA tyB : CoreType} {bytesA bytesB : List UInt8} :
      Represents a tyA bytesA →
      Represents b tyB bytesB →
      Represents (.pair a b) (.prod tyA tyB) (bytesA ++ bytesB)
  | adt (tag : Nat) {p : CoreExpr} {tyP : CoreType} {bytesP : List UInt8} :
      Represents p tyP bytesP →
      Represents (.adt tag p) (.adt tag tyP) (tag.toUInt8 :: bytesP)

/-- Size of physical byte representation if fixed. -/
def typeSize : CoreType → Option Nat
  | .unit => some 0
  | .bool => some 1
  | .int false 8 => some 1
  | .int false 16 => some 2
  | .prod tyA tyB => do
      let sA ← typeSize tyA
      let sB ← typeSize tyB
      return sA + sB
  | .adt _ tyP => do
      let sP ← typeSize tyP
      return 1 + sP
  | _ => none

theorem represents_length {e : CoreExpr} {ty : CoreType} {bytes : List UInt8}
    (h : Represents e ty bytes) :
    ∃ sz, typeSize ty = some sz ∧ bytes.length = sz := by
  induction h with
  | unit =>
    exact ⟨0, rfl, rfl⟩
  | bool b =>
    exact ⟨1, rfl, rfl⟩
  | byte v =>
    exact ⟨1, rfl, rfl⟩
  | uint16 v =>
    exact ⟨2, rfl, rfl⟩
  | prod ha hb iha ihb =>
    obtain ⟨sA, hszA, hlenA⟩ := iha
    obtain ⟨sB, hszB, hlenB⟩ := ihb
    refine ⟨sA + sB, ?_, ?_⟩
    · dsimp [typeSize]
      simp [hszA, hszB]
    · simp [List.length_append, hlenA, hlenB]
  | adt tag hp ih =>
    obtain ⟨sP, hszP, hlenP⟩ := ih
    refine ⟨1 + sP, ?_, ?_⟩
    · dsimp [typeSize]
      simp [hszP]
    · simp [hlenP, Nat.add_comm]

def decodeBool (bytes : List UInt8) : Option CoreExpr :=
  match bytes with
  | [0] => some (.bool false)
  | [1] => some (.bool true)
  | _ => none

theorem decodeBool_correct (b : Bool) :
    decodeBool [if b then 1 else 0] = some (.bool b) := by
  cases b <;> rfl

def decodeByte (bytes : List UInt8) : Option CoreExpr :=
  match bytes with
  | [b] => some (.int false 8 (Int.ofNat b.toNat))
  | _ => none

theorem decodeByte_correct (v : UInt8) :
    decodeByte [v] = some (.int false 8 (Int.ofNat v.toNat)) := rfl

def decodeUInt16LE_expr (bytes : List UInt8) : Option CoreExpr :=
  match bytes with
  | [lo, hi] => some (.int false 16 (Int.ofNat (decodeUInt16LE lo hi).toNat))
  | _ => none

theorem decodeUInt16LE_expr_correct (v : UInt16) :
    decodeUInt16LE_expr [splitLow v, splitHigh v] =
      some (.int false 16 (Int.ofNat v.toNat)) := by
  dsimp [decodeUInt16LE_expr]
  rw [decodeUInt16LE_split]

/-- A logical expression is represented in state `s` starting at `baseOffset` of `owner`. -/
def HeapRepresents (s : State) (owner : OwnerId) (baseOffset : Nat)
    (e : CoreExpr) (ty : CoreType) : Prop :=
  ∃ bytes, Represents e ty bytes ∧
    ∀ i : Nat, (h : i < bytes.length) →
      s.byte ⟨owner, baseOffset + i⟩ = some bytes[i]

theorem rep_alloc_simulation (s : State) (owner : OwnerId) (e : CoreExpr) (ty : CoreType)
    (bytes : List UInt8) (hRep : Represents e ty bytes) :
    HeapRepresents (s.addAllocation owner bytes) owner 0 e ty := by
  refine ⟨bytes, hRep, ?_⟩
  intro i hi
  dsimp [State.byte, State.addAllocation, State.allocation]
  simp only [List.find?_cons]
  have heq : (owner == owner) = true := by simp
  rw [heq]
  dsimp
  rw [Nat.zero_add]
  exact List.getElem?_eq_getElem hi

theorem rep_alloc_preserves_other (s : State) (owner other : OwnerId)
    (bytes : List UInt8) (hne : other ≠ owner) (off : Nat) (e : CoreExpr) (ty : CoreType)
    (hOld : HeapRepresents s other off e ty) :
    HeapRepresents (s.addAllocation owner bytes) other off e ty := by
  obtain ⟨bs, hRep, hBytes⟩ := hOld
  refine ⟨bs, hRep, ?_⟩
  intro i hi
  have hOldByte := hBytes i hi
  dsimp [State.byte, State.addAllocation, State.allocation] at *
  simp only [List.find?_cons]
  have hne_bool : (owner == other) = false := by
    simp [beq_eq_false_iff_ne, Ne.symm hne]
  rw [hne_bool]
  exact hOldByte

theorem rep_read_byte_simulation (s : State) (owner : OwnerId) (baseOffset : Nat)
    (e : CoreExpr) (hRep : HeapRepresents s owner baseOffset e CoreType.byte) :
    ∃ v : UInt8, e = .int false 8 (Int.ofNat v.toNat) ∧
      s.byte ⟨owner, baseOffset⟩ = some v := by
  obtain ⟨bs, hR, hBytes⟩ := hRep
  cases hR with
  | byte v =>
    refine ⟨v, rfl, ?_⟩
    have b0 := hBytes 0 Nat.zero_lt_one
    rw [Nat.add_zero] at b0
    exact b0

theorem rep_read_uint16_simulation (s : State) (owner : OwnerId) (baseOffset : Nat)
    (e : CoreExpr) (hRep : HeapRepresents s owner baseOffset e CoreType.uint16) :
    ∃ v : UInt16, e = .int false 16 (Int.ofNat v.toNat) ∧
      s.byte ⟨owner, baseOffset⟩ = some (splitLow v) ∧
      s.byte ⟨owner, baseOffset + 1⟩ = some (splitHigh v) := by
  obtain ⟨bs, hR, hBytes⟩ := hRep
  cases hR with
  | uint16 v =>
    refine ⟨v, rfl, ?_⟩
    have b0 := hBytes 0 (by decide : 0 < 2)
    have b1 := hBytes 1 (by decide : 1 < 2)
    rw [Nat.add_zero] at b0
    exact ⟨b0, b1⟩

theorem State.removeOwner_allocation_other (s : State) (owner other : OwnerId)
    (hne : other ≠ owner) :
    (s.removeOwner owner).allocation other = s.allocation other := by
  simp only [State.allocation, State.removeOwner, List.find?_filter]
  congr 1
  funext a
  by_cases same : a.owner = other
  · subst same
    have hne_bool : (a.owner != owner) = true := by
      simp [bne_iff_ne, hne]
    simp [hne_bool]
  · have hne_bool : (a.owner == other) = false := by
      simp [beq_eq_false_iff_ne, same]
    simp [hne_bool]

theorem State.removeOwner_byte_other (s : State) (owner other : OwnerId)
    (hne : other ≠ owner) (off : Nat) :
    (s.removeOwner owner).byte ⟨other, off⟩ = s.byte ⟨other, off⟩ := by
  dsimp [State.byte]
  rw [State.removeOwner_allocation_other s owner other hne]

theorem rep_destroy_simulation (s : State) (owner other : OwnerId)
    (hne : other ≠ owner) (off : Nat) (e : CoreExpr) (ty : CoreType) :
    HeapRepresents (s.removeOwner owner) other off e ty ↔ HeapRepresents s other off e ty := by
  constructor
  · rintro ⟨bs, hRep, hBytes⟩
    refine ⟨bs, hRep, ?_⟩
    intro i hi
    have h := hBytes i hi
    rw [State.removeOwner_byte_other s owner other hne] at h
    exact h
  · rintro ⟨bs, hRep, hBytes⟩
    refine ⟨bs, hRep, ?_⟩
    intro i hi
    have h := hBytes i hi
    rw [State.removeOwner_byte_other s owner other hne]
    exact h

theorem rep_write_byte_simulation (s : State) (owner : OwnerId) (baseOffset : Nat)
    (oldByte : CoreExpr) (newVal : UInt8)
    (hOld : HeapRepresents s owner baseOffset oldByte CoreType.byte) :
    HeapRepresents (s.store ⟨owner, baseOffset⟩ newVal) owner baseOffset
      (.int false 8 (Int.ofNat newVal.toNat)) CoreType.byte := by
  obtain ⟨v, _, hByte⟩ := rep_read_byte_simulation s owner baseOffset oldByte hOld
  refine ⟨[newVal], .byte newVal, ?_⟩
  intro i hi
  have hlen : [newVal].length = 1 := rfl
  rw [hlen] at hi
  have hi0 : i = 0 := by omega
  subst hi0
  simp only [Nat.add_zero, List.getElem_cons_zero]
  exact State.store_byte_written s ⟨owner, baseOffset⟩ v newVal hByte

theorem rep_write_preserves_other (s : State) (written : ByteLocation) (newVal : UInt8)
    (other : OwnerId) (off : Nat) (e : CoreExpr) (ty : CoreType)
    (hne : other ≠ written.allocation)
    (hOld : HeapRepresents s other off e ty) :
    HeapRepresents (s.store written newVal) other off e ty := by
  obtain ⟨bs, hRep, hBytes⟩ := hOld
  refine ⟨bs, hRep, ?_⟩
  intro i hi
  have hOldByte := hBytes i hi
  have hDiff : written ≠ ⟨other, off + i⟩ := by
    intro hEq
    have hAlloc : written.allocation = other := congrArg ByteLocation.allocation hEq
    exact hne hAlloc.symm
  rw [State.store_byte_other s written ⟨other, off + i⟩ newVal hDiff]
  exact hOldByte

theorem rep_write_preserves_sibling (s : State) (owner : OwnerId) (writtenOff : Nat) (newVal : UInt8)
    (siblingOff : Nat) (e : CoreExpr) (ty : CoreType)
    (hDisjoint : ∀ i, (h : i < (typeSize ty).getD 1) → writtenOff ≠ siblingOff + i)
    (hOld : HeapRepresents s owner siblingOff e ty) :
    HeapRepresents (s.store ⟨owner, writtenOff⟩ newVal) owner siblingOff e ty := by
  obtain ⟨bs, hRep, hBytes⟩ := hOld
  refine ⟨bs, hRep, ?_⟩
  intro i hi
  have hDiff : (⟨owner, writtenOff⟩ : ByteLocation) ≠ ⟨owner, siblingOff + i⟩ := by
    intro hEq
    have hOff : writtenOff = siblingOff + i := congrArg ByteLocation.offset hEq
    obtain ⟨sz, hsz, hlen⟩ := represents_length hRep
    have hszD : (typeSize ty).getD 1 = sz := by
      simp [hsz]
    rw [hlen] at hi
    have hDisj := hDisjoint i (by rw [hszD]; exact hi)
    exact hDisj hOff
  rw [State.store_byte_other s ⟨owner, writtenOff⟩ ⟨owner, siblingOff + i⟩ newVal hDiff]
  exact hBytes i hi

end Aethel.Representation
