import Aethel.CoreAST
import Aethel.CoreSemantics
import Aethel.Machine
import Aethel.Functions
import Aethel.ResourceFrame

namespace Aethel.Representation

open Functional Core Structured CoreAST

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
