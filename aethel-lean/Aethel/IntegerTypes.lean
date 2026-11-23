import Std

namespace Aethel

/-- Maximum supported bit width for Aethel arbitrary-width integers (matches Zig's u16 bit-width bound). -/
def maxIntegerBits : Nat := 65535

/-- Arbitrary positive integer bit width (`1 ≤ bits ≤ 65535`). -/
structure IntegerWidth where
  bits : Nat
  pos : 0 < bits
  le_max : bits ≤ maxIntegerBits
  deriving Repr, DecidableEq

@[ext] theorem IntegerWidth.ext {a b : IntegerWidth} (h : a.bits = b.bits) : a = b := by
  cases a; cases b; simp_all

def IntegerWidth.ofNat? (n : Nat) : Option IntegerWidth :=
  if hPos : 0 < n then
    if hMax : n ≤ maxIntegerBits then
      some ⟨n, hPos, hMax⟩
    else none
  else none

theorem IntegerWidth.ofNat?_some_iff {n : Nat} {w : IntegerWidth} :
    IntegerWidth.ofNat? n = some w ↔ w.bits = n := by
  constructor
  · intro h
    unfold ofNat? at h
    split at h
    · split at h
      · simp at h
        rw [← h]
      · simp at h
    · simp at h
  · intro h
    subst h
    simp [ofNat?, w.pos, w.le_max]

theorem IntegerWidth.ofNat?_isSome_iff (n : Nat) :
    (IntegerWidth.ofNat? n).isSome = true ↔ 0 < n ∧ n ≤ maxIntegerBits := by
  by_cases hPos : 0 < n
  · by_cases hMax : n ≤ maxIntegerBits
    · simp [ofNat?, hPos, hMax]
    · simp [ofNat?, hPos, hMax]
  · simp [ofNat?, hPos]

abbrev IntegerWidth.w1 : IntegerWidth := ⟨1, by decide, by decide⟩
abbrev IntegerWidth.w2 : IntegerWidth := ⟨2, by decide, by decide⟩
abbrev IntegerWidth.w3 : IntegerWidth := ⟨3, by decide, by decide⟩
abbrev IntegerWidth.w4 : IntegerWidth := ⟨4, by decide, by decide⟩
abbrev IntegerWidth.w5 : IntegerWidth := ⟨5, by decide, by decide⟩
abbrev IntegerWidth.w6 : IntegerWidth := ⟨6, by decide, by decide⟩
abbrev IntegerWidth.w7 : IntegerWidth := ⟨7, by decide, by decide⟩
abbrev IntegerWidth.w8 : IntegerWidth := ⟨8, by decide, by decide⟩
abbrev IntegerWidth.w16 : IntegerWidth := ⟨16, by decide, by decide⟩
abbrev IntegerWidth.w24 : IntegerWidth := ⟨24, by decide, by decide⟩
abbrev IntegerWidth.w32 : IntegerWidth := ⟨32, by decide, by decide⟩
abbrev IntegerWidth.w48 : IntegerWidth := ⟨48, by decide, by decide⟩
abbrev IntegerWidth.w64 : IntegerWidth := ⟨64, by decide, by decide⟩
abbrev IntegerWidth.w128 : IntegerWidth := ⟨128, by decide, by decide⟩
abbrev IntegerWidth.w256 : IntegerWidth := ⟨256, by decide, by decide⟩

inductive IntegerType where
  | unsigned (width : IntegerWidth)
  | signed (width : IntegerWidth)
  deriving Repr, DecidableEq

def IntegerType.width : IntegerType → IntegerWidth
  | .unsigned width | .signed width => width

def IntegerType.bits (ty : IntegerType) : Nat := ty.width.bits

theorem IntegerType.bits_pos (ty : IntegerType) : 0 < ty.bits :=
  ty.width.pos

theorem IntegerType.bits_le_max (ty : IntegerType) : ty.bits ≤ maxIntegerBits :=
  ty.width.le_max

def IntegerType.spelling (ty : IntegerType) : String :=
  (match ty with | .unsigned _ => "u" | .signed _ => "i") ++ toString ty.bits

@[reducible] def UnsignedValue (n : Nat) : Type :=
  match n with
  | 0 => BitVec 0
  | 1 => BitVec 1
  | 2 => BitVec 2
  | 3 => BitVec 3
  | 4 => BitVec 4
  | 5 => BitVec 5
  | 6 => BitVec 6
  | 7 => BitVec 7
  | 8 => UInt8
  | 9 => BitVec 9
  | 10 => BitVec 10
  | 11 => BitVec 11
  | 12 => BitVec 12
  | 13 => BitVec 13
  | 14 => BitVec 14
  | 15 => BitVec 15
  | 16 => UInt16
  | k + 17 => BitVec (k + 17)

@[reducible] def IntegerType.Value : IntegerType → Type
  | .unsigned w => UnsignedValue w.bits
  | .signed w => BitVec w.bits

-- Verify definitional reduction and typeclass synthesis for `Functions.lean` and `BranchFacts.lean`.
example : (IntegerType.unsigned .w8).Value = UInt8 := rfl
example : (IntegerType.unsigned .w16).Value = UInt16 := rfl
example : BEq (IntegerType.unsigned .w8).Value := inferInstance
example : LT (IntegerType.unsigned .w8).Value := inferInstance
example : DecidableEq (IntegerType.unsigned .w1).Value := inferInstance

def IntegerType.Fits (ty : IntegerType) (literal : Int) : Prop :=
  match ty with
  | .unsigned width => 0 ≤ literal ∧ literal < (2 : Int) ^ width.bits
  | .signed width => -(2 : Int) ^ (width.bits - 1) ≤ literal ∧
      literal < (2 : Int) ^ (width.bits - 1)

instance IntegerType.instDecidableFits (ty : IntegerType) (literal : Int) : Decidable (ty.Fits literal) :=
  match ty with
  | .unsigned _ => inferInstanceAs (Decidable (_ ∧ _))
  | .signed _ => inferInstanceAs (Decidable (_ ∧ _))

private theorem unsignedValue_eq_8 {n : Nat} (h8 : n = 8) : UnsignedValue n = UInt8 := by
  subst h8; rfl

private theorem unsignedValue_eq_16 {n : Nat} (_h8 : n ≠ 8) (h16 : n = 16) :
    UnsignedValue n = UInt16 := by
  subst h16; rfl

private theorem unsignedValue_eq_other {n : Nat} (h8 : n ≠ 8) (h16 : n ≠ 16) :
    UnsignedValue n = BitVec n := by
  match n with
  | 8 => exact False.elim (h8 rfl)
  | 16 => exact False.elim (h16 rfl)
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | _ + 17 => rfl

private def encodeUnsignedNat (literal : Int) (n : Nat) : UnsignedValue n :=
  if h8 : n = 8 then
    (unsignedValue_eq_8 h8).symm ▸ literal.toNat.toUInt8
  else if h16 : n = 16 then
    (unsignedValue_eq_16 h8 h16).symm ▸ literal.toNat.toUInt16
  else
    (unsignedValue_eq_other h8 h16).symm ▸ BitVec.ofInt n literal

private def encodeLiteral (literal : Int) : (ty : IntegerType) → ty.Value
  | .unsigned width => encodeUnsignedNat literal width.bits
  | .signed width => BitVec.ofInt width.bits literal

def IntegerType.literalValue (ty : IntegerType) (literal : Int)
    (_fits : ty.Fits literal) : ty.Value :=
  encodeLiteral literal ty

def IntegerType.checkedLiteral (ty : IntegerType) (literal : Int) : Option ty.Value :=
  if fits : ty.Fits literal then some (ty.literalValue literal fits) else none

theorem IntegerType.checkedLiteral_correct (ty : IntegerType) (literal : Int) :
    (ty.checkedLiteral literal).isSome = true ↔ ty.Fits literal := by
  by_cases fits : ty.Fits literal <;> simp [checkedLiteral, fits]

private theorem two_pow_sub_one_eq_bmod {w : Nat} (hw : 0 < w) (literal : Int)
    (hLow : -(2 : Int) ^ (w - 1) ≤ literal) (hHigh : literal < (2 : Int) ^ (w - 1)) :
    literal.bmod (2 ^ w) = literal := by
  have hwEq : w = (w - 1) + 1 := (Nat.sub_add_cancel hw).symm
  have hModEq : 2 ^ w = 2 * 2 ^ (w - 1) := by
    calc
      2 ^ w = 2 ^ ((w - 1) + 1) := by rw [← hwEq]
      _ = 2 ^ (w - 1) * 2 := Nat.pow_succ _ _
      _ = 2 * 2 ^ (w - 1) := Nat.mul_comm _ _
  have hModCast : ((2 ^ w : Nat) : Int) = 2 * ((2 ^ (w - 1) : Nat) : Int) := by
    rw [hModEq, Int.natCast_mul]
    rfl
  have hNatCast : ((2 ^ (w - 1) : Nat) : Int) = (2 : Int) ^ (w - 1) := by
    rw [Int.natCast_pow]
    rfl
  apply Int.bmod_eq_of_le <;> omega

theorem IntegerType.signedLiteral_value (width : IntegerWidth) (literal : Int)
    (fits : (IntegerType.signed width).Fits literal) :
    ((IntegerType.signed width).literalValue literal fits).toInt = literal := by
  change (BitVec.ofInt width.bits literal).toInt = literal
  rw [BitVec.toInt_ofInt]
  exact two_pow_sub_one_eq_bmod width.pos literal fits.1 fits.2

private theorem cast_symm_cancel {α β : Type} (h : β = α) (x : α) :
    h ▸ (h.symm ▸ x) = x := by
  cases h; rfl

private def unsignedToNat (n : Nat) (v : UnsignedValue n) : Nat :=
  if h8 : n = 8 then
    ((unsignedValue_eq_8 h8) ▸ v).toNat
  else if h16 : n = 16 then
    ((unsignedValue_eq_16 h8 h16) ▸ v).toNat
  else
    ((unsignedValue_eq_other h8 h16) ▸ v).toNat

def IntegerType.unsignedNat (width : IntegerWidth) : (IntegerType.unsigned width).Value → Nat :=
  unsignedToNat width.bits

private theorem unsignedToNat_encodeUnsignedNat (n : Nat) (literal : Int)
    (nonnegative : 0 ≤ literal) (within : literal < (2 : Int) ^ n) :
    unsignedToNat n (encodeUnsignedNat literal n) = literal.toNat := by
  have intMod : (literal % ↑((2 : Nat) ^ n)).toNat = literal.toNat := by
    rw [Int.natCast_pow]
    change (literal % (2 : Int) ^ n).toNat = _
    rw [Int.emod_eq_of_lt nonnegative within]
  have natMod : literal.toNat % 2 ^ n = literal.toNat := by
    apply Nat.mod_eq_of_lt
    exact Int.ofNat_lt.mp (by simpa [Int.toNat_of_nonneg nonnegative] using within)
  by_cases h8 : n = 8
  · subst h8
    simp only [unsignedToNat, encodeUnsignedNat, ↓reduceDIte,
      Nat.toUInt8, UInt8.toNat_ofNat']
    exact natMod
  · by_cases h16 : n = 16
    · subst h16
      simp only [unsignedToNat, encodeUnsignedNat, h8, ↓reduceDIte,
        Nat.toUInt16, UInt16.toNat_ofNat']
      exact natMod
    · unfold unsignedToNat encodeUnsignedNat
      simp only [h8, ↓reduceDIte, h16, cast_symm_cancel]
      exact intMod

theorem IntegerType.unsignedLiteral_value (width : IntegerWidth) (literal : Int)
    (fits : (IntegerType.unsigned width).Fits literal) :
    unsignedNat width ((IntegerType.unsigned width).literalValue literal fits) = literal.toNat :=
  unsignedToNat_encodeUnsignedNat width.bits literal fits.1 fits.2

private def unsignedFromBits (n : Nat) (bits : BitVec n) : UnsignedValue n :=
  if h8 : n = 8 then
    (unsignedValue_eq_8 h8).symm ▸ UInt8.ofBitVec (h8 ▸ bits)
  else if h16 : n = 16 then
    (unsignedValue_eq_16 h8 h16).symm ▸ UInt16.ofBitVec (h16 ▸ bits)
  else
    (unsignedValue_eq_other h8 h16).symm ▸ bits

private def unsignedToBits (n : Nat) (value : UnsignedValue n) : BitVec n :=
  if h8 : n = 8 then
    h8 ▸ ((unsignedValue_eq_8 h8) ▸ value).toBitVec
  else if h16 : n = 16 then
    h16 ▸ ((unsignedValue_eq_16 h8 h16) ▸ value).toBitVec
  else
    (unsignedValue_eq_other h8 h16) ▸ value

def IntegerType.fromBits : (kind : IntegerType) → BitVec kind.bits → kind.Value
  | .unsigned w, bits => unsignedFromBits w.bits bits
  | .signed _, bits => bits

def IntegerType.toBits : (kind : IntegerType) → kind.Value → BitVec kind.bits
  | .unsigned w, value => unsignedToBits w.bits value
  | .signed _, value => value

private theorem unsignedToBits_fromBits (n : Nat) (bits : BitVec n) :
    unsignedToBits n (unsignedFromBits n bits) = bits := by
  by_cases h8 : n = 8
  · subst h8
    simp only [unsignedToBits, unsignedFromBits, ↓reduceDIte, UInt8.toBitVec_ofBitVec]
  · by_cases h16 : n = 16
    · subst h16
      simp only [unsignedToBits, unsignedFromBits, h8, ↓reduceDIte, UInt16.toBitVec_ofBitVec]
    · unfold unsignedToBits unsignedFromBits
      simp only [h8, ↓reduceDIte, h16]
      exact cast_symm_cancel (unsignedValue_eq_other h8 h16) bits

theorem IntegerType.toBits_fromBits (kind : IntegerType) (bits : BitVec kind.bits) :
    kind.toBits (kind.fromBits bits) = bits := by
  cases kind with
  | signed _ => rfl
  | unsigned w => exact unsignedToBits_fromBits w.bits bits

private def parsePositiveDigitsAux (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: rest =>
    if '0' ≤ c ∧ c ≤ '9' then
      let d := c.toNat - '0'.toNat
      parsePositiveDigitsAux (acc * 10 + d) rest
    else none

private def parsePositiveNat? : List Char → Option Nat
  | [] => none
  | c :: rest =>
    if '1' ≤ c ∧ c ≤ '9' then
      parsePositiveDigitsAux (c.toNat - '0'.toNat) rest
    else none

/-- Parse surface integer type spellings such as `u1`, `i7`, `u128`, `u65535`.
Rejects `u0`, `i0`, leading zeroes (`u08`), and widths above `maxIntegerBits`. -/
def IntegerType.parse? (s : String) : Option IntegerType :=
  match s.toList with
  | 'u' :: rest => ((parsePositiveNat? rest).bind IntegerWidth.ofNat?).map .unsigned
  | 'i' :: rest => ((parsePositiveNat? rest).bind IntegerWidth.ofNat?).map .signed
  | _ => none

theorem IntegerType.parse?_sound {s : String} {ty : IntegerType}
    (_h : IntegerType.parse? s = some ty) :
    0 < ty.bits ∧ ty.bits ≤ maxIntegerBits :=
  ⟨ty.bits_pos, ty.bits_le_max⟩

end Aethel
