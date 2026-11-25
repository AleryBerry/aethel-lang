import Aethel.RustFFI

namespace Aethel.CargoInterop

open Aethel Aethel.Core Aethel.RustFFI

/-!
## Cargo Crate Manifests, Borrowed UTF-8 `&str`, & Stateless Aethel → Rust Callbacks (Stage H)

Establishes the three formal contracts required for Cargo-backed Rust interoperability:
1. Borrowed UTF-8 `String` (`&str`) FFI slice contract layered over `RustSliceValid`
   (`checkRustStr_correct`, `rust_empty_str_valid`, `rustStr_implies_slice_valid`).
2. Stateless/capture-free Aethel → Rust C-ABI function callback contract
   (`checkStatelessCallback_correct`, `stateless_callback_retention_safe`,
    `capturing_callback_rejected`), allowing long-lived Rust schedules (such as Bevy `App`)
   to invoke pure Aethel callbacks without dangling stack/view captures.
3. Cargo manifest (`aethel.toml`) dependency and `@external(rust, crate, sym)` target
   declaration soundness (`checkCargoDep_correct`, `checkManifestValid_correct`,
   `checkCrateTargetDeclared_correct`, `verifyProjectModuloCargoContracts`,
   `undeclared_cargo_crate_rejected`).
-/

/-! ## 1. Borrowed UTF-8 `&str` FFI Contract -/

private def isContByte (b : UInt8) : Bool :=
  0x80 ≤ b && b ≤ 0xBF

/-- Structural byte-level UTF-8 validator matching Rust `core::str::from_utf8`
(rejecting overlong encodings, UTF-16 surrogates U+D800..U+DFFF, and codepoints > U+10FFFF). -/
def isValidUtf8Bytes : List UInt8 → Bool
  | [] => true
  | b0 :: rest =>
    if b0 < 0x80 then
      isValidUtf8Bytes rest
    else if 0xC2 ≤ b0 && b0 ≤ 0xDF then
      match rest with
      | b1 :: rest' => isContByte b1 && isValidUtf8Bytes rest'
      | [] => false
    else if b0 == 0xE0 then
      match rest with
      | b1 :: b2 :: rest' =>
        (0xA0 ≤ b1 && b1 ≤ 0xBF) && isContByte b2 && isValidUtf8Bytes rest'
      | _ => false
    else if (0xE1 ≤ b0 && b0 ≤ 0xEC) || (0xEE ≤ b0 && b0 ≤ 0xEF) then
      match rest with
      | b1 :: b2 :: rest' =>
        isContByte b1 && isContByte b2 && isValidUtf8Bytes rest'
      | _ => false
    else if b0 == 0xED then
      match rest with
      | b1 :: b2 :: rest' =>
        (0x80 ≤ b1 && b1 ≤ 0x9F) && isContByte b2 && isValidUtf8Bytes rest'
      | _ => false
    else if b0 == 0xF0 then
      match rest with
      | b1 :: b2 :: b3 :: rest' =>
        (0x90 ≤ b1 && b1 ≤ 0xBF) && isContByte b2 && isContByte b3 && isValidUtf8Bytes rest'
      | _ => false
    else if 0xF1 ≤ b0 && b0 ≤ 0xF3 then
      match rest with
      | b1 :: b2 :: b3 :: rest' =>
        isContByte b1 && isContByte b2 && isContByte b3 && isValidUtf8Bytes rest'
      | _ => false
    else if b0 == 0xF4 then
      match rest with
      | b1 :: b2 :: b3 :: rest' =>
        (0x80 ≤ b1 && b1 ≤ 0x8F) && isContByte b2 && isContByte b3 && isValidUtf8Bytes rest'
      | _ => false
    else
      false

structure RustStrSpec where
  slice : RustSliceSpec
  bytes : List UInt8
  deriving Repr, DecidableEq

def checkRustStr (s : Core.State) (rs : RustStrSpec) : Bool :=
  decide (rs.slice.mode = .shared) &&
  decide (rs.slice.elemSize = 1) &&
  decide (rs.slice.elemAlign = 1) &&
  !rs.slice.isSubBytePacked &&
  checkRustSlice s rs.slice &&
  decide (rs.bytes.length = rs.slice.len) &&
  isValidUtf8Bytes rs.bytes

def RustStrValid (s : Core.State) (rs : RustStrSpec) : Prop :=
  rs.slice.mode = .shared ∧
  rs.slice.elemSize = 1 ∧
  rs.slice.elemAlign = 1 ∧
  rs.slice.isSubBytePacked = false ∧
  RustSliceValid s rs.slice ∧
  rs.bytes.length = rs.slice.len ∧
  isValidUtf8Bytes rs.bytes = true

theorem checkRustStr_correct (s : Core.State) (rs : RustStrSpec) :
    checkRustStr s rs = true ↔ RustStrValid s rs := by
  simp only [checkRustStr, RustStrValid, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, checkRustSlice_correct, and_assoc]

theorem rustStr_implies_slice_valid {s : Core.State} {rs : RustStrSpec}
    (h : RustStrValid s rs) : RustSliceValid s rs.slice :=
  h.2.2.2.2.1

theorem rust_empty_str_valid (s : Core.State) (owner : OwnerId) (offset : Nat) :
    RustStrValid s ⟨⟨owner, offset, 0, 1, 1, .shared, false⟩, []⟩ := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
  exact rust_empty_slice_valid s owner offset 1 1 .shared Nat.zero_lt_one (by decide)
    (Nat.mod_one offset) (Nat.mod_one 1)

theorem invalid_utf8_str_rejected (s : Core.State) (owner : OwnerId) :
    checkRustStr s ⟨⟨owner, 0, 1, 1, 1, .shared, false⟩, [0xFF]⟩ = false := by
  simp [checkRustStr, isValidUtf8Bytes]

theorem mut_aliased_str_rejected (s : Core.State) (owner : OwnerId) :
    checkRustStr s ⟨⟨owner, 0, 0, 1, 1, .exclusive, false⟩, []⟩ = false := by
  simp [checkRustStr]

/-! ## 2. Stateless Aethel → Rust C-ABI Function Callback Contract -/

inductive CallbackScalarTy where
  | bool
  | i8 | i16 | i32 | i64
  | u8 | u16 | u32 | u64
  | f32 | f64
  | opaquePtr
  deriving Repr, DecidableEq

inductive CallbackArgABI where
  | scalar (ty : CallbackScalarTy)
  | borrowedStr
  | flatRecord (size align : Nat)
  deriving Repr, DecidableEq

inductive CallbackRetABI where
  | unit
  | scalar (ty : CallbackScalarTy)
  | flatRecord (size align : Nat)
  deriving Repr, DecidableEq

def checkCallbackArgABI : CallbackArgABI → Bool
  | .scalar _ => true
  | .borrowedStr => true
  | .flatRecord size align =>
    decide (0 < align) && align.isPowerOfTwo && decide (size % align = 0)

def checkCallbackRetABI : CallbackRetABI → Bool
  | .unit => true
  | .scalar _ => true
  | .flatRecord size align =>
    decide (0 < align) && align.isPowerOfTwo && decide (size % align = 0)

structure AethelCallbackSpec where
  name : String
  capturesCount : Nat
  isOnce : Bool
  args : List CallbackArgABI
  ret : CallbackRetABI
  deriving Repr, DecidableEq

def StatelessCallbackValid (cb : AethelCallbackSpec) : Prop :=
  cb.capturesCount = 0 ∧
  cb.isOnce = false ∧
  (∀ a ∈ cb.args, checkCallbackArgABI a = true) ∧
  checkCallbackRetABI cb.ret = true

def checkStatelessCallback (cb : AethelCallbackSpec) : Bool :=
  decide (cb.capturesCount = 0) &&
  !cb.isOnce &&
  cb.args.all checkCallbackArgABI &&
  checkCallbackRetABI cb.ret

theorem checkStatelessCallback_correct (cb : AethelCallbackSpec) :
    checkStatelessCallback cb = true ↔ StatelessCallbackValid cb := by
  simp only [checkStatelessCallback, StatelessCallbackValid, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_true_eq, List.all_eq_true, and_assoc]

/-- Retaining a validated stateless C-ABI callback inside a foreign schedule (such as Bevy `App`)
captures zero owner identities (`capturedOwners = []`), so every retained owner invariant holds
vacuously across arbitrary future states. -/
theorem stateless_callback_retention_safe {cb : AethelCallbackSpec}
    (h : StatelessCallbackValid cb)
    (capturedOwners : List OwnerId) (hCap : capturedOwners.length = cb.capturesCount)
    (liveOwners : OwnerId → Prop) :
    capturedOwners = [] ∧ ∀ o ∈ capturedOwners, liveOwners o := by
  rw [h.1] at hCap
  have hNil : capturedOwners = [] := List.length_eq_zero_iff.mp hCap
  subst hNil
  exact ⟨rfl, fun _ hMem => False.elim (List.not_mem_nil hMem)⟩

theorem capturing_callback_rejected :
    checkStatelessCallback ⟨"leaky_sys", 1, false, [.borrowedStr], .unit⟩ = false := by
  decide

theorem fn_once_callback_rejected :
    checkStatelessCallback ⟨"once_sys", 0, true, [], .unit⟩ = false := by
  decide

/-! ## 3. Cargo Manifest & External Crate Declaration Contract -/

def isValidCrateFirstChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z')

def isValidCrateChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '_' || c == '-'

def isValidCrateIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isValidCrateFirstChar c && cs.all isValidCrateChar

structure CargoDepSpec where
  name : String
  hasVersion : Bool
  hasPath : Bool
  defaultFeatures : Bool
  features : List String
  deriving Repr, DecidableEq

def CargoDepValid (d : CargoDepSpec) : Prop :=
  isValidCrateIdent d.name = true ∧ (d.hasVersion = true ∨ d.hasPath = true)

def checkCargoDep (d : CargoDepSpec) : Bool :=
  isValidCrateIdent d.name && (d.hasVersion || d.hasPath)

theorem checkCargoDep_correct (d : CargoDepSpec) :
    checkCargoDep d = true ↔ CargoDepValid d := by
  simp only [checkCargoDep, CargoDepValid, Bool.and_eq_true, Bool.or_eq_true]

def noDuplicateCrateNames : List CargoDepSpec → Bool
  | [] => true
  | d :: ds => !(ds.any fun other => other.name == d.name) && noDuplicateCrateNames ds

structure ProjectManifestSpec where
  pkgName : String
  entry : String
  rustDeps : List CargoDepSpec
  deriving Repr, DecidableEq

def ProjectManifestValid (m : ProjectManifestSpec) : Prop :=
  isValidCrateIdent m.pkgName = true ∧
  m.entry ≠ "" ∧
  (∀ d ∈ m.rustDeps, CargoDepValid d) ∧
  noDuplicateCrateNames m.rustDeps = true

def checkManifestValid (m : ProjectManifestSpec) : Bool :=
  isValidCrateIdent m.pkgName &&
  decide (m.entry ≠ "") &&
  m.rustDeps.all checkCargoDep &&
  noDuplicateCrateNames m.rustDeps

theorem checkManifestValid_correct (m : ProjectManifestSpec) :
    checkManifestValid m = true ↔ ProjectManifestValid m := by
  simp only [checkManifestValid, ProjectManifestValid, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, checkCargoDep_correct, and_assoc]

def CrateTargetDeclared (m : ProjectManifestSpec) (target : String) : Prop :=
  target = "self" ∨ target = "bridge" ∨ target = m.pkgName ∨
  ∃ d ∈ m.rustDeps, d.name = target

def checkCrateTargetDeclared (m : ProjectManifestSpec) (target : String) : Bool :=
  decide (target = "self") ||
  decide (target = "bridge") ||
  decide (target = m.pkgName) ||
  m.rustDeps.any (fun d => d.name == target)

theorem checkCrateTargetDeclared_correct (m : ProjectManifestSpec) (target : String) :
    checkCrateTargetDeclared m target = true ↔ CrateTargetDeclared m target := by
  simp only [checkCrateTargetDeclared, CrateTargetDeclared, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true, beq_iff_eq, or_assoc]

/-- Whole-project Cargo verification boundary: all Cargo crate metadata, target declarations,
and Aethel → Rust callbacks validate cleanly without assuming unverified Rust internals. -/
theorem verifyProjectModuloCargoContracts
    (m : ProjectManifestSpec)
    (targets : List String)
    (callbacks : List AethelCallbackSpec)
    (hMan : checkManifestValid m = true)
    (hTargets : ∀ t ∈ targets, checkCrateTargetDeclared m t = true)
    (hCbs : ∀ cb ∈ callbacks, checkStatelessCallback cb = true) :
    ProjectManifestValid m ∧
    (∀ t ∈ targets, CrateTargetDeclared m t) ∧
    (∀ cb ∈ callbacks, StatelessCallbackValid cb) := by
  refine ⟨(checkManifestValid_correct m).mp hMan, ?_, ?_⟩
  · intro t ht
    exact (checkCrateTargetDeclared_correct m t).mp (hTargets t ht)
  · intro cb hcb
    exact (checkStatelessCallback_correct cb).mp (hCbs cb hcb)

theorem undeclared_cargo_crate_rejected :
    checkCrateTargetDeclared ⟨"my_app", "src/main.aethel", []⟩ "bevy" = false := by
  decide

end Aethel.CargoInterop
