import Aethel.RustComplexABI
import Aethel.CargoInterop

namespace Aethel.ProcMacroInterop

open Aethel Aethel.Core Aethel.RustFFI Aethel.RustComplexABI Aethel.CargoInterop

/-!
## Proc-Macro Interop, Zero-Padding `bytemuck::Pod`, & Extended Callbacks (Stage I)

Formalizes the Lean soundness contract for bridging Rust proc-macro attributes and
large multi-threaded Rust libraries (`bevy`, `serde`, `serde_json`, `bytemuck`,
`rayon`, `tokio`, `regex`):
1. Additive `#[derive(...)]` and allowlisted inert helper attributes (`serde`,
   `component`, `bytemuck`, `reflect`, `bincode`) preserve `@layout(flat)`
   `RecordLayout` identically, while layout-altering attribute proc-macros and
   `#[repr(...)]` overrides are statically rejected
   (`checkMacroAttachment_correct`, `derive_attachments_preserve_flat_layout`).
2. `bytemuck::Pod` / zero-padding byte-cast verification proves that a `@layout(flat)`
   record has zero implicit padding bytes (`sumFieldSizes = (planFlatStruct).size`),
   non-empty fields, and no `bool`/non-bit-pattern types (`checkPodRecord_correct`,
   `padded_struct_pod_rejected`, `bool_field_pod_rejected`).
3. Proc-macro crate paths in `@derive(rust, "crate::Trait")` require declared
   Cargo dependencies in `aethel.toml` (`checkDeriveCrateDeps_correct`,
   `undeclared_derive_crate_rejected`).
4. Extended stateless callbacks accept borrowed `View(FlatRec, ...)` and `[T]`/`[mut T]`
   slice parameters with zero retained owner captures (`checkExtendedCallback_correct`,
   `extended_callback_retention_safe`).
-/

/-! ## 1. Additive `#[derive(...)]` & Inert Helper Attribute Preservation -/

inductive RustMacroAttachment where
  | deriveTrait (crateOpt : Option String) (traitPath : String)
  | inertHelperAttr (attrNs : String) (payload : String)
  | rewritingAttrMacro (name : String)
  deriving Repr, DecidableEq

def isAllowedHelperNamespace (ns : String) : Bool :=
  ns == "serde" || ns == "component" || ns == "bytemuck" || ns == "reflect" || ns == "bincode"

def checkMacroAttachment : RustMacroAttachment → Bool
  | .deriveTrait _ traitPath => traitPath != ""
  | .inertHelperAttr ns _ => isAllowedHelperNamespace ns
  | .rewritingAttrMacro _ => false

def MacroAttachmentSafe : RustMacroAttachment → Prop
  | .deriveTrait _ traitPath => traitPath ≠ ""
  | .inertHelperAttr ns _ => isAllowedHelperNamespace ns = true
  | .rewritingAttrMacro _ => False

theorem checkMacroAttachment_correct (att : RustMacroAttachment) :
    checkMacroAttachment att = true ↔ MacroAttachmentSafe att := by
  cases att with
  | deriveTrait crateOpt traitPath =>
    simp [checkMacroAttachment, MacroAttachmentSafe]
  | inertHelperAttr ns payload =>
    simp [checkMacroAttachment, MacroAttachmentSafe]
  | rewritingAttrMacro name =>
    simp [checkMacroAttachment, MacroAttachmentSafe]

def applyMacroToLayout (lay : RecordLayout) : RustMacroAttachment → Option RecordLayout
  | .deriveTrait _ traitPath => if traitPath != "" then some lay else none
  | .inertHelperAttr ns _ => if isAllowedHelperNamespace ns then some lay else none
  | .rewritingAttrMacro _ => none

def applyMacrosToLayout (lay : RecordLayout) : List RustMacroAttachment → Option RecordLayout
  | [] => some lay
  | a :: rest =>
    match applyMacroToLayout lay a with
    | some nextLay => applyMacrosToLayout nextLay rest
    | none => none

private theorem applyMacroToLayout_eq_some {lay : RecordLayout} {a : RustMacroAttachment}
    (h : checkMacroAttachment a = true) :
    applyMacroToLayout lay a = some lay := by
  cases a with
  | deriveTrait crateOpt traitPath =>
    simp only [checkMacroAttachment, bne_iff_ne, ne_eq] at h
    simp [applyMacroToLayout, h]
  | inertHelperAttr ns payload =>
    simp only [checkMacroAttachment] at h
    simp [applyMacroToLayout, h]
  | rewritingAttrMacro name =>
    simp [checkMacroAttachment] at h

private theorem applyMacrosToLayout_preserves (lay : RecordLayout) (atts : List RustMacroAttachment)
    (hSafe : ∀ a ∈ atts, checkMacroAttachment a = true) :
    applyMacrosToLayout lay atts = some lay := by
  induction atts generalizing lay with
  | nil => rfl
  | cons a rest ih =>
    have ha : checkMacroAttachment a = true := hSafe a List.mem_cons_self
    have hRest : ∀ b ∈ rest, checkMacroAttachment b = true := fun b hb =>
      hSafe b (List.mem_cons_of_mem _ hb)
    simp only [applyMacrosToLayout, applyMacroToLayout_eq_some ha]
    exact ih lay hRest

theorem derive_attachments_preserve_flat_layout (fields : List FlatFieldSpec)
    (atts : List RustMacroAttachment)
    (hSafe : ∀ a ∈ atts, checkMacroAttachment a = true) :
    applyMacrosToLayout (planFlatStruct fields) atts = some (planFlatStruct fields) ∧
    (planFlatStruct fields).Valid :=
  ⟨applyMacrosToLayout_preserves (planFlatStruct fields) atts hSafe, planFlatStruct_valid fields⟩

def checkMirroredRecordDerives (isFlatC : Bool) (atts : List RustMacroAttachment) : Bool :=
  isFlatC && atts.all checkMacroAttachment

theorem non_flat_record_derive_rejected (atts : List RustMacroAttachment) :
    checkMirroredRecordDerives false atts = false := by
  simp [checkMirroredRecordDerives]

theorem rewriting_attr_macro_rejected (name : String) :
    checkMacroAttachment (.rewritingAttrMacro name) = false := rfl

theorem repr_override_helper_rejected (payload : String) :
    checkMacroAttachment (.inertHelperAttr "repr" payload) = false := rfl

/-! ## 2. Zero-Padding `bytemuck::Pod` Verification -/

def sumFieldSizes : List FlatFieldSpec → Nat
  | [] => 0
  | f :: rest => f.size + sumFieldSizes rest

def PodRecordValid (fields : List FlatFieldSpec) (allBitPatternValid : Bool) : Prop :=
  fields ≠ [] ∧ allBitPatternValid = true ∧ sumFieldSizes fields = (planFlatStruct fields).size

def checkPodRecord (fields : List FlatFieldSpec) (allBitPatternValid : Bool) : Bool :=
  !fields.isEmpty && allBitPatternValid && decide (sumFieldSizes fields = (planFlatStruct fields).size)

theorem checkPodRecord_correct (fields : List FlatFieldSpec) (allBitPatternValid : Bool) :
    checkPodRecord fields allBitPatternValid = true ↔ PodRecordValid fields allBitPatternValid := by
  cases fields with
  | nil =>
    simp [checkPodRecord, PodRecordValid]
  | cons f rest =>
    simp only [checkPodRecord, PodRecordValid, List.isEmpty_cons, Bool.not_false,
      Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      true_and]

private def podFieldU8 : FlatFieldSpec :=
  ⟨1, 1, Nat.zero_lt_one, Nat.zero_lt_one, ⟨0, rfl⟩, rfl⟩

private def podFieldU32 : FlatFieldSpec :=
  ⟨4, 4, by decide, by decide, ⟨2, rfl⟩, rfl⟩

theorem padded_struct_pod_rejected :
    checkPodRecord [podFieldU8, podFieldU32] true = false := by
  decide

theorem bool_field_pod_rejected (fields : List FlatFieldSpec) :
    checkPodRecord fields false = false := by
  simp [checkPodRecord]

/-! ## 3. Proc-Macro Crate Dependency Soundness -/

def isStdMacroRoot (c : String) : Bool :=
  c == "core" || c == "std" || c == "alloc"

def checkAttachmentCrateDeclared (m : ProjectManifestSpec) : RustMacroAttachment → Bool
  | .deriveTrait none traitPath => traitPath != ""
  | .deriveTrait (some c) traitPath =>
    traitPath != "" && (isStdMacroRoot c || checkCrateTargetDeclared m c)
  | .inertHelperAttr ns _ => isAllowedHelperNamespace ns
  | .rewritingAttrMacro _ => false

def DeriveCrateDepsValid (m : ProjectManifestSpec) (att : RustMacroAttachment) : Prop :=
  match att with
  | .deriveTrait none traitPath => traitPath ≠ ""
  | .deriveTrait (some c) traitPath =>
    traitPath ≠ "" ∧ (isStdMacroRoot c = true ∨ CrateTargetDeclared m c)
  | .inertHelperAttr ns _ => isAllowedHelperNamespace ns = true
  | .rewritingAttrMacro _ => False

theorem checkDeriveCrateDeps_correct (m : ProjectManifestSpec) (att : RustMacroAttachment) :
    checkAttachmentCrateDeclared m att = true ↔ DeriveCrateDepsValid m att := by
  cases att with
  | deriveTrait crateOpt traitPath =>
    cases crateOpt with
    | none => simp [checkAttachmentCrateDeclared, DeriveCrateDepsValid]
    | some c =>
      simp [checkAttachmentCrateDeclared, DeriveCrateDepsValid, checkCrateTargetDeclared_correct]
  | inertHelperAttr ns payload =>
    simp [checkAttachmentCrateDeclared, DeriveCrateDepsValid]
  | rewritingAttrMacro name =>
    simp [checkAttachmentCrateDeclared, DeriveCrateDepsValid]

theorem undeclared_derive_crate_rejected :
    checkAttachmentCrateDeclared ⟨"my_app", "src/main.aethel", []⟩
      (.deriveTrait (some "serde") "Serialize") = false := by
  decide

/-! ## 4. Extended Stateless Callback Borrowed View & Slice Contract -/

inductive ExtendedCallbackArgABI where
  | base (a : CallbackArgABI)
  | borrowedFlatView (mode : AccessMode) (size align : Nat)
  | borrowedSlice (mode : AccessMode) (elemSize elemAlign : Nat)
  deriving Repr, DecidableEq

def checkExtendedCallbackArg : ExtendedCallbackArgABI → Bool
  | .base a => checkCallbackArgABI a
  | .borrowedFlatView _ size align =>
    decide (0 < align) && align.isPowerOfTwo && decide (size % align = 0)
  | .borrowedSlice _ elemSize elemAlign =>
    decide (0 < elemAlign) && elemAlign.isPowerOfTwo && decide (elemSize % elemAlign = 0)

structure ExtendedCallbackSpec where
  name : String
  capturesCount : Nat
  isOnce : Bool
  args : List ExtendedCallbackArgABI
  ret : CallbackRetABI
  deriving Repr, DecidableEq

def ExtendedCallbackValid (cb : ExtendedCallbackSpec) : Prop :=
  cb.capturesCount = 0 ∧
  cb.isOnce = false ∧
  (∀ a ∈ cb.args, checkExtendedCallbackArg a = true) ∧
  checkCallbackRetABI cb.ret = true

def checkExtendedCallback (cb : ExtendedCallbackSpec) : Bool :=
  decide (cb.capturesCount = 0) &&
  !cb.isOnce &&
  cb.args.all checkExtendedCallbackArg &&
  checkCallbackRetABI cb.ret

theorem checkExtendedCallback_correct (cb : ExtendedCallbackSpec) :
    checkExtendedCallback cb = true ↔ ExtendedCallbackValid cb := by
  simp only [checkExtendedCallback, ExtendedCallbackValid, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_true_eq, List.all_eq_true, and_assoc]

theorem extended_callback_retention_safe {cb : ExtendedCallbackSpec}
    (h : ExtendedCallbackValid cb)
    (capturedOwners : List OwnerId) (hCap : capturedOwners.length = cb.capturesCount)
    (liveOwners : OwnerId → Prop) :
    capturedOwners = [] ∧ ∀ o ∈ capturedOwners, liveOwners o := by
  rw [h.1] at hCap
  have hNil : capturedOwners = [] := List.length_eq_zero_iff.mp hCap
  subst hNil
  exact ⟨rfl, fun _ hMem => False.elim (List.not_mem_nil hMem)⟩

end Aethel.ProcMacroInterop
