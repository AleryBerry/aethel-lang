import Aethel.Machine
import Aethel.ResourceFrame
import Aethel.LayoutAccess
import Aethel.LayoutPaths

namespace Aethel.CategoricalLNL

open Aethel Aethel.Core Aethel.AutomaticLayout

/-!
## Part A: Benton's Mixed Linear/Non-Linear (LNL) Type System

Pure copyable values inhabit the Cartesian closed category `C` (`isCopyable = true`).
Affine handles, active views, tensors, and once-callable closures inhabit the symmetric
monoidal category `L` (`isCopyable = false`), linked via `AllCopyable` promotion (`lam`).
-/

inductive LNLType where
  | unit : LNLType
  | bool : LNLType
  | byte : LNLType
  | cprod (a b : LNLType) : LNLType
  | arrow (dom cod : LNLType) : LNLType
  | handle : LNLType
  | view (mode : AccessMode) : LNLType
  | tensor (a b : LNLType) : LNLType
  | onceArrow (dom cod : LNLType) : LNLType
  deriving DecidableEq, Repr

def LNLType.isCopyable : LNLType → Bool
  | .unit | .bool | .byte | .arrow _ _ => true
  | .cprod a b => a.isCopyable && b.isCopyable
  | .handle | .view _ | .tensor _ _ | .onceArrow _ _ => false

abbrev LNLCtx := List (Nat × LNLType)

def AllCopyable (Γ : LNLCtx) : Prop :=
  ∀ p ∈ Γ, p.2.isCopyable = true

/-- Monoidal resource-splitting judgment: copyable bindings may enter both
branches (`both`); affine bindings may enter at most one branch (`left`, `right`,
or unused `drop`). -/
inductive CtxSplit : LNLCtx → LNLCtx → LNLCtx → Prop where
  | nil : CtxSplit [] [] []
  | both {x : Nat} {τ : LNLType} {Γ Γ₁ Γ₂ : LNLCtx}
      (hCopy : τ.isCopyable = true) :
      CtxSplit Γ Γ₁ Γ₂ → CtxSplit ((x, τ) :: Γ) ((x, τ) :: Γ₁) ((x, τ) :: Γ₂)
  | left {x : Nat} {τ : LNLType} {Γ Γ₁ Γ₂ : LNLCtx} :
      CtxSplit Γ Γ₁ Γ₂ → CtxSplit ((x, τ) :: Γ) ((x, τ) :: Γ₁) Γ₂
  | right {x : Nat} {τ : LNLType} {Γ Γ₁ Γ₂ : LNLCtx} :
      CtxSplit Γ Γ₁ Γ₂ → CtxSplit ((x, τ) :: Γ) Γ₁ ((x, τ) :: Γ₂)
  | drop {x : Nat} {τ : LNLType} {Γ Γ₁ Γ₂ : LNLCtx} :
      CtxSplit Γ Γ₁ Γ₂ → CtxSplit ((x, τ) :: Γ) Γ₁ Γ₂

inductive LNLExpr where
  | unit : LNLExpr
  | bool (b : Bool) : LNLExpr
  | byte (v : UInt8) : LNLExpr
  | var (id : Nat) : LNLExpr
  | cpair (a b : LNLExpr) : LNLExpr
  | tp (a b : LNLExpr) : LNLExpr
  | lam (p : Nat) (ty : LNLType) (body : LNLExpr) : LNLExpr
  | onceLam (p : Nat) (ty : LNLType) (body : LNLExpr) : LNLExpr
  | app (fn arg : LNLExpr) : LNLExpr
  | appOnce (fn arg : LNLExpr) : LNLExpr
  | letBind (id : Nat) (v body : LNLExpr) : LNLExpr
  deriving Repr, DecidableEq

inductive LNLWellTyped : LNLCtx → LNLExpr → LNLType → Prop where
  | unit (Γ : LNLCtx) : LNLWellTyped Γ .unit .unit
  | bool (Γ : LNLCtx) (b : Bool) : LNLWellTyped Γ (.bool b) .bool
  | byte (Γ : LNLCtx) (v : UInt8) : LNLWellTyped Γ (.byte v) .byte
  | var {Γ : LNLCtx} (x : Nat) (τ : LNLType) :
      (x, τ) ∈ Γ → LNLWellTyped Γ (.var x) τ
  | cpair {Γ Γ₁ Γ₂ : LNLCtx} {a b : LNLExpr} {tyA tyB : LNLType} :
      CtxSplit Γ Γ₁ Γ₂ →
      tyA.isCopyable = true → tyB.isCopyable = true →
      LNLWellTyped Γ₁ a tyA → LNLWellTyped Γ₂ b tyB →
      LNLWellTyped Γ (.cpair a b) (.cprod tyA tyB)
  | tp {Γ Γ₁ Γ₂ : LNLCtx} {a b : LNLExpr} {tyA tyB : LNLType} :
      CtxSplit Γ Γ₁ Γ₂ →
      LNLWellTyped Γ₁ a tyA → LNLWellTyped Γ₂ b tyB →
      LNLWellTyped Γ (.tp a b) (.tensor tyA tyB)
  | lam {Γ : LNLCtx} (p : Nat) (tyP : LNLType) {body : LNLExpr} {tyBody : LNLType} :
      AllCopyable Γ →
      LNLWellTyped ((p, tyP) :: Γ) body tyBody →
      LNLWellTyped Γ (.lam p tyP body) (.arrow tyP tyBody)
  | onceLam {Γ : LNLCtx} (p : Nat) (tyP : LNLType) {body : LNLExpr} {tyBody : LNLType} :
      LNLWellTyped ((p, tyP) :: Γ) body tyBody →
      LNLWellTyped Γ (.onceLam p tyP body) (.onceArrow tyP tyBody)
  | app {Γ Γ₁ Γ₂ : LNLCtx} {fn arg : LNLExpr} {dom cod : LNLType} :
      CtxSplit Γ Γ₁ Γ₂ →
      LNLWellTyped Γ₁ fn (.arrow dom cod) → LNLWellTyped Γ₂ arg dom →
      LNLWellTyped Γ (.app fn arg) cod
  | appOnce {Γ Γ₁ Γ₂ : LNLCtx} {fn arg : LNLExpr} {dom cod : LNLType} :
      CtxSplit Γ Γ₁ Γ₂ →
      LNLWellTyped Γ₁ fn (.onceArrow dom cod) → LNLWellTyped Γ₂ arg dom →
      LNLWellTyped Γ (.appOnce fn arg) cod
  | letBind {Γ Γ₁ Γ₂ : LNLCtx} (id : Nat) {v body : LNLExpr} {tyV tyBody : LNLType} :
      CtxSplit Γ Γ₁ Γ₂ →
      LNLWellTyped Γ₁ v tyV →
      LNLWellTyped ((id, tyV) :: Γ₂) body tyBody →
      LNLWellTyped Γ (.letBind id v body) tyBody

theorem CtxSplit.symm {Γ Γ₁ Γ₂ : LNLCtx} (h : CtxSplit Γ Γ₁ Γ₂) :
    CtxSplit Γ Γ₂ Γ₁ := by
  induction h with
  | nil => exact .nil
  | both hCopy _ ih => exact .both hCopy ih
  | left _ ih => exact .right ih
  | right _ ih => exact .left ih
  | drop _ ih => exact .drop ih

theorem CtxSplit.assoc {Γ Γ₁₂ Γ₃ Γ₁ Γ₂ : LNLCtx}
    (h1 : CtxSplit Γ Γ₁₂ Γ₃) (h2 : CtxSplit Γ₁₂ Γ₁ Γ₂) :
    ∃ Γ₂₃, CtxSplit Γ Γ₁ Γ₂₃ ∧ CtxSplit Γ₂₃ Γ₂ Γ₃ := by
  induction h1 generalizing Γ₁ Γ₂ with
  | nil =>
    cases h2
    exact ⟨[], .nil, .nil⟩
  | drop _ ih =>
    obtain ⟨Γ₂₃, hs1, hs2⟩ := ih h2
    exact ⟨Γ₂₃, .drop hs1, hs2⟩
  | right _ ih =>
    obtain ⟨Γ₂₃, hs1, hs2⟩ := ih h2
    exact ⟨_ :: Γ₂₃, .right hs1, .right hs2⟩
  | left _ ih =>
    cases h2 with
    | both hCopy h2' =>
      obtain ⟨Γ₂₃, hs1, hs2⟩ := ih h2'
      exact ⟨_ :: Γ₂₃, .both hCopy hs1, .left hs2⟩
    | left h2' =>
      obtain ⟨Γ₂₃, hs1, hs2⟩ := ih h2'
      exact ⟨Γ₂₃, .left hs1, hs2⟩
    | right h2' =>
      obtain ⟨Γ₂₃, hs1, hs2⟩ := ih h2'
      exact ⟨_ :: Γ₂₃, .right hs1, .left hs2⟩
    | drop h2' =>
      obtain ⟨Γ₂₃, hs1, hs2⟩ := ih h2'
      exact ⟨Γ₂₃, .drop hs1, hs2⟩
  | both hCopy _ ih =>
    cases h2 with
    | both _ h2' =>
      obtain ⟨Γ₂₃, hs1, hs2⟩ := ih h2'
      exact ⟨_ :: Γ₂₃, .both hCopy hs1, .both hCopy hs2⟩
    | left h2' =>
      obtain ⟨Γ₂₃, hs1, hs2⟩ := ih h2'
      exact ⟨_ :: Γ₂₃, .both hCopy hs1, .right hs2⟩
    | right h2' =>
      obtain ⟨Γ₂₃, hs1, hs2⟩ := ih h2'
      exact ⟨_ :: Γ₂₃, .right hs1, .both hCopy hs2⟩
    | drop h2' =>
      obtain ⟨Γ₂₃, hs1, hs2⟩ := ih h2'
      exact ⟨_ :: Γ₂₃, .right hs1, .right hs2⟩

theorem CtxSplit.cartesian_dup {Γ : LNLCtx} (hAll : AllCopyable Γ) :
    CtxSplit Γ Γ Γ := by
  induction Γ with
  | nil => exact .nil
  | cons p rest ih =>
    have hHead : p.2.isCopyable = true := hAll p List.mem_cons_self
    have hTail : AllCopyable rest := fun q hq => hAll q (List.mem_cons_of_mem _ hq)
    exact .both hHead (ih hTail)

theorem CtxSplit.mem_left {Γ Γ₁ Γ₂ : LNLCtx} (h : CtxSplit Γ Γ₁ Γ₂)
    {p : Nat × LNLType} (hp : p ∈ Γ₁) : p ∈ Γ := by
  induction h with
  | nil => cases hp
  | both _ _ ih | left _ ih =>
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hp')
  | right _ ih | drop _ ih =>
    exact List.mem_cons_of_mem _ (ih hp)

theorem CtxSplit.mem_right {Γ Γ₁ Γ₂ : LNLCtx} (h : CtxSplit Γ Γ₁ Γ₂)
    {p : Nat × LNLType} (hp : p ∈ Γ₂) : p ∈ Γ :=
  h.symm.mem_left hp

theorem CtxSplit.affine_not_both {Γ Γ₁ Γ₂ : LNLCtx} (hNodup : (Γ.map Prod.fst).Nodup)
    (hSplit : CtxSplit Γ Γ₁ Γ₂) {x : Nat} {τ₁ τ₂ : LNLType}
    (h1 : (x, τ₁) ∈ Γ₁) (h2 : (x, τ₂) ∈ Γ₂) (hAff : τ₁.isCopyable = false) :
    False := by
  induction hSplit with
  | nil => cases h1
  | drop _ ih =>
    have hTail : (_root_.List.map Prod.fst _).Nodup := (List.nodup_cons.mp hNodup).2
    exact ih hTail h1 h2
  | left hSub ih =>
    have hSplitNodup := List.nodup_cons.mp hNodup
    rcases List.mem_cons.mp h1 with hHead | hTail1
    · have hEq : x = _ := congrArg Prod.fst hHead
      have hIn := List.mem_map_of_mem (f := Prod.fst) (hSub.mem_right h2)
      rw [hEq] at hIn
      exact hSplitNodup.1 hIn
    · exact ih hSplitNodup.2 hTail1 h2
  | right hSub ih =>
    have hSplitNodup := List.nodup_cons.mp hNodup
    rcases List.mem_cons.mp h2 with hHead | hTail2
    · have hEq : x = _ := congrArg Prod.fst hHead
      have hIn := List.mem_map_of_mem (f := Prod.fst) (hSub.mem_left h1)
      rw [hEq] at hIn
      exact hSplitNodup.1 hIn
    · exact ih hSplitNodup.2 h1 hTail2
  | both hCopy hSub ih =>
    have hSplitNodup := List.nodup_cons.mp hNodup
    rcases List.mem_cons.mp h1 with hHead1 | hTail1
    · have hTyEq : τ₁ = _ := congrArg Prod.snd hHead1
      rw [hTyEq, hCopy] at hAff
      contradiction
    · rcases List.mem_cons.mp h2 with hHead2 | hTail2
      · have hEq : x = _ := congrArg Prod.fst hHead2
        have hIn := List.mem_map_of_mem (f := Prod.fst) (hSub.mem_left hTail1)
        rw [hEq] at hIn
        exact hSplitNodup.1 hIn
      · exact ih hSplitNodup.2 hTail1 hTail2

theorem copyable_pair_dup_accepted :
    LNLWellTyped [(0, .byte)] (.cpair (.var 0) (.var 0)) (.cprod .byte .byte) :=
  .cpair (.both rfl .nil) rfl rfl (.var 0 .byte List.mem_cons_self) (.var 0 .byte List.mem_cons_self)

theorem affine_handle_dup_rejected :
    ¬ LNLWellTyped [(0, .handle)] (.tp (.var 0) (.var 0)) (.tensor .handle .handle) := by
  intro hT
  cases hT with
  | tp hSplit hA hB =>
    cases hA with | var _ _ hIn1 =>
    cases hB with | var _ _ hIn2 =>
    exact CtxSplit.affine_not_both (by decide) hSplit hIn1 hIn2 rfl

theorem reusable_lam_cannot_capture_handle :
    ¬ LNLWellTyped [(0, .handle)] (.lam 1 .unit (.var 0)) (.arrow .unit .handle) := by
  intro hT
  cases hT with
  | lam _ _ hAll _ =>
    have hCopy := hAll (0, .handle) List.mem_cons_self
    cases hCopy

theorem onceClosure_captures_handle_accepted :
    LNLWellTyped [(0, .handle)] (.onceLam 1 .unit (.var 0)) (.onceArrow .unit .handle) :=
  .onceLam 1 .unit (.var 0 .handle (List.mem_cons_of_mem _ List.mem_cons_self))

theorem onceClosure_double_call_rejected :
    ¬ LNLWellTyped [(0, .onceArrow .unit .unit)]
        (.tp (.appOnce (.var 0) .unit) (.appOnce (.var 0) .unit)) (.tensor .unit .unit) := by
  intro hT
  cases hT with
  | tp hSplit hA hB =>
    cases hA with | appOnce hSplitA hFnA _ =>
    cases hFnA with | var _ _ hInA =>
    cases hB with | appOnce hSplitB hFnB _ =>
    cases hFnB with | var _ _ hInB =>
    exact CtxSplit.affine_not_both (by decide) hSplit
      (hSplitA.mem_left hInA) (hSplitB.mem_left hInB) rfl

theorem reusable_lam_cannot_capture_onceClosure :
    ¬ LNLWellTyped [(0, .onceArrow .unit .unit)]
        (.lam 1 .unit (.var 0)) (.arrow .unit (.onceArrow .unit .unit)) := by
  intro hT
  cases hT with
  | lam _ _ hAll _ =>
    have hCopy := hAll (0, .onceArrow .unit .unit) List.mem_cons_self
    cases hCopy

theorem onceClosure_captures_view_accepted :
    LNLWellTyped [(0, .view .exclusive)]
        (.onceLam 1 .unit (.var 0)) (.onceArrow .unit (.view .exclusive)) :=
  .onceLam 1 .unit (.var 0 (.view .exclusive) (List.mem_cons_of_mem _ List.mem_cons_self))

theorem onceClosure_unused_drop_accepted :
    LNLWellTyped [(0, .onceArrow .unit .unit)] .unit .unit :=
  .unit _

/-!
## Part B: Categorical Lens Laws for Mutable Byte Views & Bit-Packed Record Leaves
-/

theorem byteLens_put_get (s : Core.State) (loc : ByteLocation) (old v : UInt8)
    (hLive : s.byte loc = some old) :
    (s.store loc v).byte loc = some v :=
  Core.State.store_byte_written s loc old v hLive

theorem byteLens_get_put (s : Core.State) (loc : ByteLocation) (v : UInt8)
    (hLive : s.byte loc = some v) :
    ∀ loc', (s.store loc v).byte loc' = s.byte loc' := by
  intro loc'
  by_cases hEq : loc = loc'
  · subst hEq
    rw [Core.State.store_byte_written s loc v v hLive, hLive]
  · exact Core.State.store_byte_other s loc loc' v hEq

theorem byteLens_put_put (s : Core.State) (loc : ByteLocation) (old v1 v2 : UInt8)
    (hLive : s.byte loc = some old) :
    ∀ loc', ((s.store loc v1).store loc v2).byte loc' = (s.store loc v2).byte loc' := by
  intro loc'
  by_cases hEq : loc = loc'
  · subst hEq
    have h1 := Core.State.store_byte_written s loc old v1 hLive
    rw [Core.State.store_byte_written (s.store loc v1) loc v1 v2 h1,
      Core.State.store_byte_written s loc old v2 hLive]
  · rw [Core.State.store_byte_other (s.store loc v1) loc loc' v2 hEq,
      Core.State.store_byte_other s loc loc' v1 hEq,
      Core.State.store_byte_other s loc loc' v2 hEq]

private theorem state_store_byte_none (s : Core.State) (p : ByteLocation) (v : UInt8)
    (hNone : s.byte p = none) :
    (s.store p v).byte p = none := by
  simp only [Core.State.byte, Core.State.allocation, Core.State.store,
    List.find?_map, Function.comp_def] at hNone ⊢
  generalize hFind : s.allocations.find? (fun a => a.owner == p.allocation) = found at hNone ⊢
  cases found with
  | none => rfl
  | some alloc =>
    have hOwner : alloc.owner = p.allocation := by simpa using List.find?_some hFind
    simp only [Option.map_some, bind, Option.bind, hOwner, beq_self_eq_true, ↓reduceIte] at hNone ⊢
    have hOut : alloc.bytes.length ≤ p.offset := List.getElem?_eq_none_iff.mp hNone
    exact List.getElem?_eq_none (by simpa [List.length_set] using hOut)

theorem byteLens_disjoint_commute (s : Core.State) (loc1 loc2 : ByteLocation) (v1 v2 : UInt8)
    (hDiff : loc1 ≠ loc2) :
    ∀ loc', ((s.store loc1 v1).store loc2 v2).byte loc' =
      ((s.store loc2 v2).store loc1 v1).byte loc' := by
  intro loc'
  by_cases h1 : loc1 = loc'
  · subst h1
    rw [Core.State.store_byte_other (s.store loc1 v1) loc2 loc1 v2 hDiff.symm]
    cases hL : s.byte loc1 with
    | none =>
      have hL2 : (s.store loc2 v2).byte loc1 = none := by
        rw [Core.State.store_byte_other s loc2 loc1 v2 hDiff.symm]
        exact hL
      rw [state_store_byte_none s loc1 v1 hL, state_store_byte_none (s.store loc2 v2) loc1 v1 hL2]
    | some b1 =>
      have hL2 : (s.store loc2 v2).byte loc1 = some b1 := by
        rw [Core.State.store_byte_other s loc2 loc1 v2 hDiff.symm]
        exact hL
      rw [Core.State.store_byte_written s loc1 b1 v1 hL,
        Core.State.store_byte_written (s.store loc2 v2) loc1 b1 v1 hL2]
  · by_cases h2 : loc2 = loc'
    · subst h2
      rw [Core.State.store_byte_other (s.store loc2 v2) loc1 loc2 v1 hDiff]
      cases hL : s.byte loc2 with
      | none =>
        have hL1 : (s.store loc1 v1).byte loc2 = none := by
          rw [Core.State.store_byte_other s loc1 loc2 v1 hDiff]
          exact hL
        rw [state_store_byte_none (s.store loc1 v1) loc2 v2 hL1,
          state_store_byte_none s loc2 v2 hL]
      | some b2 =>
        have hL1 : (s.store loc1 v1).byte loc2 = some b2 := by
          rw [Core.State.store_byte_other s loc1 loc2 v1 hDiff]
          exact hL
        rw [Core.State.store_byte_written (s.store loc1 v1) loc2 b2 v2 hL1,
          Core.State.store_byte_written s loc2 b2 v2 hL]
    · rw [Core.State.store_byte_other (s.store loc1 v1) loc2 loc' v2 h2,
        Core.State.store_byte_other s loc1 loc' v1 h1,
        Core.State.store_byte_other (s.store loc2 v2) loc1 loc' v1 h1,
        Core.State.store_byte_other s loc2 loc' v2 h2]

theorem image_ext_bits {size : Nat} {img1 img2 : Image size}
    (hBits : ∀ idx, idx < size * 8 → img1.bit idx = img2.bit idx) :
    img1 = img2 := by
  funext byte
  apply BitVec.eq_of_getLsbD_eq
  intro bit hBit
  have hIdxLt : byte.val * 8 + bit < size * 8 := by omega
  have hEq := hBits (byte.val * 8 + bit) hIdxLt
  have hDiv : (byte.val * 8 + bit) / 8 = byte.val := by
    rw [Nat.mul_comm byte.val 8, Nat.mul_add_div (by decide), Nat.div_eq_of_lt hBit, Nat.add_zero]
  have hMod : (byte.val * 8 + bit) % 8 = bit := by
    rw [Nat.mul_comm byte.val 8, Nat.mul_add_mod, Nat.mod_eq_of_lt hBit]
  have hIn : (byte.val * 8 + bit) / 8 < size := by rw [hDiv]; exact byte.isLt
  simp only [Image.bit, dite_eq_left hIn] at hEq
  have hFin : (⟨(byte.val * 8 + bit) / 8, hIn⟩ : Fin size) = byte := Fin.ext hDiv
  rw [hFin, hMod] at hEq
  exact hEq

theorem recordLeafLens_put_get {size : Nat} (field : IntegerField size) (img : Image size)
    (v : BitVec field.kind.bits) :
    field.get (field.set img v) = v :=
  field.get_set img v

theorem recordLeafLens_get_put {size : Nat} (field : IntegerField size) (img : Image size) :
    field.set img (field.get img) = img := by
  apply image_ext_bits
  intro idx hIdx
  dsimp [IntegerField.set, IntegerField.get]
  rw [Image.bit_write _ _ _ idx hIdx]
  split
  · rename_i hRange
    rw [Image.readBits_getLsbD img field.offset field.kind.bits (by omega),
      Nat.add_sub_cancel' hRange.1]
  · rfl

theorem recordLeafLens_put_put {size : Nat} (field : IntegerField size) (img : Image size)
    (v1 v2 : BitVec field.kind.bits) :
    field.set (field.set img v1) v2 = field.set img v2 := by
  apply image_ext_bits
  intro idx hIdx
  dsimp [IntegerField.set]
  rw [Image.bit_write _ _ _ idx hIdx, Image.bit_write _ _ _ idx hIdx,
    Image.bit_write _ _ _ idx hIdx]
  split
  · rfl
  · rfl

theorem recordLeafLens_disjoint_commute {abi : TargetIntegerABI} {schema : Schema}
    {layout : Layout} (planned : Conforms abi schema layout)
    {p1 p2 : List Nat} {f1 f2 : IntegerField layout.size}
    (h1 : resolveInteger planned p1 = some f1)
    (h2 : resolveInteger planned p2 = some f2)
    (hDiff : p1 ≠ p2)
    (img : Image layout.size) (v1 : BitVec f1.kind.bits) (v2 : BitVec f2.kind.bits) :
    f2.set (f1.set img v1) v2 = f1.set (f2.set img v2) v1 := by
  have hSep := leaf_paths_separate planned h1 h2 hDiff
  apply image_ext_bits
  intro idx hIdx
  dsimp [IntegerField.set]
  rw [Image.bit_write _ _ _ idx hIdx, Image.bit_write _ _ _ idx hIdx,
    Image.bit_write _ _ _ idx hIdx, Image.bit_write _ _ _ idx hIdx]
  by_cases hIn1 : f1.offset ≤ idx ∧ idx < f1.offset + f1.kind.bits <;>
    by_cases hIn2 : f2.offset ≤ idx ∧ idx < f2.offset + f2.kind.bits
  · omega
  · simp [hIn1, hIn2]
  · simp [hIn1, hIn2]
  · simp [hIn1, hIn2]

end Aethel.CategoricalLNL
