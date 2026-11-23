import Aethel.Machine
import Aethel.CorePermissions
import Aethel.ResourceFrame

namespace Aethel.Permissions

open Aethel.Core

/-- Four-state permission lattice supporting Tree-Borrows-style lazy two-phase
reservations. A `reserved` mutable borrow tolerates concurrent `shared` and
`frozen` readers until promoted to `activeExclusive` on its first write. -/
inductive BorrowPerm where
  | shared
  | reserved
  | activeExclusive
  | frozen
  deriving Repr, DecidableEq

def BorrowPerm.compatibleBool : BorrowPerm → BorrowPerm → Bool
  | .shared, .shared => true
  | .shared, .frozen => true
  | .shared, .reserved => true
  | .frozen, .shared => true
  | .frozen, .frozen => true
  | .frozen, .reserved => true
  | .reserved, .shared => true
  | .reserved, .frozen => true
  | _, _ => false

def BorrowPerm.Compatible (a b : BorrowPerm) : Prop :=
  a.compatibleBool b = true

instance (a b : BorrowPerm) : Decidable (a.Compatible b) :=
  inferInstanceAs (Decidable (a.compatibleBool b = true))

def BorrowPerm.toAccessMode : BorrowPerm → Core.AccessMode
  | .activeExclusive => .exclusive
  | _ => .shared

theorem BorrowPerm.compatible_symm {a b : BorrowPerm} (h : a.Compatible b) :
    b.Compatible a := by
  cases a <;> cases b <;> simp_all [Compatible, compatibleBool]

theorem BorrowPerm.reserved_compatible_shared :
    BorrowPerm.reserved.Compatible .shared := rfl

theorem BorrowPerm.reserved_compatible_frozen :
    BorrowPerm.reserved.Compatible .frozen := rfl

theorem BorrowPerm.activeExclusive_conflicts_all (b : BorrowPerm) :
    ¬ BorrowPerm.activeExclusive.Compatible b := by
  cases b <;> decide

theorem BorrowPerm.freeze_monotone {a b : BorrowPerm}
    (h : a = .reserved ∨ a = .activeExclusive) (hc : a.Compatible b) :
    BorrowPerm.frozen.Compatible b := by
  rcases h with rfl | rfl <;> cases b <;> simp_all [Compatible, compatibleBool]

structure PermView where
  id : ViewId
  location : ByteLocation
  perm : BorrowPerm
  deriving Repr, DecidableEq

structure PermState where
  base : Core.State
  pviews : List PermView := []
  deriving Repr, DecidableEq

def PermState.view (ps : PermState) (id : ViewId) : Option PermView :=
  ps.pviews.find? fun v => v.id == id

def PermState.CanAdd (ps : PermState) (loc : ByteLocation) (perm : BorrowPerm) : Prop :=
  ∀ v ∈ ps.pviews, v.location ≠ loc ∨ perm.Compatible v.perm

instance (ps : PermState) (loc : ByteLocation) (perm : BorrowPerm) :
    Decidable (ps.CanAdd loc perm) :=
  inferInstanceAs (Decidable (∀ v ∈ ps.pviews, v.location ≠ loc ∨ perm.Compatible v.perm))

def PermState.CanActivate (ps : PermState) (id : ViewId) (loc : ByteLocation) : Prop :=
  ∀ v ∈ ps.pviews, v.id = id ∨ v.location ≠ loc

instance (ps : PermState) (id : ViewId) (loc : ByteLocation) :
    Decidable (ps.CanActivate id loc) :=
  inferInstanceAs (Decidable (∀ v ∈ ps.pviews, v.id = id ∨ v.location ≠ loc))

def PermState.ViewsValid (ps : PermState) : Prop :=
  ps.pviews.Pairwise fun a b => a.id ≠ b.id ∧
    (a.location ≠ b.location ∨ a.perm.Compatible b.perm)

def PermState.Valid (ps : PermState) : Prop :=
  ps.ViewsValid ∧ ∀ v ∈ ps.pviews, (ps.base.byte v.location).isSome = true

theorem PermState.empty_valid : ({ base := {} } : PermState).Valid := by
  refine ⟨List.Pairwise.nil, ?_⟩
  intro v hv
  cases hv

inductive PermInstr where
  | reserve (id : ViewId) (loc : ByteLocation) (perm : BorrowPerm)
  | activate (id : ViewId)
  | freeze (id : ViewId)
  | read (id : ViewId)
  | write (id : ViewId) (val : UInt8)
  | release (id : ViewId)
  deriving Repr, DecidableEq

/-- Independent relational transition semantics for the 4-state borrow lattice. -/
inductive PermStep : PermState → PermInstr → PermState → Prop where
  | reserve {ps : PermState} (id : ViewId) (loc : ByteLocation) (perm : BorrowPerm) {byte : UInt8}
      (fresh : ps.view id = none)
      (live : ps.base.byte loc = some byte)
      (compat : ps.CanAdd loc perm) :
      PermStep ps (.reserve id loc perm) { ps with pviews := ⟨id, loc, perm⟩ :: ps.pviews }
  | activate {ps : PermState} (id : ViewId) {v : PermView}
      (found : ps.view id = some v)
      (isReserved : v.perm = .reserved)
      (canAct : ps.CanActivate id v.location) :
      PermStep ps (.activate id)
        { ps with pviews := ps.pviews.map fun w => if w.id == id then { w with perm := .activeExclusive } else w }
  | freeze {ps : PermState} (id : ViewId) {v : PermView}
      (found : ps.view id = some v)
      (canFreeze : v.perm = .reserved ∨ v.perm = .activeExclusive) :
      PermStep ps (.freeze id)
        { ps with pviews := ps.pviews.map fun w => if w.id == id then { w with perm := .frozen } else w }
  | read {ps : PermState} (id : ViewId) {v : PermView} {val : UInt8}
      (found : ps.view id = some v)
      (live : ps.base.byte v.location = some val) :
      PermStep ps (.read id) { ps with base := ps.base.observe val }
  | write {ps : PermState} (id : ViewId) {v : PermView} {old : UInt8} (val : UInt8)
      (found : ps.view id = some v)
      (isActive : v.perm = .activeExclusive)
      (live : ps.base.byte v.location = some old) :
      PermStep ps (.write id val) { ps with base := ps.base.store v.location val }
  | release {ps : PermState} (id : ViewId) {v : PermView}
      (found : ps.view id = some v) :
      PermStep ps (.release id) { ps with pviews := ps.pviews.filter fun w => w.id != id }

def execPerm (ps : PermState) : PermInstr → Option PermState
  | .reserve id loc perm => do
    if (ps.view id).isSome then none else do
      let _ ← ps.base.byte loc
      if ps.CanAdd loc perm then
        some { ps with pviews := ⟨id, loc, perm⟩ :: ps.pviews }
      else none
  | .activate id => do
    let v ← ps.view id
    if v.perm = .reserved ∧ ps.CanActivate id v.location then
      some { ps with pviews := ps.pviews.map fun w => if w.id == id then { w with perm := .activeExclusive } else w }
    else none
  | .freeze id => do
    let v ← ps.view id
    if v.perm = .reserved ∨ v.perm = .activeExclusive then
      some { ps with pviews := ps.pviews.map fun w => if w.id == id then { w with perm := .frozen } else w }
    else none
  | .read id => do
    let v ← ps.view id
    let val ← ps.base.byte v.location
    some { ps with base := ps.base.observe val }
  | .write id val => do
    let v ← ps.view id
    if v.perm = .activeExclusive then
      let _ ← ps.base.byte v.location
      some { ps with base := ps.base.store v.location val }
    else none
  | .release id => do
    let _ ← ps.view id
    some { ps with pviews := ps.pviews.filter fun w => w.id != id }

def runPerm (ps : PermState) : List PermInstr → Option PermState
  | [] => some ps
  | i :: rest => (execPerm ps i).bind fun mid => runPerm mid rest

inductive PermRuns : PermState → List PermInstr → PermState → Prop where
  | nil : PermRuns ps [] ps
  | cons : PermStep ps i mid → PermRuns mid rest final → PermRuns ps (i :: rest) final

theorem execPerm_sound {ps ps' : PermState} {instr : PermInstr}
    (h : execPerm ps instr = some ps') : PermStep ps instr ps' := by
  cases instr <;>
    simp only [execPerm, bind, Option.bind_eq_some_iff,
      Option.ite_none_left_eq_some, Option.ite_none_right_eq_some,
      Option.some.injEq, Bool.not_eq_true, Option.isSome_eq_false_iff] at h
  case reserve id loc perm =>
    rcases h with ⟨fresh, byte, live, compat, rfl⟩
    exact .reserve id loc perm (Option.isNone_iff_eq_none.mp fresh) live compat
  case activate id =>
    rcases h with ⟨v, found, ⟨isRes, canAct⟩, rfl⟩
    exact .activate id found isRes canAct
  case freeze id =>
    rcases h with ⟨v, found, canFrz, rfl⟩
    exact .freeze id found canFrz
  case read id =>
    rcases h with ⟨v, found, val, live, rfl⟩
    exact .read id found live
  case write id val =>
    rcases h with ⟨v, found, isAct, old, live, rfl⟩
    exact .write id val found isAct live
  case release id =>
    rcases h with ⟨v, found, rfl⟩
    exact .release id found

theorem execPerm_complete {ps ps' : PermState} {instr : PermInstr}
    (h : PermStep ps instr ps') : execPerm ps instr = some ps' := by
  cases h <;> simp_all [execPerm, bind]

theorem execPerm_correct (ps ps' : PermState) (instr : PermInstr) :
    execPerm ps instr = some ps' ↔ PermStep ps instr ps' :=
  ⟨execPerm_sound, execPerm_complete⟩

theorem runPerm_sound {ps final : PermState} {prog : List PermInstr}
    (h : runPerm ps prog = some final) : PermRuns ps prog final := by
  induction prog generalizing ps with
  | nil =>
    cases h
    exact .nil
  | cons i rest ih =>
    simp only [runPerm, Option.bind_eq_some_iff] at h
    obtain ⟨mid, h1, h2⟩ := h
    exact .cons (execPerm_sound h1) (ih h2)

theorem runPerm_complete {ps final : PermState} {prog : List PermInstr}
    (h : PermRuns ps prog final) : runPerm ps prog = some final := by
  induction h with
  | nil => rfl
  | cons h1 _ ih =>
    simp only [runPerm, execPerm_complete h1, Option.bind_some]
    exact ih

theorem runPerm_correct (ps final : PermState) (prog : List PermInstr) :
    runPerm ps prog = some final ↔ PermRuns ps prog final :=
  ⟨runPerm_sound, runPerm_complete⟩

private theorem permView_unique {ps : PermState} (hValid : ps.ViewsValid)
    {id : ViewId} {v w : PermView}
    (hFound : ps.view id = some v) (hMem : w ∈ ps.pviews) (hId : w.id = id) :
    w = v := by
  have hvMem : v ∈ ps.pviews := List.mem_of_find?_eq_some hFound
  have hvId : v.id = id := by simpa [PermState.view] using List.find?_some hFound
  obtain ⟨i, hi, atV⟩ := List.mem_iff_getElem.mp hvMem
  obtain ⟨j, hj, atW⟩ := List.mem_iff_getElem.mp hMem
  have hPair := List.pairwise_iff_getElem.mp hValid
  rcases Nat.lt_trichotomy i j with lt | rfl | gt
  · have hNe := (hPair i j hi hj lt).1
    rw [atV, atW, hvId, hId] at hNe
    exact False.elim (hNe rfl)
  · exact atW.symm.trans atV
  · have hNe := (hPair j i hj hi gt).1
    rw [atV, atW, hvId, hId] at hNe
    exact False.elim (hNe rfl)

theorem PermStep.preserves_valid {ps ps' : PermState} {instr : PermInstr}
    (hStep : PermStep ps instr ps') (hValid : ps.Valid) : ps'.Valid := by
  obtain ⟨hViews, hLive⟩ := hValid
  cases hStep with
  | reserve id loc perm fresh live compat =>
    refine ⟨?_, ?_⟩
    · apply List.Pairwise.cons _ hViews
      intro v hv
      have hIdNe : id ≠ v.id := by
        have hNone := List.find?_eq_none.mp fresh v hv
        simp only [beq_iff_eq] at hNone
        exact Ne.symm hNone
      have hCompat : (⟨id, loc, perm⟩ : PermView).location ≠ v.location ∨
          (⟨id, loc, perm⟩ : PermView).perm.Compatible v.perm := by
        rcases compat v hv with hLoc | hComp
        · exact Or.inl hLoc.symm
        · exact Or.inr hComp
      exact ⟨hIdNe, hCompat⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hOld
      · simp [live]
      · exact hLive w hOld
  | activate id found isReserved canAct =>
    rename_i v
    refine ⟨?_, ?_⟩
    · dsimp [PermState.ViewsValid]
      rw [List.pairwise_map]
      apply List.Pairwise.imp_of_mem _ hViews
      intro a b haMem hbMem hab
      obtain ⟨hIdNe, hLocOrComp⟩ := hab
      by_cases ha : a.id = id
      · have hb : b.id ≠ id := fun hbEq => hIdNe (ha.trans hbEq.symm)
        have haEq : a = v := permView_unique hViews found haMem ha
        have hbLoc : b.location ≠ v.location := by
          rcases canAct b hbMem with hbId | hbLoc
          · exact False.elim (hb hbId)
          · exact hbLoc
        have hNeLoc : a.location ≠ b.location := by
          rw [haEq]
          exact hbLoc.symm
        simp [ha, hb, hNeLoc, Ne.symm hb]
      · by_cases hb : b.id = id
        · have hbEq : b = v := permView_unique hViews found hbMem hb
          have haLoc : a.location ≠ v.location := by
            rcases canAct a haMem with haId | haLoc
            · exact False.elim (ha haId)
            · exact haLoc
          have hNeLoc : a.location ≠ b.location := by
            rw [hbEq]
            exact haLoc
          simp [ha, hb, hNeLoc]
        · simp [ha, hb, hIdNe, hLocOrComp]
    · intro w hw
      obtain ⟨u, huMem, rfl⟩ := List.mem_map.mp hw
      split
      · simpa using hLive u huMem
      · exact hLive u huMem
  | freeze id found canFreeze =>
    rename_i v
    refine ⟨?_, ?_⟩
    · dsimp [PermState.ViewsValid]
      rw [List.pairwise_map]
      apply List.Pairwise.imp_of_mem _ hViews
      intro a b haMem hbMem hab
      obtain ⟨hIdNe, hLocOrComp⟩ := hab
      by_cases ha : a.id = id
      · have hb : b.id ≠ id := fun hbEq => hIdNe (ha.trans hbEq.symm)
        have haEq : a = v := permView_unique hViews found haMem ha
        simp only [ha, beq_self_eq_true, ↓reduceIte,
          show (b.id == id) = false from beq_false_of_ne hb, Bool.false_eq_true]
        refine ⟨by rw [← ha]; exact hIdNe, ?_⟩
        rcases hLocOrComp with hLoc | hComp
        · exact Or.inl hLoc
        · exact Or.inr (BorrowPerm.freeze_monotone (haEq ▸ canFreeze) hComp)
      · by_cases hb : b.id = id
        · have hbEq : b = v := permView_unique hViews found hbMem hb
          simp only [show (a.id == id) = false from beq_false_of_ne ha, Bool.false_eq_true,
            ↓reduceIte, hb, beq_self_eq_true]
          refine ⟨by rw [← hb]; exact hIdNe, ?_⟩
          rcases hLocOrComp with hLoc | hComp
          · exact Or.inl hLoc
          · exact Or.inr (BorrowPerm.compatible_symm
              (BorrowPerm.freeze_monotone (hbEq ▸ canFreeze) (BorrowPerm.compatible_symm hComp)))
        · simp [ha, hb, hIdNe, hLocOrComp]
    · intro w hw
      obtain ⟨u, huMem, rfl⟩ := List.mem_map.mp hw
      split
      · simpa using hLive u huMem
      · exact hLive u huMem
  | read id found live =>
    exact ⟨hViews, hLive⟩
  | write id val found isActive live =>
    rename_i v _
    refine ⟨hViews, ?_⟩
    intro w hw
    by_cases hLoc : w.location = v.location
    · rw [hLoc, State.store_byte_written ps.base v.location _ val live]
      rfl
    · rw [State.store_byte_other ps.base v.location w.location val (Ne.symm hLoc)]
      exact hLive w hw
  | release id found =>
    refine ⟨List.Pairwise.filter _ hViews, ?_⟩
    intro w hw
    exact hLive w (List.mem_filter.mp hw).1

theorem PermRuns.preserves_valid {ps final : PermState} {prog : List PermInstr}
    (hRuns : PermRuns ps prog final) (hValid : ps.Valid) : final.Valid := by
  induction hRuns with
  | nil => exact hValid
  | cons hStep _ ih => exact ih (hStep.preserves_valid hValid)

theorem PermStep.activate_unique {ps ps' : PermState} {id : ViewId} {v : PermView}
    (hFound : ps.view id = some v)
    (hCanAct : ps.CanActivate id v.location)
    (hStep : PermStep ps (.activate id) ps') :
    ∀ w ∈ ps'.pviews, w.id = id ∨ w.location ≠ v.location := by
  cases hStep with
  | activate _ found2 _ _ =>
    intro w hw
    obtain ⟨u, huMem, rfl⟩ := List.mem_map.mp hw
    by_cases huId : u.id = id
    · left; simp [huId]
    · right
      have hFalse : (u.id == id) = false := beq_false_of_ne huId
      simp only [hFalse, Bool.false_eq_true, ↓reduceIte]
      have sameV := Option.some.inj (found2.symm.trans hFound)
      rcases hCanAct u huMem with hEq | hNe
      · exact False.elim (huId hEq)
      · exact sameV ▸ hNe

theorem PermStep.write_exclusive_footprint {ps ps' : PermState} {id : ViewId} {val : UInt8}
    {v : PermView} (hValid : ps.Valid) (hFound : ps.view id = some v)
    (hStep : PermStep ps (.write id val) ps') :
    ∀ w ∈ ps.pviews, w.id ≠ id →
      (accessFootprint v.location .exclusive).Compatible
        (accessFootprint w.location w.perm.toAccessMode) := by
  cases hStep with
  | write _ _ found2 isAct _ =>
    rename_i v2 _ _
    have hEqV : v2 = v := Option.some.inj (found2.symm.trans hFound)
    subst hEqV
    intro w hwMem hwNe
    have hvMem : v2 ∈ ps.pviews := List.mem_of_find?_eq_some found2
    have hvId : v2.id = id := by simpa [PermState.view] using List.find?_some found2
    obtain ⟨i, hi, atV⟩ := List.mem_iff_getElem.mp hvMem
    obtain ⟨j, hj, atW⟩ := List.mem_iff_getElem.mp hwMem
    have hPair := List.pairwise_iff_getElem.mp hValid.1
    have hLocNe : v2.location ≠ w.location := by
      rcases Nat.lt_trichotomy i j with lt | rfl | gt
      · have hRel := (hPair i j hi hj lt).2
        rw [atV, atW, isAct] at hRel
        rcases hRel with hLoc | hComp
        · exact hLoc
        · exact False.elim (BorrowPerm.activeExclusive_conflicts_all w.perm hComp)
      · rw [atV] at atW
        rw [← atW, hvId] at hwNe
        exact False.elim (hwNe rfl)
      · have hRel := (hPair j i hj hi gt).2
        rw [atV, atW, isAct] at hRel
        rcases hRel with hLoc | hComp
        · exact hLoc.symm
        · exact False.elim (BorrowPerm.activeExclusive_conflicts_all w.perm
            (BorrowPerm.compatible_symm hComp))
    exact (accessFootprint_compatible v2.location w.location .exclusive w.perm.toAccessMode).mpr
      (Or.inl hLocNe)

theorem PermStep.write_frame_other {ps ps' : PermState} {id : ViewId} {val : UInt8}
    {v : PermView} (hFound : ps.view id = some v)
    (hStep : PermStep ps (.write id val) ps')
    (other : ByteLocation) (hDiff : v.location ≠ other) :
    ps'.base.byte other = ps.base.byte other := by
  cases hStep with
  | write _ _ found2 _ _ =>
    rename_i v2 _ _ _
    have hEqV : v2 = v := Option.some.inj (found2.symm.trans hFound)
    subst hEqV
    exact Core.State.store_byte_other ps.base v2.location other val hDiff

end Aethel.Permissions
