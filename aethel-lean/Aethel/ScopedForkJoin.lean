import Aethel.PermissionLattice
import Aethel.ResourceFrame
import Aethel.CategoricalLNL

namespace Aethel.ScopedForkJoin

open Aethel.Core Aethel.Permissions Aethel.CategoricalLNL

/-!
## Scoped Fork / Join Parallelism & Data-Race Freedom (Phase 6A Lean Gate)

Models structured parallel task footprints (`reads`, `writes`), proves that
disjoint footprints make concurrent task writes commute identically across every
byte location while stabilizing all concurrent reads, and proves that `joinRelease`
restores parent borrow permissions on child completion.
-/

structure TaskFootprint where
  reads : List ByteLocation
  writes : List ByteLocation
  deriving Repr, DecidableEq

def TaskFootprint.touched (f : TaskFootprint) : List ByteLocation :=
  f.reads ++ f.writes

def checkForkDisjoint (a b : TaskFootprint) : Bool :=
  a.writes.all (fun w => !decide (w ∈ b.reads) && !decide (w ∈ b.writes)) &&
  b.writes.all (fun w => !decide (w ∈ a.reads) && !decide (w ∈ a.writes))

/-- Independent mathematical race-freedom specification for scoped child tasks. -/
def ForkDisjoint (a b : TaskFootprint) : Prop :=
  (∀ w ∈ a.writes, w ∉ b.reads ∧ w ∉ b.writes) ∧
  (∀ w ∈ b.writes, w ∉ a.reads ∧ w ∉ a.writes)

theorem checkForkDisjoint_correct (a b : TaskFootprint) :
    checkForkDisjoint a b = true ↔ ForkDisjoint a b := by
  simp only [checkForkDisjoint, ForkDisjoint, Bool.and_eq_true, List.all_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not]

theorem forkDisjoint_symm {a b : TaskFootprint} (h : ForkDisjoint a b) :
    ForkDisjoint b a :=
  ⟨h.2, h.1⟩

theorem forkDisjoint_read_read_safe (r1 r2 : List ByteLocation) :
    ForkDisjoint ⟨r1, []⟩ ⟨r2, []⟩ := by
  constructor <;> intro w hw <;> cases hw

abbrev TaskWrites := List (ByteLocation × UInt8)

def applyTaskWrites (s : Core.State) (ws : TaskWrites) : Core.State :=
  ws.foldl (fun st (loc, v) => st.store loc v) s

def WritesWithin (ws : TaskWrites) (fp : TaskFootprint) : Prop :=
  ∀ p ∈ ws, p.1 ∈ fp.writes

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

theorem applyTaskWrites_preserves_outside {s : Core.State} {ws : TaskWrites}
    {fp : TaskFootprint} {loc : ByteLocation}
    (hWithin : WritesWithin ws fp) (hOut : loc ∉ fp.writes) :
    (applyTaskWrites s ws).byte loc = s.byte loc := by
  induction ws generalizing s with
  | nil => rfl
  | cons hd tl ih =>
    have hIn : hd.1 ∈ fp.writes := hWithin hd (by simp)
    have hNe : hd.1 ≠ loc := fun hEq => hOut (hEq ▸ hIn)
    have hTail : (applyTaskWrites (s.store hd.1 hd.2) tl).byte loc =
        (s.store hd.1 hd.2).byte loc :=
      ih (fun p hp => hWithin p (by simp [hp]))
    exact hTail.trans (Core.State.store_byte_other s hd.1 loc hd.2 hNe)

private theorem applyTaskWrites_byte_at {s1 s2 : Core.State} (ws : TaskWrites)
    (loc : ByteLocation) (hEq : s1.byte loc = s2.byte loc) :
    (applyTaskWrites s1 ws).byte loc = (applyTaskWrites s2 ws).byte loc := by
  induction ws generalizing s1 s2 with
  | nil => exact hEq
  | cons hd tl ih =>
    dsimp [applyTaskWrites]
    apply ih
    by_cases hHit : hd.1 = loc
    · subst hHit
      cases hB : s1.byte hd.1 with
      | none =>
        have hB2 : s2.byte hd.1 = none := hEq.symm.trans hB
        rw [state_store_byte_none s1 hd.1 hd.2 hB, state_store_byte_none s2 hd.1 hd.2 hB2]
      | some old =>
        have hB2 : s2.byte hd.1 = some old := hEq.symm.trans hB
        rw [Core.State.store_byte_written s1 hd.1 old hd.2 hB,
          Core.State.store_byte_written s2 hd.1 old hd.2 hB2]
    · rw [Core.State.store_byte_other s1 hd.1 loc hd.2 hHit,
        Core.State.store_byte_other s2 hd.1 loc hd.2 hHit]
      exact hEq

theorem forkDisjoint_writes_commute {fpA fpB : TaskFootprint}
    (hCheck : checkForkDisjoint fpA fpB = true)
    {wsA wsB : TaskWrites} (hWA : WritesWithin wsA fpA) (hWB : WritesWithin wsB fpB)
    (s : Core.State) :
    ∀ loc : ByteLocation,
      (applyTaskWrites (applyTaskWrites s wsA) wsB).byte loc =
      (applyTaskWrites (applyTaskWrites s wsB) wsA).byte loc := by
  have hDisj := (checkForkDisjoint_correct fpA fpB).mp hCheck
  intro loc
  by_cases hInA : loc ∈ fpA.writes
  · have hNotB : loc ∉ fpB.writes := (hDisj.1 loc hInA).2
    have hSt1 : (applyTaskWrites (applyTaskWrites s wsA) wsB).byte loc =
        (applyTaskWrites s wsA).byte loc :=
      applyTaskWrites_preserves_outside hWB hNotB
    have hSt2 : (applyTaskWrites (applyTaskWrites s wsB) wsA).byte loc =
        (applyTaskWrites s wsA).byte loc :=
      applyTaskWrites_byte_at wsA loc (applyTaskWrites_preserves_outside hWB hNotB)
    exact hSt1.trans hSt2.symm
  · have hSt1 : (applyTaskWrites (applyTaskWrites s wsA) wsB).byte loc =
        (applyTaskWrites s wsB).byte loc :=
      applyTaskWrites_byte_at wsB loc (applyTaskWrites_preserves_outside hWA hInA)
    have hSt2 : (applyTaskWrites (applyTaskWrites s wsB) wsA).byte loc =
        (applyTaskWrites s wsB).byte loc :=
      applyTaskWrites_preserves_outside hWA hInA
    exact hSt1.trans hSt2.symm

theorem forkDisjoint_reads_stable {fpA fpB : TaskFootprint}
    (hCheck : checkForkDisjoint fpA fpB = true)
    {wsB : TaskWrites} (hWB : WritesWithin wsB fpB) (s : Core.State) :
    ∀ loc ∈ fpA.reads, (applyTaskWrites s wsB).byte loc = s.byte loc := by
  have hDisj := (checkForkDisjoint_correct fpA fpB).mp hCheck
  intro loc hRead
  apply applyTaskWrites_preserves_outside hWB
  intro hWrite
  exact (hDisj.2 loc hWrite).1 hRead

/-! ## Scoped Fork / Join Permission Transitions on `PermState` -/

def forkAddView (ps : PermState) (v : PermView) : Option PermState :=
  if (ps.view v.id).isSome then none
  else if (ps.base.byte v.location).isNone then none
  else if ps.CanAdd v.location v.perm then
    some { ps with pviews := v :: ps.pviews }
  else none

def forkAcquire (ps : PermState) : List PermView → Option PermState
  | [] => some ps
  | v :: vs =>
    match forkAddView ps v with
    | none => none
    | some mid => forkAcquire mid vs

def joinRelease (ps : PermState) (ids : List ViewId) : PermState :=
  { ps with pviews := ps.pviews.filter fun v => !(ids.contains v.id) }

private theorem forkAddView_preserves_valid {ps mid : PermState} {v : PermView}
    (hAdd : forkAddView ps v = some mid) (hValid : ps.Valid) :
    mid.Valid := by
  dsimp [forkAddView] at hAdd
  cases hView : ps.view v.id with
  | some existing =>
    simp [hView] at hAdd
  | none =>
    simp only [hView, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hAdd
    cases hByte : ps.base.byte v.location with
    | none =>
      simp [hByte] at hAdd
    | some b =>
      simp only [hByte, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at hAdd
      split at hAdd
      · next hCompat =>
        cases hAdd
        exact (PermStep.reserve v.id v.location v.perm hView hByte hCompat).preserves_valid hValid
      · cases hAdd

theorem forkAcquire_preserves_valid {ps child : PermState} {vs : List PermView}
    (hAcq : forkAcquire ps vs = some child) (hValid : ps.Valid) :
    child.Valid := by
  induction vs generalizing ps with
  | nil =>
    cases hAcq
    exact hValid
  | cons v rest ih =>
    dsimp [forkAcquire] at hAcq
    cases hStep : forkAddView ps v with
    | none =>
      rw [hStep] at hAcq
      cases hAcq
    | some mid =>
      rw [hStep] at hAcq
      exact ih hAcq (forkAddView_preserves_valid hStep hValid)

private theorem forkAcquire_prefix {ps child : PermState} {vs : List PermView}
    (hAcq : forkAcquire ps vs = some child) :
    child.base = ps.base ∧ ∃ added, child.pviews = added ++ ps.pviews ∧ ∀ a ∈ added, a ∈ vs := by
  induction vs generalizing ps with
  | nil =>
    cases hAcq
    exact ⟨rfl, [], rfl, fun _ h => nomatch h⟩
  | cons v rest ih =>
    dsimp [forkAcquire] at hAcq
    cases hStep : forkAddView ps v with
    | none =>
      rw [hStep] at hAcq
      cases hAcq
    | some mid =>
      rw [hStep] at hAcq
      have hMid : mid.base = ps.base ∧ mid.pviews = v :: ps.pviews := by
        dsimp [forkAddView] at hStep
        repeat (split at hStep <;> try contradiction)
        cases hStep
        exact ⟨rfl, rfl⟩
      obtain ⟨hBase, added, hViews, hSub⟩ := ih hAcq
      refine ⟨hBase.trans hMid.1, added ++ [v], ?_, ?_⟩
      · rw [hViews, hMid.2]
        simp [List.append_assoc]
      · intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with haAdded | rfl
        · exact List.mem_cons_of_mem v (hSub a haAdded)
        · exact List.mem_cons_self

theorem joinRelease_preserves_valid {ps : PermState} (ids : List ViewId)
    (hValid : ps.Valid) :
    (joinRelease ps ids).Valid := by
  obtain ⟨hViews, hLive⟩ := hValid
  refine ⟨?_, ?_⟩
  · dsimp [joinRelease, PermState.ViewsValid]
    exact hViews.filter _
  · intro v hv
    simp only [joinRelease, List.mem_filter] at hv
    exact hLive v hv.1

theorem joinRelease_restores_parent {parent child : PermState} {vs : List PermView}
    (hAcq : forkAcquire parent vs = some child)
    (hFresh : ∀ v ∈ vs, parent.view v.id = none) :
    joinRelease child (vs.map PermView.id) = parent := by
  obtain ⟨hBase, added, hViews, hSub⟩ := forkAcquire_prefix hAcq
  cases parent with
  | mk baseParent pviewsParent =>
    dsimp [joinRelease] at *
    subst hBase
    congr 1
    rw [hViews, List.filter_append]
    have hAddedNil : added.filter (fun v => !((vs.map PermView.id).contains v.id)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      simp
      exact ⟨a, hSub a ha, rfl⟩
    have hParentSame : pviewsParent.filter (fun v => !((vs.map PermView.id).contains v.id)) =
        pviewsParent := by
      rw [List.filter_eq_self]
      intro w hw
      simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, List.contains_iff_mem, List.mem_map,
        not_exists, not_and]
      intro v hv hEq
      have hNone := hFresh v hv
      have hBad := List.find?_eq_none.mp hNone w hw
      simp [hEq] at hBad
    rw [hAddedNil, hParentSame, List.nil_append]

/-! ## Negative Race-Freedom Counterexamples -/

theorem fork_write_write_overlap_rejected :
    checkForkDisjoint ⟨[], [⟨0, 0⟩]⟩ ⟨[], [⟨0, 0⟩]⟩ = false := by
  decide

theorem fork_parent_write_during_child_read_rejected :
    checkForkDisjoint ⟨[⟨0, 0⟩], []⟩ ⟨[], [⟨0, 0⟩]⟩ = false := by
  decide

/-! ## Multi-Branch OS-Thread Schedule Determinism (`@parallel fork / join`) -/

structure ForkTask where
  footprint : TaskFootprint
  writes : TaskWrites
  within : WritesWithin writes footprint

def PairwiseForkDisjoint (tasks : List ForkTask) : Prop :=
  tasks.Pairwise fun a b => ForkDisjoint a.footprint b.footprint

def runForkSchedule (s : Core.State) (tasks : List ForkTask) : Core.State :=
  tasks.foldl (fun st t => applyTaskWrites st t.writes) s

private theorem runForkSchedule_byte_at {s1 s2 : Core.State} (tasks : List ForkTask)
    (loc : ByteLocation) (hEq : s1.byte loc = s2.byte loc) :
    (runForkSchedule s1 tasks).byte loc = (runForkSchedule s2 tasks).byte loc := by
  induction tasks generalizing s1 s2 with
  | nil => exact hEq
  | cons t rest ih =>
    dsimp [runForkSchedule]
    exact ih (applyTaskWrites_byte_at t.writes loc hEq)

theorem pairwiseForkDisjoint_perm {l1 l2 : List ForkTask}
    (hPerm : List.Perm l1 l2) (hDisj : PairwiseForkDisjoint l1) :
    PairwiseForkDisjoint l2 := by
  induction hPerm with
  | nil => exact .nil
  | @cons x xs ys _ ih =>
    dsimp [PairwiseForkDisjoint] at hDisj ⊢
    rw [List.pairwise_cons] at hDisj ⊢
    refine ⟨?_, ih hDisj.2⟩
    intro z hz
    exact hDisj.1 z ((List.Perm.mem_iff (by assumption)).mpr hz)
  | swap x y l =>
    dsimp [PairwiseForkDisjoint] at hDisj ⊢
    rw [List.pairwise_cons] at hDisj
    obtain ⟨hYAll, hXL⟩ := hDisj
    rw [List.pairwise_cons] at hXL
    obtain ⟨hXAll, hL⟩ := hXL
    rw [List.pairwise_cons]
    refine ⟨?_, ?_⟩
    · intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hzL
      · exact forkDisjoint_symm (hYAll x (by simp))
      · exact hXAll z hzL
    · rw [List.pairwise_cons]
      exact ⟨fun z hz => hYAll z (by simp [hz]), hL⟩
  | trans h12 h23 ih1 ih2 =>
    exact ih2 (ih1 hDisj)

/-- Regardless of how `@parallel fork` OS threads are interleaved by the kernel
scheduler, any two schedules with pairwise-disjoint footprints produce bitwise
identical final heap memory across every byte location. -/
theorem parallel_fork_join_deterministic (s : Core.State) {sched1 sched2 : List ForkTask}
    (hPerm : List.Perm sched1 sched2) (hDisj : PairwiseForkDisjoint sched1) :
    ∀ loc : ByteLocation,
      (runForkSchedule s sched1).byte loc = (runForkSchedule s sched2).byte loc := by
  induction hPerm generalizing s with
  | nil =>
    intro _
    rfl
  | cons x _ ih =>
    intro loc
    dsimp [PairwiseForkDisjoint] at hDisj
    rw [List.pairwise_cons] at hDisj
    exact ih (applyTaskWrites s x.writes) hDisj.2 loc
  | swap x y l =>
    intro loc
    dsimp [PairwiseForkDisjoint] at hDisj
    rw [List.pairwise_cons] at hDisj
    have hYX : ForkDisjoint y.footprint x.footprint := hDisj.1 x (by simp)
    have hCheck := (checkForkDisjoint_correct y.footprint x.footprint).mpr hYX
    dsimp [runForkSchedule]
    apply runForkSchedule_byte_at l loc
    exact forkDisjoint_writes_commute hCheck y.within x.within s loc
  | trans h12 _ ih1 ih2 =>
    intro loc
    exact (ih1 s hDisj loc).trans (ih2 s (pairwiseForkDisjoint_perm h12 hDisj) loc)

end Aethel.ScopedForkJoin
