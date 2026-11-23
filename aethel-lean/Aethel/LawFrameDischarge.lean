import Aethel.FunctionSummaries
import Aethel.RecordRuntime
import Aethel.LayoutPaths
import Aethel.CacheLayout
import Aethel.CategoricalFusion

namespace Aethel.LawFrameDischarge

open Aethel Aethel.Core Aethel.AutomaticLayout Aethel.CacheLayout Aethel.CategoricalFusion

/-!
## Tier 0 — Instant Structural & Frame Discharge

Automatically proves `preserves` frame laws directly from `Effect` write/invalidation
footprints and `CollectionLayout` field indices across packed record leaves, AoS, SoA,
and Tiled AoSoA layouts.
-/

def checkEffectPreserves (eff : Effect) (preserved : List (List Nat)) : Bool :=
  preserved.all fun p =>
    eff.writes.all (fun w => !pathConflicts w p) &&
    eff.invalidates.all (fun inv => !pathConflicts inv p)

/-- Independent mathematical specification for record/path frame preservation. -/
def EffectPreserves (eff : Effect) (preserved : List (List Nat)) : Prop :=
  ∀ p ∈ preserved,
    (∀ w ∈ eff.writes, pathConflicts w p = false) ∧
    (∀ inv ∈ eff.invalidates, pathConflicts inv p = false)

theorem checkEffectPreserves_correct (eff : Effect) (preserved : List (List Nat)) :
    checkEffectPreserves eff preserved = true ↔ EffectPreserves eff preserved := by
  simp only [checkEffectPreserves, EffectPreserves, List.all_eq_true, Bool.and_eq_true,
    Bool.not_eq_true']

theorem checkEffectPreserves_implies_disjoint {eff : Effect} {preserved : List (List Nat)}
    (hCheck : checkEffectPreserves eff preserved = true) :
    Effect.Disjoint eff ⟨preserved, [], []⟩ := by
  have hPres := (checkEffectPreserves_correct eff preserved).mp hCheck
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw r hr
    exact (hPres r hr).1 w hw
  · intro _ _ _ hw2
    cases hw2
  · intro w hw
    cases hw
  · intro inv hinv r hr
    exact (hPres r hr).2 inv hinv
  · intro _ _ _ hw2
    cases hw2
  · intro inv hinv
    cases hinv
  · intro inv hinv
    cases hinv

theorem effectPreserves_subpath_ne {eff : Effect} {preserved : List (List Nat)}
    (hPres : EffectPreserves eff preserved) {root writePath p : List Nat}
    (hRoot : root ∈ eff.writes) (hPref : root.isPrefixOf writePath = true)
    (hp : p ∈ preserved) :
    writePath ≠ p := by
  intro hEq
  subst hEq
  have hFalse := (hPres writePath hp).1 root hRoot
  simp [pathConflicts, hPref] at hFalse

/-- Multi-step record leaf write trace constrained to write footprints of `eff`. -/
inductive RecordWriteTrace {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) (eff : Effect) :
    Image layout.size → Image layout.size → Prop where
  | refl (img : Image layout.size) : RecordWriteTrace planned eff img img
  | step {img mid next : Image layout.size} {root writePath : List Nat} {val : IntegerBits}
      (hRoot : root ∈ eff.writes)
      (hPref : root.isPrefixOf writePath = true)
      (hWrite : writeInteger planned writePath img val = some mid)
      (hRest : RecordWriteTrace planned eff mid next) :
      RecordWriteTrace planned eff img next

theorem tier0_record_trace_preserves {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    {planned : Conforms abi schema layout} {eff : Effect} {preserved : List (List Nat)}
    {imgBefore imgAfter : Image layout.size}
    (hCheck : checkEffectPreserves eff preserved = true)
    (hTrace : RecordWriteTrace planned eff imgBefore imgAfter) :
    ∀ p ∈ preserved,
      readInteger planned p imgAfter = readInteger planned p imgBefore := by
  have hPres := (checkEffectPreserves_correct eff preserved).mp hCheck
  induction hTrace with
  | refl _ =>
    intro _ _
    rfl
  | step hRoot hPref hWrite _ ih =>
    intro p hp
    have hNe : _ ≠ p := effectPreserves_subpath_ne hPres hRoot hPref hp
    exact (ih p hp).trans (readInteger_preserved_other_path planned hNe hWrite)

theorem tier0_recordRef_write_preserves {abi : TargetIntegerABI} {schema : Schema}
    {record : RecordRef abi schema} {state next : State}
    {eff : Effect} {preserved : List (List Nat)} {root writePath : List Nat}
    {targets : List Structured.AccessTarget} {value : IntegerBits}
    (hCheck : checkEffectPreserves eff preserved = true)
    (hRoot : root ∈ eff.writes) (hPref : root.isPrefixOf writePath = true)
    (hWrite : record.write state writePath targets value = some next) :
    ∃ before after : Image record.layout.size,
      (next.allocation record.owner).map Allocation.bytes = some after.toBytes ∧
      ∀ p ∈ preserved,
        readInteger record.conforms p after = readInteger record.conforms p before := by
  have hPres := (checkEffectPreserves_correct eff preserved).mp hCheck
  obtain ⟨before, after, _, hBytes, _, hFrame⟩ := RecordRef.write_effect hWrite
  exact ⟨before, after, hBytes, fun p hp =>
    hFrame p (effectPreserves_subpath_ne hPres hRoot hPref hp)⟩

def checkCollectionPreserves (writtenFields preservedFields : List Nat) : Bool :=
  preservedFields.all fun p => writtenFields.all fun w => w != p

/-- Independent mathematical specification for collection-field frame preservation. -/
def CollectionPreserves (writtenFields preservedFields : List Nat) : Prop :=
  ∀ p ∈ preservedFields, ∀ w ∈ writtenFields, w ≠ p

theorem checkCollectionPreserves_correct (writtenFields preservedFields : List Nat) :
    checkCollectionPreserves writtenFields preservedFields = true ↔
      CollectionPreserves writtenFields preservedFields := by
  simp only [checkCollectionPreserves, CollectionPreserves, List.all_eq_true, bne_iff_ne]

def applyFieldPasses (owner : OwnerId) (layout : CollectionLayout)
    (length fieldCount : Nat) (passes : List (Nat × (UInt8 → UInt8)))
    (s : Core.State) : Core.State :=
  passes.foldl (fun st (f, fn) => mapFieldInPlace owner layout length fieldCount f fn st) s

private theorem tier0_collection_passes_rep {owner : OwnerId} {layout : CollectionLayout}
    (hValid : layout.Valid) {length fieldCount : Nat}
    {passes : List (Nat × (UInt8 → UInt8))} {preservedFields : List Nat}
    (hInBounds : ∀ pass ∈ passes, pass.1 < fieldCount)
    (hCheck : checkCollectionPreserves (passes.map Prod.fst) preservedFields = true)
    {s : Core.State} {table : Nat → Nat → UInt8}
    (hRep : ByteCollectionRep s owner layout length fieldCount table) :
    ∃ table' : Nat → Nat → UInt8,
      ByteCollectionRep (applyFieldPasses owner layout length fieldCount passes s)
        owner layout length fieldCount table' ∧
      ∀ p ∈ preservedFields, ∀ i, i < length → table' i p = table i p := by
  induction passes generalizing s table with
  | nil =>
    exact ⟨table, hRep, fun _ _ _ _ => rfl⟩
  | cons hd tl ih =>
    have hf : hd.1 < fieldCount := hInBounds hd (by simp)
    have hPres : CollectionPreserves (hd.1 :: tl.map Prod.fst) preservedFields :=
      (checkCollectionPreserves_correct _ _).mp hCheck
    have hStepRep := mapFieldInPlace_rep hValid hf hd.2 hRep
    have hTlCheck : checkCollectionPreserves (tl.map Prod.fst) preservedFields = true :=
      (checkCollectionPreserves_correct _ _).mpr fun p hp w hw => hPres p hp w (by simp [hw])
    have hTlBounds : ∀ pass ∈ tl, pass.1 < fieldCount := fun pass hp => hInBounds pass (by simp [hp])
    obtain ⟨table', hFinalRep, hSameTl⟩ := ih hTlBounds hTlCheck hStepRep
    refine ⟨table', hFinalRep, fun p hp i hi => ?_⟩
    have hNe : hd.1 ≠ p := hPres p hp hd.1 (by simp)
    rw [hSameTl p hp i hi]
    exact ite_eq_right hNe.symm

/-- Across AoS, SoA, and Tiled AoSoA layouts, an unchecked sequence of in-place
collection passes leaves every preserved field byte equal to its original value. -/
theorem tier0_collection_passes_preserves {owner : OwnerId} {layout : CollectionLayout}
    (hValid : layout.Valid) {length fieldCount : Nat}
    {passes : List (Nat × (UInt8 → UInt8))} {preservedFields : List Nat}
    (hInBounds : ∀ pass ∈ passes, pass.1 < fieldCount)
    (hBoundsPres : ∀ p ∈ preservedFields, p < fieldCount)
    (hCheck : checkCollectionPreserves (passes.map Prod.fst) preservedFields = true)
    {s : Core.State} {table : Nat → Nat → UInt8}
    (hRep : ByteCollectionRep s owner layout length fieldCount table) :
    ∀ p ∈ preservedFields, ∀ i, i < length →
      (applyFieldPasses owner layout length fieldCount passes s).byte
        ⟨owner, collectionSlot layout length fieldCount i p⟩ = some (table i p) ∧
      (applyFieldPasses owner layout length fieldCount passes s).byte
        ⟨owner, collectionSlot layout length fieldCount i p⟩ =
        s.byte ⟨owner, collectionSlot layout length fieldCount i p⟩ := by
  obtain ⟨table', hFinalRep, hSame⟩ := tier0_collection_passes_rep hValid hInBounds hCheck hRep
  intro p hp i hi
  have hBytes := hFinalRep i hi p (hBoundsPres p hp)
  rw [hSame p hp i hi] at hBytes
  exact ⟨hBytes, hBytes.trans (hRep i hi p (hBoundsPres p hp)).symm⟩

theorem movement_frame_discharged :
    checkEffectPreserves ⟨[[0], [1]], [[0], [1]], []⟩ [[2], [3]] = true := by
  decide

theorem self_write_frame_rejected :
    checkEffectPreserves ⟨[], [[0]], []⟩ [[0]] = false := by
  decide

theorem parent_write_frame_rejected :
    checkEffectPreserves ⟨[], [[]], []⟩ [[0, 1]] = false := by
  decide

theorem collection_overlap_rejected :
    checkCollectionPreserves [0, 1] [1, 2] = false := by
  decide

end Aethel.LawFrameDischarge
