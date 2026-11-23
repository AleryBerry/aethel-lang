import Aethel.AutomaticLayout
import Aethel.FunctionSummaries
import Aethel.Permissions
import Aethel.LayoutPaths

namespace Aethel.CoBorrowPacking

open Aethel Aethel.AutomaticLayout

/-- Co-borrow interference graph over a record's top-level fields. An edge `(i, j)`
forbids packing fields `i` and `j` into the same physical byte so independent
exclusive views can never suffer a packed-byte read-modify-write collision. -/
structure CoBorrowGraph where
  fieldCount : Nat
  conflicts : List (Nat × Nat)
  deriving Repr, DecidableEq

def CoBorrowGraph.interferes (g : CoBorrowGraph) (i j : Nat) : Bool :=
  decide (i < g.fieldCount ∧ j < g.fieldCount ∧ i ≠ j ∧
    ((i, j) ∈ g.conflicts ∨ (j, i) ∈ g.conflicts))

def CoBorrowGraph.hasAnyConflict (g : CoBorrowGraph) (i : Nat) : Bool :=
  (List.range g.fieldCount).any fun j => g.interferes i j

private def effectFieldConflicts (e1 e2 : Effect) (i j : Nat) : Bool :=
  let writeI := e1.writes.any (fun p => p.head? == some i)
  let touchJ := e2.reads.any (fun p => p.head? == some j) ||
                e2.writes.any (fun p => p.head? == some j) ||
                e2.invalidates.any (fun p => p.head? == some j)
  let writeJ := e2.writes.any (fun p => p.head? == some j)
  let touchI := e1.reads.any (fun p => p.head? == some i) ||
                e1.writes.any (fun p => p.head? == some i) ||
                e1.invalidates.any (fun p => p.head? == some i)
  (writeI && touchJ) || (writeJ && touchI)

def CoBorrowGraph.ofEffects (fieldCount : Nat) (pairs : List (Effect × Effect)) : CoBorrowGraph :=
  let edges := (List.range fieldCount).flatMap fun i =>
    (List.range fieldCount).filterMap fun j =>
      if i != j && pairs.any (fun (e1, e2) => effectFieldConflicts e1 e2 i j) then some (i, j) else none
  ⟨fieldCount, edges⟩

def synthesizePolicy (g : CoBorrowGraph) (i : Nat) : StoragePolicy :=
  if g.hasAnyConflict i then .addressable else .mayShareByte

def applyPolicies (g : CoBorrowGraph) (fields : List Schema) : Schema :=
  .record (fields.zipIdx.map fun (s, idx) => (synthesizePolicy g idx, s))

def autoPlan (abi : TargetIntegerABI) (g : CoBorrowGraph) (fields : List Schema) : Option Layout :=
  AutomaticLayout.plan abi (applyPolicies g fields)

def ByteSpanDisjoint (a b : Field) : Prop :=
  a.bytes = 0 ∨ b.bytes = 0 ∨
  a.1.byteOffset + a.bytes ≤ b.1.byteOffset ∨ b.1.byteOffset + b.bytes ≤ a.1.byteOffset

def PackingConflictFree (g : CoBorrowGraph) (placed : List Field) : Prop :=
  ∀ i j, (hi : i < placed.length) → (hj : j < placed.length) →
    i ≠ j → g.interferes i j = true → ByteSpanDisjoint placed[i] placed[j]

theorem CoBorrowGraph.interferes_symm {g : CoBorrowGraph} {i j : Nat}
    (h : g.interferes i j = true) : g.interferes j i = true := by
  simp only [interferes, decide_eq_true_eq] at h ⊢
  obtain ⟨hi, hj, hne, hor⟩ := h
  exact ⟨hj, hi, hne.symm, hor.symm⟩

theorem synthesizePolicy_conflict_addressable {g : CoBorrowGraph} {i j : Nat}
    (h : g.interferes i j = true) :
    synthesizePolicy g i = .addressable ∧ synthesizePolicy g j = .addressable := by
  have hInfo := h
  simp only [CoBorrowGraph.interferes, decide_eq_true_eq] at hInfo
  obtain ⟨hi, hj, _, _⟩ := hInfo
  have hiAny : g.hasAnyConflict i = true := by
    simp only [CoBorrowGraph.hasAnyConflict, List.any_eq_true, List.mem_range]
    exact ⟨j, hj, h⟩
  have hjAny : g.hasAnyConflict j = true := by
    simp only [CoBorrowGraph.hasAnyConflict, List.any_eq_true, List.mem_range]
    exact ⟨i, hi, CoBorrowGraph.interferes_symm h⟩
  simp [synthesizePolicy, hiAny, hjAny]

theorem autoPlan_conforms {abi : TargetIntegerABI} {g : CoBorrowGraph}
    {fields : List Schema} {layout : Layout}
    (hPlan : autoPlan abi g fields = some layout) :
    Conforms abi (applyPolicies g fields) layout :=
  AutomaticLayout.plan_sound hPlan

private theorem applyPolicies_field_policy {g : CoBorrowGraph} {fields : List Schema}
    {i : Nat} {policy : StoragePolicy} {child : Schema}
    (hAt : (fields.zipIdx.map fun (s, idx) => (synthesizePolicy g idx, s))[i]? = some (policy, child)) :
    policy = synthesizePolicy g i := by
  rw [List.getElem?_map] at hAt
  cases hZip : fields.zipIdx[i]? with
  | none => simp [hZip] at hAt
  | some entry =>
    simp only [hZip, Option.map_some, Option.some.injEq] at hAt
    obtain ⟨hLen, atZip⟩ := List.getElem?_eq_some_iff.mp hZip
    rw [List.getElem_zipIdx hLen] at atZip
    have hIdx : i = entry.2 := by
      have := congrArg Prod.snd atZip
      simpa using this
    rw [hIdx]
    exact (Prod.mk.inj hAt).1.symm

private theorem field_valid_addressable_no_bit {total align : Nat} {f : Field}
    (hValid : Field.Valid total align .addressable f) : f.1.bitOffset = none := by
  unfold Field.Valid at hValid
  cases hBit : f.1.bitOffset with
  | none => rfl
  | some bit =>
    rw [hBit] at hValid
    cases hValid.2.1

private theorem separate_no_bit_disjoint {a b : Field}
    (hSep : Field.Separate a b)
    (ha : a.1.bitOffset = none) (hb : b.1.bitOffset = none) :
    ByteSpanDisjoint a b := by
  unfold Field.Separate at hSep
  rcases hSep with h0 | h0 | h1 | h2 | ⟨_, hBits⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl h0)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr h2))
  · rw [ha, hb] at hBits
    contradiction

theorem autoPlan_conflict_free {abi : TargetIntegerABI} {g : CoBorrowGraph}
    {fields : List Schema} {size alignment : Nat} {placed : List Field}
    (hPlan : autoPlan abi g fields = some (.record size alignment placed)) :
    PackingConflictFree g placed := by
  have hConf := autoPlan_conforms hPlan
  intro i j hi hj hNe hInt
  obtain ⟨hPolI, hPolJ⟩ := synthesizePolicy_conflict_addressable hInt
  obtain ⟨policyI, _, hSrcI, hValidI, _⟩ := hConf.field (List.getElem?_eq_getElem hi)
  obtain ⟨policyJ, _, hSrcJ, hValidJ, _⟩ := hConf.field (List.getElem?_eq_getElem hj)
  have hPi : policyI = .addressable := (applyPolicies_field_policy hSrcI).trans hPolI
  have hPj : policyJ = .addressable := (applyPolicies_field_policy hSrcJ).trans hPolJ
  have hBitI := field_valid_addressable_no_bit (hPi ▸ hValidI)
  have hBitJ := field_valid_addressable_no_bit (hPj ▸ hValidJ)
  have hPair := by
    cases hConf with
    | record _ _ _ apart _ _ => exact apart
  have hSep : Field.Separate placed[i] placed[j] := by
    rcases Nat.lt_or_gt_of_ne hNe with hLt | hGt
    · exact List.pairwise_iff_getElem.mp hPair i j hi hj hLt
    · exact (List.pairwise_iff_getElem.mp hPair j i hj hi hGt).symm
  exact separate_no_bit_disjoint hSep hBitI hBitJ

theorem byteSpanDisjoint_implies_no_shared_byte {a b : Field}
    (hDisj : ByteSpanDisjoint a b) :
    ∀ off, ¬ (a.1.byteOffset ≤ off ∧ off < a.1.byteOffset + a.bytes ∧
              b.1.byteOffset ≤ off ∧ off < b.1.byteOffset + b.bytes) := by
  intro off ⟨haLo, haHi, hbLo, hbHi⟩
  rcases hDisj with h0 | h0 | h1 | h2 <;> omega

end Aethel.CoBorrowPacking
