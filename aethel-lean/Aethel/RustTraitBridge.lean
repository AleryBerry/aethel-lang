import Aethel.CategoricalTraits

namespace Aethel.RustTraitBridge

open Aethel.CategoricalTraits

/-!
## Formal Bridge: `rustc` Trait Coherence & Orphan Rules $\hookrightarrow$ Aethel Traits

Mechanizes Rust's orphan check (`compiler/rustc_hir_analysis/src/coherence/orphan.rs`,
`compiler/rustc_next_trait_solver/src/coherence.rs` at `c884ecfbabb04b04fa5054dafc67ec258ecde745`)
and proves the **Rust $\rightarrow$ Aethel migration theorem**:
1. Independent crates passing `orphanCheckLocal` can never collide on a ground `impl`
   (`rust_orphan_prevents_sibling_collision`).
2. Pairwise non-overlapping Rust ground trait impls migrate 1-to-1 into Aethel's
   `default instance` registry with guaranteed unambiguous resolution (`migrateRustImpls_coherent`).
3. Demonstrates two structural limitations of Rust traits solved by Aethel:
   downstream composition blocked by the orphan rule (`rust_orphan_blocks_downstream_composition`)
   and missing behavioral laws (`rust_trait_admits_unlawful_monoid`).
4. Models imported `@external(rust)` instances honestly via `ForeignRustInstanceSpec`
   without introducing project axioms.
-/

abbrev CrateId := Nat

inductive RustTy where
  | adt0 (krate : CrateId) (tyId : Nat)
  | adt1 (krate : CrateId) (tyId : Nat) (arg : RustTy)
  | adt2 (krate : CrateId) (tyId : Nat) (arg1 arg2 : RustTy)
  | fundamentalBox (inner : RustTy)
  | fundamentalRef (isMut : Bool) (inner : RustTy)
  | param (idx : Nat)
  deriving Repr, DecidableEq

structure RustTraitRef where
  traitCrate : CrateId
  traitId : Nat
  inputTys : List RustTy
  deriving Repr, DecidableEq

def RustTy.hasParam : RustTy → Bool
  | .adt0 _ _ => false
  | .adt1 _ _ arg => arg.hasParam
  | .adt2 _ _ arg1 arg2 => arg1.hasParam || arg2.hasParam
  | .fundamentalBox inner => inner.hasParam
  | .fundamentalRef _ inner => inner.hasParam
  | .param _ => true

def RustTraitRef.isGround (tr : RustTraitRef) : Bool :=
  !tr.inputTys.any RustTy.hasParam

/-- Walks fundamental wrappers (`Box`, `&`, `&mut`) to check whether a nominal
type owned by `localCrate` covers any type parameter in this trait input type. -/
def coversLocalBeforeParam (localCrate : CrateId) : RustTy → Bool
  | .adt0 c _ => c == localCrate
  | .adt1 c _ _ => c == localCrate
  | .adt2 c _ _ _ => c == localCrate
  | .fundamentalBox inner => coversLocalBeforeParam localCrate inner
  | .fundamentalRef _ inner => coversLocalBeforeParam localCrate inner
  | .param _ => false

/-- Models `orphan_check_trait_ref` (local non-fundamental trait rule): an `impl`
in `localCrate` is accepted iff the trait itself is local OR some input parameter
reaches a type owned by `localCrate` through fundamental wrappers without encountering
an earlier uncovered generic type parameter (`coherence.rs:131-151`). -/
def orphanCheckLocal.scan (localCrate : CrateId) : List RustTy → Bool
  | [] => false
  | ty :: rest =>
    if coversLocalBeforeParam localCrate ty then true
    else if ty.hasParam then false
    else orphanCheckLocal.scan localCrate rest

def orphanCheckLocal (localCrate : CrateId) : RustTraitRef → Bool
  | ⟨tCrate, _, inputs⟩ =>
    if tCrate == localCrate then true
    else orphanCheckLocal.scan localCrate inputs

def RustTy.AllCratesIn (allowed : CrateId → Prop) : RustTy → Prop
  | .adt0 c _ => allowed c
  | .adt1 c _ arg => allowed c ∧ arg.AllCratesIn allowed
  | .adt2 c _ a1 a2 => allowed c ∧ a1.AllCratesIn allowed ∧ a2.AllCratesIn allowed
  | .fundamentalBox inner => inner.AllCratesIn allowed
  | .fundamentalRef _ inner => inner.AllCratesIn allowed
  | .param _ => True

def RustTraitRef.AllCratesIn (allowed : CrateId → Prop) (tr : RustTraitRef) : Prop :=
  allowed tr.traitCrate ∧ ∀ t ∈ tr.inputTys, t.AllCratesIn allowed

theorem coversLocal_implies_allowed_has {localCrate : CrateId} {allowed : CrateId → Prop}
    {ty : RustTy} (hCov : coversLocalBeforeParam localCrate ty = true)
    (hAllow : ty.AllCratesIn allowed) :
    allowed localCrate := by
  induction ty with
  | adt0 c _ =>
    simp only [coversLocalBeforeParam, beq_iff_eq] at hCov
    subst hCov
    exact hAllow
  | adt1 c _ _ _ =>
    simp only [coversLocalBeforeParam, beq_iff_eq] at hCov
    subst hCov
    exact hAllow.1
  | adt2 c _ _ _ _ _ =>
    simp only [coversLocalBeforeParam, beq_iff_eq] at hCov
    subst hCov
    exact hAllow.1
  | fundamentalBox _ ih => exact ih hCov hAllow
  | fundamentalRef _ _ ih => exact ih hCov hAllow
  | param _ => simp [coversLocalBeforeParam] at hCov

private theorem scan_implies_allowed {localCrate : CrateId} {allowed : CrateId → Prop}
    {tys : List RustTy}
    (hScan : orphanCheckLocal.scan localCrate tys = true)
    (hAllow : ∀ t ∈ tys, t.AllCratesIn allowed) :
    allowed localCrate := by
  induction tys with
  | nil => simp [orphanCheckLocal.scan] at hScan
  | cons ty rest ih =>
    simp only [orphanCheckLocal.scan] at hScan
    by_cases hCov : coversLocalBeforeParam localCrate ty = true
    · exact coversLocal_implies_allowed_has hCov (hAllow ty List.mem_cons_self)
    · have hCovFalse : coversLocalBeforeParam localCrate ty = false := Bool.eq_false_iff.mpr hCov
      simp only [hCovFalse, Bool.false_eq_true, ↓reduceIte] at hScan
      by_cases hParam : ty.hasParam = true
      · simp [hParam] at hScan
      · have hParamFalse : ty.hasParam = false := Bool.eq_false_iff.mpr hParam
        simp only [hParamFalse, Bool.false_eq_true, ↓reduceIte] at hScan
        exact ih hScan (fun t ht => hAllow t (List.mem_cons_of_mem _ ht))

theorem orphanCheckLocal_implies_crate_owns {localCrate : CrateId}
    {allowed : CrateId → Prop} {tr : RustTraitRef}
    (hOrphan : orphanCheckLocal localCrate tr = true)
    (hAllow : tr.AllCratesIn allowed) :
    allowed localCrate := by
  cases tr with
  | mk tCrate tId inputs =>
    dsimp [orphanCheckLocal] at hOrphan
    by_cases hTC : tCrate = localCrate
    · rw [← hTC]
      exact hAllow.1
    · have hBeq : (tCrate == localCrate) = false := beq_false_of_ne hTC
      simp only [hBeq, Bool.false_eq_true, ↓reduceIte] at hOrphan
      exact scan_implies_allowed hOrphan hAllow.2

/-- Link-safety theorem (`coherence.rs:166`): two mutually-independent crates
(`c1` absent from `allow2`) can never both own the same `RustTraitRef`. -/
theorem rust_orphan_prevents_sibling_collision {c1 : CrateId}
    {allow1 allow2 : CrateId → Prop}
    (hDisj1 : ¬ allow2 c1)
    {tr : RustTraitRef}
    (hOrph1 : orphanCheckLocal c1 tr = true)
    (_hFrom1 : tr.AllCratesIn allow1)
    (hFrom2 : tr.AllCratesIn allow2) :
    False := by
  exact hDisj1 (orphanCheckLocal_implies_crate_owns hOrph1 hFrom2)

/-! ### Part B: 1-to-1 Coherent Rust $\hookrightarrow$ Aethel Migration -/

structure GroundRustImpl where
  implId : InstanceId
  traitId : TraitId
  typeKey : TypeKey
  crateId : CrateId
  deriving Repr, DecidableEq

def GroundRustImpl.toAethelDefault (r : GroundRustImpl) : InstanceEntry :=
  ⟨r.implId, r.traitId, r.typeKey, r.crateId, true⟩

def migrateRustImpls (impls : List GroundRustImpl) : InstanceRegistry :=
  impls.map GroundRustImpl.toAethelDefault

def RustImplsNonOverlapping (impls : List GroundRustImpl) : Prop :=
  impls.Pairwise fun a b => a.traitId ≠ b.traitId ∨ a.typeKey ≠ b.typeKey

private theorem migrateRustImpls_nodup {impls : List GroundRustImpl}
    (hNoOverlap : RustImplsNonOverlapping impls) :
    (migrateRustImpls impls).Nodup := by
  dsimp [migrateRustImpls]
  induction impls with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons]
    have hPair := List.pairwise_cons.mp hNoOverlap
    refine ⟨?_, ih hPair.2⟩
    intro hIn
    obtain ⟨y, hyMem, hyEq⟩ := List.mem_map.mp hIn
    have hDiff := hPair.1 y hyMem
    have hTr : y.traitId = x.traitId := congrArg InstanceEntry.traitId hyEq
    have hTy : y.typeKey = x.typeKey := congrArg InstanceEntry.typeKey hyEq
    rcases hDiff with hT | hK
    · exact hT hTr.symm
    · exact hK hTy.symm

theorem migrateRustImpls_coherent {impls : List GroundRustImpl}
    (hNoOverlap : RustImplsNonOverlapping impls)
    {r : GroundRustImpl} (hMem : r ∈ impls) :
    resolveDefault (migrateRustImpls impls) r.traitId r.typeKey = some r.toAethelDefault := by
  apply resolveDefault_complete (migrateRustImpls_nodup hNoOverlap)
  refine ⟨List.mem_map_of_mem hMem, rfl, rfl, rfl, ?_⟩
  intro other hOtherMem hTr hTy _
  obtain ⟨y, hyMem, rfl⟩ := List.mem_map.mp hOtherMem
  obtain ⟨i, hi, atY⟩ := List.mem_iff_getElem.mp hyMem
  obtain ⟨j, hj, atR⟩ := List.mem_iff_getElem.mp hMem
  have hPair := List.pairwise_iff_getElem.mp hNoOverlap
  rcases Nat.lt_trichotomy i j with hLt | rfl | hGt
  · have hDiff := hPair i j hi hj hLt
    rw [atY, atR] at hDiff
    rcases hDiff with hT | hK
    · exact False.elim (hT hTr)
    · exact False.elim (hK hTy)
  · rw [atY] at atR
    rw [atR]
  · have hDiff := hPair j i hj hi hGt
    rw [atR, atY] at hDiff
    rcases hDiff with hT | hK
    · exact False.elim (hT hTr.symm)
    · exact False.elim (hK hTy.symm)

/-! ### Part C: Why Aethel Goes Beyond Rust Traits (Orphan Composition + Laws) -/

theorem rust_orphan_blocks_downstream_composition :
    let upstreamTraitCrate := 0
    let upstreamTypeCrate := 1
    let appCrate := 2
    let toJsonOnFoo : RustTraitRef := ⟨upstreamTraitCrate, 42, [.adt0 upstreamTypeCrate 7]⟩
    orphanCheckLocal appCrate toJsonOnFoo = false ∧
    resolveDefault [⟨1, 42, 7, appCrate, true⟩] 42 7 = some ⟨1, 42, 7, appCrate, true⟩ := by
  decide

theorem rust_trait_admits_unlawful_monoid :
    ∃ (empty : Nat) (combine : Nat → Nat → Nat),
      empty = 1 ∧ combine = (· + ·) ∧ ¬ (∀ x : Nat, combine empty x = x) :=
  ⟨1, (· + ·), rfl, rfl, badAddEmptyOne_not_left_id⟩

/-! ### Part D: Explicit `ForeignTraitContract` Boundary (Zero Project Axioms) -/

structure ForeignRustInstanceSpec (LawProp : Prop) where
  instanceName : String
  rustCrate : String
  rustTarget : String

theorem verifyModuloForeignContract {LawProp : Prop}
    (_spec : ForeignRustInstanceSpec LawProp) (contract : LawProp) : LawProp :=
  contract

end Aethel.RustTraitBridge
