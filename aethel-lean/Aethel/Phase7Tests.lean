import Aethel.CategoricalTraits
import Aethel.RustBorrowBridge
import Aethel.RustTraitBridge
import Aethel.RustComplexABI

namespace Aethel.Phase7.Tests

open Aethel Aethel.Core Aethel.Permissions Aethel.RustFFI
open Aethel.CategoricalTraits Aethel.RustBorrowBridge Aethel.RustTraitBridge Aethel.RustComplexABI

private def require (msg : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError msg)

private def runTraitRegistryTests : IO Unit := do
  -- Open-universe coexistence: default `sum_u32` (id 1) + named `max_u32` (id 2)
  let reg : InstanceRegistry :=
    [ ⟨1, 10, 100, 0, true⟩
    , ⟨2, 10, 100, 1, false⟩ ]
  require "default instance sum resolves"
    (resolveWithUsing reg none 10 100 == some ⟨1, 10, 100, 0, true⟩)
  require "using override max_u32 resolves"
    (resolveWithUsing reg (some 2) 10 100 == some ⟨2, 10, 100, 1, false⟩)

  -- Ambiguous defaults rejected
  let ambReg : InstanceRegistry :=
    [ ⟨1, 10, 100, 0, true⟩
    , ⟨2, 10, 100, 1, true⟩ ]
  require "ambiguous defaults rejected"
    (resolveDefault ambReg 10 100 == none)

  -- Branded container coherence
  require "same branded instance matches" (checkBrandedSameInst 1 1)
  require "different branded instances rejected" (!checkBrandedSameInst 1 2)

  -- Forgetful functor synthesis from Monad -> Applicative -> Functor
  let appOpt := optionMonadTrait.toApplicativeTrait
  let funOpt := optionMonadTrait.toFunctorTrait
  require "Monad-derived Option Functor maps cleanly"
    (funOpt.map (· + 1) (some 41) == some 42)
  require "Monad-derived Option Applicative applies cleanly"
    (appOpt.ap (some (· * 2)) (some 21) == some 42)

  -- Polynomial structural `using` without `newtype`
  let nestedBar : PolyData Nat :=
    .pair (.list [.leaf 3, .constNat 7, .inl (.leaf 5)]) (.inr (.leaf 9))
  require "polynomial structural encoding runs without wrapper"
    (polyEncode (fun n => [n * 2]) nestedBar == [3, 6, 7, 0, 10, 1, 18])

private def runRustBridgeTests : IO Unit := do
  -- rustc_borrowck places conflict checks
  let pFieldA : RustPlace := ⟨0, [.field 0 false]⟩
  let pFieldB : RustPlace := ⟨0, [.field 1 false]⟩
  let pIdxI : RustPlace := ⟨0, [.index 0]⟩
  let pIdxJ : RustPlace := ⟨0, [.index 1]⟩
  let pSlice1 : RustPlace := ⟨0, [.subslice 0 4]⟩
  let pSlice2 : RustPlace := ⟨0, [.subslice 4 8]⟩
  require "distinct Rust struct fields do not conflict"
    (!rustPlacesConflict pFieldA pFieldB .overlap)
  require "disjoint Rust subslices do not conflict"
    (!rustPlacesConflict pSlice1 pSlice2 .overlap)
  require "rustc conservatively rejects dynamic array indices a[i], a[j]"
    (rustPlacesConflict pIdxI pIdxJ .overlap)

  -- Orphan check + coherent migration
  let localImpl : RustTraitRef := ⟨0, 42, [.adt0 1 7]⟩
  require "foreign app crate 2 blocked by Rust orphan rule"
    (!orphanCheckLocal 2 localImpl)
  require "defining crate 1 passes Rust orphan rule"
    (orphanCheckLocal 1 localImpl)
  let migrated := migrateRustImpls [⟨1, 42, 7, 1⟩, ⟨2, 43, 7, 1⟩]
  require "migrated Rust impl resolves as unique Aethel default"
    (resolveDefault migrated 42 7 == some ⟨1, 42, 7, 1, true⟩)

  -- Flat C-ABI struct & Bevy SoA query compatibility
  let posSpec : FlatFieldSpec :=
    ⟨4, 4, by decide, by decide, by decide, by decide⟩
  let flagSpec : FlatFieldSpec :=
    ⟨1, 1, by decide, by decide, by decide, by decide⟩
  let cfgLayout := planFlatStruct [posSpec, flagSpec]
  require "flat C-ABI struct {f32, u8} pads to 8 bytes with 4-byte align"
    (cfgLayout.size == 8 && cfgLayout.alignment == 4)

  let qFields : List SoAQueryField :=
    [⟨0, .exclusive⟩, ⟨1, .exclusive⟩, ⟨2, .shared⟩, ⟨2, .shared⟩]
  require "Bevy split SoA query with 2 exclusive + shared columns validates"
    (checkSoAQueryFields qFields)
  let qBad : List SoAQueryField :=
    [⟨0, .exclusive⟩, ⟨0, .shared⟩]
  require "conflicting exclusive + shared on same SoA column rejected"
    (!checkSoAQueryFields qBad)

  -- 64B AoSoA tile bridge alignment check
  let tileSpec : AoSoATileBridgeSpec :=
    ⟨16, 3, 4, by decide, by decide, by decide, by decide⟩
  require "64B AoSoA tile offset aligns to 64B boundary"
    (aosoaTileByteOffset tileSpec 2 1 0 % 64 == 0)

def run : IO Unit := do
  runTraitRegistryTests
  runRustBridgeTests

end Aethel.Phase7.Tests
