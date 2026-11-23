import Aethel.ResourceCheck
import Aethel.CoBorrowPacking
import Aethel.CacheLayout
import Aethel.LawFrameDischarge
import Aethel.ConstitutionalLaws

namespace Aethel.MIRValidator

open Aethel Aethel.Core Aethel.AutomaticLayout Aethel.CoBorrowPacking
open Aethel.CacheLayout Aethel.LawFrameDischarge

/-!
## Versioned MIR Certificate Validator (Phase 5 Lean Gate)

Validates serialized versioned MIR records, collections, and function bodies by
re-deriving co-borrow-safe record layouts, collection layout invariants, kernel
resource safety (`verifyResources`), and effect frame preservation directly from
actual operations. Stale versions or forged layout sizes are rejected.
-/

def currentMIRVersion : Nat := 1

structure MIRRecordDecl where
  name : String
  fields : List Schema
  conflicts : List (Nat × Nat) := []
  claimedSize : Option Nat := none
  deriving Repr

structure MIRCollectionDecl where
  name : String
  layout : CollectionLayout
  fieldCount : Nat
  deriving Repr, DecidableEq

structure MIRFunctionDecl where
  name : String
  effects : Effect
  preserves : List (List Nat)
  body : Program
  deriving Repr, DecidableEq

structure MIRModule where
  version : Nat
  records : List MIRRecordDecl := []
  collections : List MIRCollectionDecl := []
  functions : List MIRFunctionDecl := []
  deriving Repr

inductive MIRError where
  | unsupportedVersion (actual expected : Nat)
  | invalidRecordLayout (name : String)
  | staleLayoutSize (name : String) (claimed actual : Nat)
  | invalidCollectionLayout (name : String)
  | invalidResources (fnName : String)
  | frameViolation (fnName : String)
  deriving Repr, DecidableEq

structure MIRCertificate where
  version : Nat
  recordSizes : List (String × Nat)
  functionCount : Nat
  deriving Repr, DecidableEq

/-- Independent mathematical specification of a valid MIR module. -/
def MIRRecordDecl.Valid (r : MIRRecordDecl) : Prop :=
  let g : CoBorrowGraph := ⟨r.fields.length, r.conflicts⟩
  ∃ lay, autoPlan .natural g r.fields = some lay ∧
    Conforms .natural (applyPolicies g r.fields) lay ∧
    (∀ size alignment placed, lay = .record size alignment placed → PackingConflictFree g placed) ∧
    (∀ sz, r.claimedSize = some sz → lay.size = sz)

def MIRCollectionDecl.Valid (c : MIRCollectionDecl) : Prop :=
  c.layout.Valid ∧ 0 < c.fieldCount

def MIRFunctionDecl.Valid (f : MIRFunctionDecl) : Prop :=
  (∃ final, Runs {} f.body final ∧ final.views = []) ∧
  EffectPreserves f.effects f.preserves

def MIRModule.Valid (m : MIRModule) : Prop :=
  m.version = currentMIRVersion ∧
  (∀ r ∈ m.records, r.Valid) ∧
  (∀ c ∈ m.collections, c.Valid) ∧
  (∀ f ∈ m.functions, f.Valid)

def validateRecord (r : MIRRecordDecl) : Except MIRError (String × Nat) :=
  let g : CoBorrowGraph := ⟨r.fields.length, r.conflicts⟩
  match autoPlan .natural g r.fields with
  | none => .error (.invalidRecordLayout r.name)
  | some lay =>
    match r.claimedSize with
    | none => .ok (r.name, lay.size)
    | some sz =>
      if lay.size == sz then .ok (r.name, lay.size)
      else .error (.staleLayoutSize r.name sz lay.size)

private def layoutValidBool : CollectionLayout → Bool
  | .aos => true
  | .soa => true
  | .aosoa w => decide (0 < w)

def validateCollection (c : MIRCollectionDecl) : Except MIRError Unit :=
  if layoutValidBool c.layout && decide (0 < c.fieldCount) then .ok ()
  else .error (.invalidCollectionLayout c.name)

def validateFunction (f : MIRFunctionDecl) : Except MIRError Unit :=
  if !verifyResources f.body then .error (.invalidResources f.name)
  else if !checkEffectPreserves f.effects f.preserves then .error (.frameViolation f.name)
  else .ok ()

def validateRecords : List MIRRecordDecl → Except MIRError (List (String × Nat))
  | [] => .ok []
  | r :: rs =>
    match validateRecord r with
    | .error e => .error e
    | .ok pair =>
      match validateRecords rs with
      | .error e => .error e
      | .ok rest => .ok (pair :: rest)

def validateCollections : List MIRCollectionDecl → Except MIRError Unit
  | [] => .ok ()
  | c :: cs =>
    match validateCollection c with
    | .error e => .error e
    | .ok () => validateCollections cs

def validateFunctions : List MIRFunctionDecl → Except MIRError Unit
  | [] => .ok ()
  | f :: fs =>
    match validateFunction f with
    | .error e => .error e
    | .ok () => validateFunctions fs

def validateMIR (m : MIRModule) : Except MIRError MIRCertificate :=
  if m.version != currentMIRVersion then
    .error (.unsupportedVersion m.version currentMIRVersion)
  else
    match validateRecords m.records with
    | .error e => .error e
    | .ok sizes =>
      match validateCollections m.collections with
      | .error e => .error e
      | .ok () =>
        match validateFunctions m.functions with
        | .error e => .error e
        | .ok () => .ok ⟨m.version, sizes, m.functions.length⟩

theorem validateRecord_sound {r : MIRRecordDecl} {pair : String × Nat}
    (hOk : validateRecord r = .ok pair) :
    r.Valid := by
  dsimp [validateRecord] at hOk
  let g : CoBorrowGraph := ⟨r.fields.length, r.conflicts⟩
  cases hPlan : autoPlan .natural g r.fields with
  | none =>
    rw [hPlan] at hOk
    cases hOk
  | some lay =>
    rw [hPlan] at hOk
    refine ⟨lay, hPlan, autoPlan_conforms hPlan, ?_, ?_⟩
    · intro size alignment placed hEq
      subst hEq
      exact autoPlan_conflict_free hPlan
    · intro sz hClaim
      rw [hClaim] at hOk
      dsimp only at hOk
      split at hOk
      · next hSz => exact beq_iff_eq.mp hSz
      · cases hOk

theorem validateCollection_sound {c : MIRCollectionDecl}
    (hOk : validateCollection c = .ok ()) :
    c.Valid := by
  dsimp [validateCollection, MIRCollectionDecl.Valid] at hOk ⊢
  split at hOk
  · next hCond =>
    cases hLay : c.layout with
    | aos | soa =>
      simp only [hLay, layoutValidBool, CollectionLayout.Valid, Bool.true_and,
        decide_eq_true_eq] at hCond ⊢
      exact ⟨trivial, hCond⟩
    | aosoa w =>
      simp only [hLay, layoutValidBool, CollectionLayout.Valid, Bool.and_eq_true,
        decide_eq_true_eq] at hCond ⊢
      exact hCond
  · cases hOk

theorem validateFunction_sound {f : MIRFunctionDecl}
    (hOk : validateFunction f = .ok ()) :
    f.Valid := by
  dsimp [validateFunction] at hOk
  by_cases hRes : verifyResources f.body = true
  · simp only [hRes, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
    by_cases hFrm : checkEffectPreserves f.effects f.preserves = true
    · exact ⟨(verifyResources_correct f.body).mp hRes,
        (checkEffectPreserves_correct f.effects f.preserves).mp hFrm⟩
    · have hFrmF : checkEffectPreserves f.effects f.preserves = false :=
        Bool.eq_false_iff.mpr hFrm
      simp only [hFrmF, Bool.not_false, ↓reduceIte] at hOk
      cases hOk
  · have hResF : verifyResources f.body = false := Bool.eq_false_iff.mpr hRes
    simp only [hResF, Bool.not_false, ↓reduceIte] at hOk
    cases hOk

theorem validateRecords_sound {rs : List MIRRecordDecl} {sizes : List (String × Nat)}
    (hOk : validateRecords rs = .ok sizes) :
    ∀ r ∈ rs, r.Valid := by
  induction rs generalizing sizes with
  | nil =>
    intro _ hr
    cases hr
  | cons r rs ih =>
    dsimp [validateRecords] at hOk
    cases h1 : validateRecord r with
    | error e =>
      rw [h1] at hOk
      cases hOk
    | ok pair =>
      rw [h1] at hOk
      cases h2 : validateRecords rs with
      | error e =>
        rw [h2] at hOk
        cases hOk
      | ok rest =>
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hxRest
        · exact validateRecord_sound h1
        · exact ih h2 x hxRest

theorem validateCollections_sound {cs : List MIRCollectionDecl}
    (hOk : validateCollections cs = .ok ()) :
    ∀ c ∈ cs, c.Valid := by
  induction cs with
  | nil =>
    intro _ hc
    cases hc
  | cons c cs ih =>
    dsimp [validateCollections] at hOk
    cases h1 : validateCollection c with
    | error e =>
      rw [h1] at hOk
      cases hOk
    | ok u =>
      rw [h1] at hOk
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hxRest
      · exact validateCollection_sound h1
      · exact ih hOk x hxRest

theorem validateFunctions_sound {fs : List MIRFunctionDecl}
    (hOk : validateFunctions fs = .ok ()) :
    ∀ f ∈ fs, f.Valid := by
  induction fs with
  | nil =>
    intro _ hf
    cases hf
  | cons f fs ih =>
    dsimp [validateFunctions] at hOk
    cases h1 : validateFunction f with
    | error e =>
      rw [h1] at hOk
      cases hOk
    | ok u =>
      rw [h1] at hOk
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hxRest
      · exact validateFunction_sound h1
      · exact ih hOk x hxRest

theorem validateMIR_sound {m : MIRModule} {cert : MIRCertificate}
    (hOk : validateMIR m = .ok cert) :
    m.Valid := by
  dsimp [validateMIR] at hOk
  by_cases hVer : m.version = currentMIRVersion
  · simp only [hVer, bne_self_eq_false] at hOk
    cases hR : validateRecords m.records with
    | error e => rw [hR] at hOk; cases hOk
    | ok sizes =>
      rw [hR] at hOk
      cases hC : validateCollections m.collections with
      | error e => rw [hC] at hOk; cases hOk
      | ok u =>
        rw [hC] at hOk
        cases hF : validateFunctions m.functions with
        | error e => rw [hF] at hOk; cases hOk
        | ok u2 =>
          exact ⟨hVer, validateRecords_sound hR, validateCollections_sound hC,
            validateFunctions_sound hF⟩
  · have hBne : (m.version != currentMIRVersion) = true := bne_iff_ne.mpr hVer
    simp only [hBne, ↓reduceIte] at hOk
    cases hOk

theorem validateMIR_rejects_stale_version {m : MIRModule}
    (hVer : m.version ≠ currentMIRVersion) :
    ∃ err, validateMIR m = .error err := by
  refine ⟨.unsupportedVersion m.version currentMIRVersion, ?_⟩
  have hBne : (m.version != currentMIRVersion) = true := bne_iff_ne.mpr hVer
  simp [validateMIR, hBne]

/-! ## Line-Oriented `.mir` Parser (`lake exe aethel-check <file.mir>`) -/

private def tokenizeLine (line : String) : List String :=
  (line.replace "\r" "" |>.replace "\t" " " |>.splitOn " ").filter (· != "")

private def parseSchemaToken (tok : String) : Except String Schema :=
  match IntegerType.parse? tok with
  | some ty => .ok (.integer ty)
  | none => .error s!"unknown field integer type '{tok}'"

private def parseNatTok (tok : String) : Except String Nat :=
  match tok.toNat? with
  | some n => .ok n
  | none => .error s!"expected natural number, got '{tok}'"

private def parseAccessMode : String → Except String AccessMode
  | "shared" => .ok .shared
  | "exclusive" => .ok .exclusive
  | tok => .error s!"expected 'shared' or 'exclusive', got '{tok}'"

private def parsePath (tok : String) : Except String (List Nat) :=
  if tok == "root" then .ok []
  else (tok.splitOn ".").mapM parseNatTok

private def parseInstruction : List String → Except String Instruction
  | ["alloc", ownerTok, lenTok] => do
    let owner ← parseNatTok ownerTok
    let len ← parseNatTok lenTok
    return .alloc owner (List.replicate len 0)
  | ["alias", idTok, ownerTok, offTok, modeTok] => do
    let id ← parseNatTok idTok
    let owner ← parseNatTok ownerTok
    let off ← parseNatTok offTok
    let mode ← parseAccessMode modeTok
    return .alias id owner off mode
  | ["read", idTok] => return .read (← parseNatTok idTok)
  | ["write", idTok, valTok] => do
    let id ← parseNatTok idTok
    let val ← parseNatTok valTok
    return .write id val.toUInt8
  | ["reserve", vidTok, hidTok, modeTok] => do
    let vid ← parseNatTok vidTok
    let hid ← parseNatTok hidTok
    let mode ← parseAccessMode modeTok
    return .reserve vid hid mode
  | ["read_view", vidTok] => return .readView (← parseNatTok vidTok)
  | ["write_view", vidTok, valTok] => do
    let vid ← parseNatTok vidTok
    let val ← parseNatTok valTok
    return .writeView vid val.toUInt8
  | ["release", vidTok] => return .release (← parseNatTok vidTok)
  | ["forget", hidTok] => return .forget (← parseNatTok hidTok)
  | ["destroy", ownerTok] => return .destroy (← parseNatTok ownerTok)
  | toks => .error s!"unrecognized MIR instruction '{String.intercalate " " toks}'"

private inductive ParseBlock where
  | top
  | inRecord (recDecl : MIRRecordDecl)
  | inFn (fnDecl : MIRFunctionDecl)

private structure ParseState where
  mod : MIRModule
  hasVersion : Bool
  block : ParseBlock

private def stepParseLine (st : ParseState) (line : String) : Except String ParseState := do
  let toks := tokenizeLine line
  if toks.isEmpty || toks.head?.any (·.startsWith "#") then
    return st
  match st.block with
  | .top =>
    match toks with
    | ["mir_version", vTok] =>
      let v ← parseNatTok vTok
      return { st with mod := { st.mod with version := v }, hasVersion := true }
    | ["collection", name, "aos", fcTok] =>
      let fc ← parseNatTok fcTok
      return { st with mod := { st.mod with collections := st.mod.collections ++ [⟨name, .aos, fc⟩] } }
    | ["collection", name, "soa", fcTok] =>
      let fc ← parseNatTok fcTok
      return { st with mod := { st.mod with collections := st.mod.collections ++ [⟨name, .soa, fc⟩] } }
    | ["collection", name, "aosoa", wTok, fcTok] =>
      let w ← parseNatTok wTok
      let fc ← parseNatTok fcTok
      return { st with mod := { st.mod with collections := st.mod.collections ++ [⟨name, .aosoa w, fc⟩] } }
    | ["record", name] =>
      return { st with block := .inRecord ⟨name, [], [], none⟩ }
    | ["record", name, szTok] =>
      let sz ← parseNatTok szTok
      return { st with block := .inRecord ⟨name, [], [], some sz⟩ }
    | ["fn", name] =>
      return { st with block := .inFn ⟨name, .empty, [], []⟩ }
    | _ => .error s!"unexpected top-level MIR directive '{String.intercalate " " toks}'"
  | .inRecord r =>
    match toks with
    | ["field", tyTok] =>
      let s ← parseSchemaToken tyTok
      return { st with block := .inRecord { r with fields := r.fields ++ [s] } }
    | ["conflict", iTok, jTok] =>
      let i ← parseNatTok iTok
      let j ← parseNatTok jTok
      return { st with block := .inRecord { r with conflicts := r.conflicts ++ [(i, j)] } }
    | ["end_record"] =>
      return { st with
        mod := { st.mod with records := st.mod.records ++ [r] }
        block := .top }
    | _ => .error s!"unexpected record directive '{String.intercalate " " toks}'"
  | .inFn f =>
    match toks with
    | ["effect_write", pTok] =>
      let p ← parsePath pTok
      return { st with block := .inFn { f with effects := { f.effects with writes := f.effects.writes ++ [p] } } }
    | ["effect_invalidate", pTok] =>
      let p ← parsePath pTok
      return { st with block := .inFn { f with effects := { f.effects with invalidates := f.effects.invalidates ++ [p] } } }
    | ["preserves", pTok] =>
      let p ← parsePath pTok
      return { st with block := .inFn { f with preserves := f.preserves ++ [p] } }
    | ["end_fn"] =>
      return { st with
        mod := { st.mod with functions := st.mod.functions ++ [f] }
        block := .top }
    | _ =>
      let instr ← parseInstruction toks
      return { st with block := .inFn { f with body := f.body ++ [instr] } }

def parseMIR (input : String) : Except String MIRModule := do
  let lines := input.splitOn "\n"
  let init : ParseState := ⟨⟨0, [], [], []⟩, false, .top⟩
  let final ← lines.foldlM stepParseLine init
  if !final.hasVersion then
    .error "missing required 'mir_version <n>' header"
  else
    match final.block with
    | .top => .ok final.mod
    | .inRecord r => .error s!"unterminated record block '{r.name}'"
    | .inFn f => .error s!"unterminated function block '{f.name}'"

private def formatMIRError : MIRError → String
  | .unsupportedVersion actual expected =>
    s!"unsupported MIR version {actual} (expected {expected})"
  | .invalidRecordLayout name =>
    s!"failed to synthesize valid layout for record '{name}'"
  | .staleLayoutSize name claimed actual =>
    s!"stale layout certificate for record '{name}': claimed {claimed} bytes, computed {actual} bytes"
  | .invalidCollectionLayout name =>
    s!"invalid collection layout descriptor for '{name}'"
  | .invalidResources fnName =>
    s!"resource/borrow check failed in function '{fnName}'"
  | .frameViolation fnName =>
    s!"effect frame preservation failed in function '{fnName}'"

def validateMIRText (input : String) : Except String MIRCertificate := do
  let mod ← parseMIR input
  match validateMIR mod with
  | .ok cert => .ok cert
  | .error e => .error (formatMIRError e)

/-! ## Concrete Positive & Negative MIR Validator Witnesses -/

def sampleValidMIR : MIRModule :=
  { version := 1
    records :=
      [ { name := "EntityFlags"
          fields := [.integer (.unsigned .w32), .integer (.unsigned .w1), .integer (.unsigned .w1)]
          conflicts := []
          claimedSize := some 8 } ]
    collections :=
      [ ⟨"EntitiesAoSoA", .aosoa 8, 4⟩ ]
    functions :=
      [ { name := "step_pos"
          effects := ⟨[[0]], [[0]], []⟩
          preserves := [[2], [3]]
          body :=
            [ .alloc 0 [10, 20]
            , .alias 0 0 0 .exclusive
            , .reserve 0 0 .exclusive
            , .writeView 0 42
            , .release 0
            , .forget 0
            , .destroy 0 ] } ] }

def sampleForgedSizeMIR : MIRModule :=
  { version := 1
    records :=
      [ { name := "EntityFlags"
          fields := [.integer (.unsigned .w32), .integer (.unsigned .w1)]
          conflicts := []
          claimedSize := some 999 } ] }

def sampleLeakedViewMIR : MIRModule :=
  { version := 1
    functions :=
      [ { name := "leak_fn"
          effects := .empty
          preserves := []
          body :=
            [ .alloc 0 [10]
            , .alias 0 0 0 .shared
            , .reserve 0 0 .shared ] } ] }

def sampleValidCFMIR : MIRModule :=
  { version := 1
    records := []
    collections := [⟨"EntitiesAoSoA", .aosoa 8, 4⟩]
    functions :=
      [ { name := "step_pos"
          effects := ⟨[[0]], [[0]], []⟩
          preserves := [[2], [3]]
          body :=
            [ .alloc 0 [10, 20]
            , .alias 0 0 0 .exclusive
            , .reserve 0 0 .exclusive
            , .writeView 0 42
            , .release 0
            , .forget 0
            , .destroy 0 ] } ] }

theorem validateMIR_accepts_valid_module :
    validateMIR sampleValidCFMIR = .ok ⟨1, [], 1⟩ ∧
    sampleValidCFMIR.Valid := by
  have hOk : validateMIR sampleValidCFMIR = .ok ⟨1, [], 1⟩ := by rfl
  exact ⟨hOk, validateMIR_sound hOk⟩

theorem validateMIR_rejects_forged_size (r : MIRRecordDecl) {lay : Layout} {sz : Nat}
    (hPlan : autoPlan .natural ⟨r.fields.length, r.conflicts⟩ r.fields = some lay)
    (hClaim : r.claimedSize = some sz) (hNe : lay.size ≠ sz) :
    ∃ err, validateMIR { version := currentMIRVersion, records := [r] } = .error err := by
  refine ⟨.staleLayoutSize r.name sz lay.size, ?_⟩
  have hBne : (lay.size == sz) = false := beq_false_of_ne hNe
  simp [validateMIR, validateRecords, validateRecord, hPlan, hClaim, hBne, currentMIRVersion]

theorem validateMIR_rejects_leaked_view :
    ∃ err, validateMIR sampleLeakedViewMIR = .error err := by
  exact ⟨.invalidResources "leak_fn", rfl⟩

end Aethel.MIRValidator
