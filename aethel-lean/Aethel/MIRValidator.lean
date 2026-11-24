import Aethel.ResourceCheck
import Aethel.CoBorrowPacking
import Aethel.CacheLayout
import Aethel.LawFrameDischarge
import Aethel.ConstitutionalLaws
import Aethel.InterprocBorrow
import Aethel.Iteration

namespace Aethel.MIRValidator

open Aethel Aethel.Core Aethel.AutomaticLayout Aethel.CoBorrowPacking
open Aethel.CacheLayout Aethel.LawFrameDischarge Aethel.Permissions Aethel.InterprocBorrow
open Aethel.LawAutoProver

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

structure MIRDynVecDecl where
  name : String
  layout : CollectionLayout
  fieldCount : Nat
  initCap : Nat
  deriving Repr, DecidableEq

def MIRDynVecDecl.Valid (d : MIRDynVecDecl) : Prop :=
  d.layout.Valid ∧ 0 < d.fieldCount ∧ 0 < d.initCap

structure MIRDecreasesCert where
  guards : List LawProp := []
  curMeasure : LawExpr
  nextMeasure : LawExpr
  deriving Repr, DecidableEq

inductive MIRLawKind where
  | always
  | never
  deriving Repr, DecidableEq

structure MIRLawDecl where
  name : String
  kind : MIRLawKind
  hyps : List LawProp := []
  goal : LawProp
  deriving Repr, DecidableEq

structure MIRFunctionDecl where
  name : String
  effects : Effect
  preserves : List (List Nat)
  body : Program
  permAllocSize : Nat := 0
  permTrace : List PermInstr := []
  disjointCerts : List MIRDisjointCert := []
  decreasesCerts : List MIRDecreasesCert := []
  deriving Repr

structure MIRModule where
  version : Nat
  records : List MIRRecordDecl := []
  collections : List MIRCollectionDecl := []
  functions : List MIRFunctionDecl := []
  laws : List MIRLawDecl := []
  deriving Repr

inductive MIRError where
  | unsupportedVersion (actual expected : Nat)
  | invalidRecordLayout (name : String)
  | staleLayoutSize (name : String) (claimed actual : Nat)
  | invalidCollectionLayout (name : String)
  | invalidResources (fnName : String)
  | frameViolation (fnName : String)
  | invalidPermTrace (fnName : String)
  | invalidDisjointCert (fnName : String)
  | invalidDecreasesCert (fnName : String)
  | lawCounterexample (lawName witness : String)
  | unprovedLaw (lawName : String)
  deriving Repr, DecidableEq

structure MIRCertificate where
  version : Nat
  recordSizes : List (String × Nat)
  functionCount : Nat
  lawCount : Nat := 0
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

def MIRDecreasesCert.Valid (d : MIRDecreasesCert) : Prop :=
  ∀ env : Nat → Nat, (∀ h ∈ d.guards, h.Holds env) → d.nextMeasure.eval env < d.curMeasure.eval env

def checkDecreasesCert (d : MIRDecreasesCert) : Bool :=
  autoProveNorm d.guards 12 (.lt d.nextMeasure d.curMeasure)

theorem checkDecreasesCert_sound {d : MIRDecreasesCert}
    (hOk : checkDecreasesCert d = true) : d.Valid :=
  autoProveNorm_sound hOk

theorem decreasesCert_implies_loopWF_progress {S : Type} (cond : S → Bool) (step : S → S)
    (val : S → Nat → Nat) (d : MIRDecreasesCert) (hVal : d.Valid)
    (hRel : ∀ s, cond s = true →
      (∀ h ∈ d.guards, h.Holds (val s)) ∧
      d.curMeasure.eval (val (step s)) = d.nextMeasure.eval (val s)) :
    ∀ s, cond s = true → d.curMeasure.eval (val (step s)) < d.curMeasure.eval (val s) := by
  intro s hs
  obtain ⟨hGuards, hEq⟩ := hRel s hs
  rw [hEq]
  exact hVal (val s) hGuards

private def MIRLawDecl.targetProp (l : MIRLawDecl) : LawProp :=
  match l.kind with
  | .always => l.goal
  | .never => .not l.goal

def MIRLawDecl.Valid (l : MIRLawDecl) : Prop :=
  match l.kind with
  | .always => ∀ env : Nat → Nat, (∀ h ∈ l.hyps, h.Holds env) → l.goal.Holds env
  | .never => ∀ env : Nat → Nat, (∀ h ∈ l.hyps, h.Holds env) → ¬ l.goal.Holds env

def MIRFunctionDecl.Valid (f : MIRFunctionDecl) : Prop :=
  (∃ final, Runs {} f.body final ∧ final.views = []) ∧
  EffectPreserves f.effects f.preserves ∧
  (f.permTrace ≠ [] → PermTraceValid f.permAllocSize f.permTrace) ∧
  (∀ c ∈ f.disjointCerts, c.Valid) ∧
  (∀ d ∈ f.decreasesCerts, d.Valid)

def MIRModule.Valid (m : MIRModule) : Prop :=
  m.version = currentMIRVersion ∧
  (∀ r ∈ m.records, r.Valid) ∧
  (∀ c ∈ m.collections, c.Valid) ∧
  (∀ f ∈ m.functions, f.Valid) ∧
  (∀ l ∈ m.laws, l.Valid)

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

def validateDynVec (d : MIRDynVecDecl) : Except MIRError MIRCollectionDecl :=
  if layoutValidBool d.layout && decide (0 < d.fieldCount) && decide (0 < d.initCap) then
    .ok ⟨d.name, d.layout, d.fieldCount⟩
  else
    .error (.invalidCollectionLayout d.name)

def validateFunction (f : MIRFunctionDecl) : Except MIRError Unit :=
  if !verifyResources f.body then .error (.invalidResources f.name)
  else if !checkEffectPreserves f.effects f.preserves then .error (.frameViolation f.name)
  else if !f.permTrace.isEmpty && !verifyPermTrace f.permAllocSize f.permTrace then .error (.invalidPermTrace f.name)
  else if !f.disjointCerts.all checkDisjointCert then .error (.invalidDisjointCert f.name)
  else if !f.decreasesCerts.all checkDecreasesCert then .error (.invalidDecreasesCert f.name)
  else .ok ()

def validateLaw (l : MIRLawDecl) : Except MIRError Unit :=
  let prop := l.targetProp
  if autoProveNorm l.hyps 12 prop then .ok ()
  else
    match falsifySymbolic 6 l.hyps prop with
    | some (v0, v1, v2) => .error (.lawCounterexample l.name s!"v0={v0}, v1={v1}, v2={v2}")
    | none => .error (.unprovedLaw l.name)

private def validateEach (validate : α → Except MIRError Unit) :
    List α → Except MIRError Unit
  | [] => .ok ()
  | x :: xs => do
    validate x
    validateEach validate xs

def validateRecords (records : List MIRRecordDecl) :
    Except MIRError (List (String × Nat)) :=
  records.mapM validateRecord

def validateCollections := validateEach validateCollection

def validateFunctions := validateEach validateFunction

def validateLaws := validateEach validateLaw

def validateMIR (m : MIRModule) : Except MIRError MIRCertificate :=
  if m.version != currentMIRVersion then
    .error (.unsupportedVersion m.version currentMIRVersion)
  else do
    let sizes ← validateRecords m.records
    validateCollections m.collections
    validateFunctions m.functions
    validateLaws m.laws
    return ⟨m.version, sizes, m.functions.length, m.laws.length⟩

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

theorem validateDynVec_sound {d : MIRDynVecDecl} {c : MIRCollectionDecl}
    (hOk : validateDynVec d = .ok c) :
    d.Valid ∧ c.Valid := by
  dsimp [validateDynVec, MIRDynVecDecl.Valid, MIRCollectionDecl.Valid] at hOk ⊢
  split at hOk
  · next hCond =>
    cases hOk
    cases hLay : d.layout with
    | aos | soa =>
      simp only [hLay, layoutValidBool, CollectionLayout.Valid, Bool.true_and, Bool.and_eq_true,
        decide_eq_true_eq] at hCond ⊢
      exact ⟨⟨trivial, hCond.1, hCond.2⟩, ⟨trivial, hCond.1⟩⟩
    | aosoa w =>
      simp only [hLay, layoutValidBool, CollectionLayout.Valid, Bool.and_eq_true,
        decide_eq_true_eq] at hCond ⊢
      exact ⟨⟨hCond.1.1, hCond.1.2, hCond.2⟩, ⟨hCond.1.1, hCond.1.2⟩⟩
  · cases hOk

private theorem if_err_eq_ok {α ε : Type} (cond : Bool) (err : ε) (k : Except ε α) (v : α)
    (h : (if cond then .error err else k) = .ok v) :
    cond = false ∧ k = .ok v := by
  by_cases hc : cond = true
  · simp [hc] at h
  · have hf : cond = false := Bool.eq_false_iff.mpr hc
    simp [hf] at h
    exact ⟨hf, h⟩

theorem validateFunction_sound {f : MIRFunctionDecl}
    (hOk : validateFunction f = .ok ()) :
    f.Valid := by
  dsimp [validateFunction] at hOk
  obtain ⟨hResF, h1⟩ := if_err_eq_ok _ _ _ _ hOk
  obtain ⟨hFrmF, h2⟩ := if_err_eq_ok _ _ _ _ h1
  obtain ⟨hPermF, h3⟩ := if_err_eq_ok _ _ _ _ h2
  obtain ⟨hDisjF, h4⟩ := if_err_eq_ok _ _ _ _ h3
  obtain ⟨hDecF, _⟩ := if_err_eq_ok _ _ _ _ h4
  have hRes : verifyResources f.body = true := by
    cases hb : verifyResources f.body <;> simp_all
  have hFrm : checkEffectPreserves f.effects f.preserves = true := by
    cases hb : checkEffectPreserves f.effects f.preserves <;> simp_all
  have hDisj : f.disjointCerts.all checkDisjointCert = true := by
    cases hb : f.disjointCerts.all checkDisjointCert <;> simp_all
  have hDec : f.decreasesCerts.all checkDecreasesCert = true := by
    cases hb : f.decreasesCerts.all checkDecreasesCert <;> simp_all
  have hPermSpec : f.permTrace ≠ [] → PermTraceValid f.permAllocSize f.permTrace := by
    intro hNe
    have hEmptyFalse : f.permTrace.isEmpty = false := by
      cases hp : f.permTrace with
      | nil => exact False.elim (hNe hp)
      | cons _ _ => rfl
    by_cases hOkP : verifyPermTrace f.permAllocSize f.permTrace = true
    · exact (verifyPermTrace_correct f.permAllocSize f.permTrace).mp hOkP
    · simp_all
  exact ⟨(verifyResources_correct f.body).mp hRes,
    (checkEffectPreserves_correct f.effects f.preserves).mp hFrm,
    hPermSpec,
    fun c hc => checkDisjointCert_sound (List.all_eq_true.mp hDisj c hc),
    fun d hd => checkDecreasesCert_sound (List.all_eq_true.mp hDec d hd)⟩

theorem validateLaw_sound {l : MIRLawDecl}
    (hOk : validateLaw l = .ok ()) : l.Valid := by
  dsimp [validateLaw] at hOk
  by_cases hPrv : autoProveNorm l.hyps 12 l.targetProp = true
  · have hSpec := autoProveNorm_sound hPrv
    cases hk : l.kind <;>
      simpa [MIRLawDecl.Valid, MIRLawDecl.targetProp, LawProp.Holds, hk] using hSpec
  · simp only [hPrv, Bool.false_eq_true, ↓reduceIte] at hOk
    cases hFal : falsifySymbolic 6 l.hyps l.targetProp <;> rw [hFal] at hOk <;> cases hOk

theorem validateLaw_counterexample_refutes {l : MIRLawDecl} {w : String}
    (hErr : validateLaw l = .error (.lawCounterexample l.name w)) : ¬ l.Valid := by
  dsimp [validateLaw] at hErr
  by_cases hPrv : autoProveNorm l.hyps 12 l.targetProp = true
  · simp [hPrv] at hErr
  · simp only [hPrv, Bool.false_eq_true, ↓reduceIte] at hErr
    cases hFal : falsifySymbolic 6 l.hyps l.targetProp with
    | none => rw [hFal] at hErr; cases hErr
    | some triple =>
      obtain ⟨v0, v1, v2⟩ := triple
      have hNot := falsifySymbolic_sound hFal
      cases hk : l.kind <;>
        simpa [MIRLawDecl.Valid, MIRLawDecl.targetProp, LawProp.Holds, hk] using hNot

private theorem validateMap_sound {validate : α → Except MIRError β} {Valid : α → Prop}
    (sound : ∀ {x value}, validate x = .ok value → Valid x)
    {xs : List α} {values : List β} (ok : xs.mapM validate = .ok values) :
    ∀ x ∈ xs, Valid x := by
  induction xs generalizing values with
  | nil => simp
  | cons x xs ih =>
    cases checked : validate x with
    | error err => simp [List.mapM_cons, checked, bind, Except.bind] at ok
    | ok value =>
      cases tail : xs.mapM validate with
      | error err => simp [List.mapM_cons, checked, tail, bind, Except.bind] at ok
      | ok rest =>
        simpa only [List.forall_mem_cons] using And.intro (sound checked) (ih tail)

private theorem validateEach_sound {validate : α → Except MIRError Unit} {Valid : α → Prop}
    (sound : ∀ {x}, validate x = .ok () → Valid x)
    {xs : List α} (ok : validateEach validate xs = .ok ()) :
    ∀ x ∈ xs, Valid x := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases checked : validate x with
    | error err => simp [validateEach, checked, bind, Except.bind] at ok
    | ok value =>
      cases value
      simpa only [List.forall_mem_cons] using
        And.intro (sound checked) (ih (by simpa [validateEach, checked, bind, Except.bind] using ok))

theorem validateRecords_sound {rs : List MIRRecordDecl} {sizes : List (String × Nat)}
    (hOk : validateRecords rs = .ok sizes) :
    ∀ r ∈ rs, r.Valid :=
  validateMap_sound (fun h => validateRecord_sound h) hOk

theorem validateCollections_sound {cs : List MIRCollectionDecl}
    (hOk : validateCollections cs = .ok ()) :
    ∀ c ∈ cs, c.Valid :=
  validateEach_sound (fun h => validateCollection_sound h) hOk

theorem validateFunctions_sound {fs : List MIRFunctionDecl}
    (hOk : validateFunctions fs = .ok ()) :
    ∀ f ∈ fs, f.Valid :=
  validateEach_sound (fun h => validateFunction_sound h) hOk

theorem validateLaws_sound {ls : List MIRLawDecl}
    (hOk : validateLaws ls = .ok ()) :
    ∀ l ∈ ls, l.Valid :=
  validateEach_sound (fun h => validateLaw_sound h) hOk

theorem validateMIR_sound {m : MIRModule} {cert : MIRCertificate}
    (hOk : validateMIR m = .ok cert) :
    m.Valid := by
  simp only [validateMIR, bind, Except.bind] at hOk
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
          rw [hF] at hOk
          cases hL : validateLaws m.laws with
          | error e => rw [hL] at hOk; cases hOk
          | ok u3 =>
            exact ⟨hVer, validateRecords_sound hR, validateCollections_sound hC,
              validateFunctions_sound hF, validateLaws_sound hL⟩
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

private def parseBorrowPerm : String → Except String BorrowPerm
  | "shared" => .ok .shared
  | "reserved" => .ok .reserved
  | "exclusive" | "active_exclusive" => .ok .activeExclusive
  | "frozen" => .ok .frozen
  | tok => .error s!"expected 'shared', 'reserved', 'exclusive', or 'frozen', got '{tok}'"

private def parseIdxAtom (tok : String) : Except String IdxExpr :=
  match tok.splitOn "v" with
  | ["", rest] => return .value (← parseNatTok rest)
  | _ => return .const (← parseNatTok tok)

private def parseIdxExpr (tok : String) : Except String IdxExpr := do
  let parts := tok.splitOn "+"
  let atoms ← parts.mapM parseIdxAtom
  match atoms with
  | [] => .error s!"empty index expression '{tok}'"
  | a :: rest => return rest.foldl .add a

private def parseVarIdTok (tok : String) : Except String Nat :=
  match tok.splitOn "v" with
  | ["", rest] => parseNatTok rest
  | _ => parseNatTok tok

private def stepOrderFact (env : OrderFactEnv) (item : String) : Except String OrderFactEnv := do
  match item.splitOn ":" with
  | ["ne", pairTok] =>
    match pairTok.splitOn "," with
    | [aTok, bTok] =>
      let a ← parseIdxExpr aTok
      let b ← parseIdxExpr bTok
      return { env with base := env.base.assumeNe a b }
    | _ => .error s!"expected 'ne:<a>,<b>', got '{item}'"
  | ["lt", pairTok] =>
    match pairTok.splitOn "," with
    | [xTok, yTok] =>
      let x ← parseVarIdTok xTok
      let y ← parseVarIdTok yTok
      return env.assumeLt x y
    | _ => .error s!"expected 'lt:<x>,<y>', got '{item}'"
  | ["le", pairTok] =>
    match pairTok.splitOn "," with
    | [xTok, yTok] =>
      let x ← parseVarIdTok xTok
      let y ← parseVarIdTok yTok
      return env.assumeLe x y
    | _ => .error s!"expected 'le:<x>,<y>', got '{item}'"
  | _ => .error s!"expected order fact 'ne:...', 'lt:...', or 'le:...', got '{item}'"

private def parseOrderFactEnv (tok : String) : Except String OrderFactEnv :=
  if tok == "none" then .ok {}
  else (tok.splitOn ";").foldlM stepOrderFact {}

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

private def parseLawExprFuel : Nat → List String → Except String (LawExpr × List String)
  | 0, _ => .error "law expression exceeded parser depth budget"
  | _, [] => .error "unexpected end of law expression"
  | fuel + 1, tok :: rest =>
    if tok == "add" then do
      let (a, r1) ← parseLawExprFuel fuel rest
      let (b, r2) ← parseLawExprFuel fuel r1
      return (.add a b, r2)
    else if tok == "sub" then do
      let (a, r1) ← parseLawExprFuel fuel rest
      let (b, r2) ← parseLawExprFuel fuel r1
      return (.sub a b, r2)
    else if tok == "mul" then do
      match rest with
      | cTok :: r0 =>
        let c ← parseNatTok cTok
        let (e, r1) ← parseLawExprFuel fuel r0
        return (.mulConst c e, r1)
      | [] => .error "expected constant after 'mul' in law expression"
    else if tok == "min" then do
      let (a, r1) ← parseLawExprFuel fuel rest
      let (b, r2) ← parseLawExprFuel fuel r1
      return (.min a b, r2)
    else if tok == "max" then do
      let (a, r1) ← parseLawExprFuel fuel rest
      let (b, r2) ← parseLawExprFuel fuel r1
      return (.max a b, r2)
    else
      match tok.splitOn "v" with
      | ["", nTok] => do
        let n ← parseNatTok nTok
        return (.var n, rest)
      | _ => do
        let n ← parseNatTok tok
        return (.const n, rest)

private def parseLawPropFuel : Nat → List String → Except String (LawProp × List String)
  | 0, _ => .error "law proposition exceeded parser depth budget"
  | _, [] => .error "unexpected end of law proposition"
  | fuel + 1, tok :: rest =>
    if tok == "tt" then return (.tt, rest)
    else if tok == "ff" then return (.ff, rest)
    else if tok == "eq" then do
      let (a, r1) ← parseLawExprFuel (rest.length + 1) rest
      let (b, r2) ← parseLawExprFuel (r1.length + 1) r1
      return (.eq a b, r2)
    else if tok == "ne" then do
      let (a, r1) ← parseLawExprFuel (rest.length + 1) rest
      let (b, r2) ← parseLawExprFuel (r1.length + 1) r1
      return (.ne a b, r2)
    else if tok == "le" then do
      let (a, r1) ← parseLawExprFuel (rest.length + 1) rest
      let (b, r2) ← parseLawExprFuel (r1.length + 1) r1
      return (.le a b, r2)
    else if tok == "lt" then do
      let (a, r1) ← parseLawExprFuel (rest.length + 1) rest
      let (b, r2) ← parseLawExprFuel (r1.length + 1) r1
      return (.lt a b, r2)
    else if tok == "not" then do
      let (p, r1) ← parseLawPropFuel fuel rest
      return (.not p, r1)
    else if tok == "and" then do
      let (p, r1) ← parseLawPropFuel fuel rest
      let (q, r2) ← parseLawPropFuel fuel r1
      return (.and p q, r2)
    else if tok == "or" then do
      let (p, r1) ← parseLawPropFuel fuel rest
      let (q, r2) ← parseLawPropFuel fuel r1
      return (.or p q, r2)
    else if tok == "imp" then do
      let (p, r1) ← parseLawPropFuel fuel rest
      let (q, r2) ← parseLawPropFuel fuel r1
      return (.imp p q, r2)
    else .error s!"unexpected token '{tok}' in law proposition"

private def parseLawPropListFuel : Nat → Nat → List String → Except String (List LawProp × List String)
  | _, 0, toks => return ([], toks)
  | 0, _ + 1, _ => .error "decreases guard list exceeded parser depth budget"
  | fuel + 1, n + 1, toks => do
    let (p, r1) ← parseLawPropFuel (toks.length + 1) toks
    let (ps, r2) ← parseLawPropListFuel fuel n r1
    return (p :: ps, r2)

private def parseLawPropExact (toks : List String) : Except String LawProp := do
  let (p, rest) ← parseLawPropFuel (toks.length + 1) toks
  if rest.isEmpty then return p
  else .error s!"trailing tokens in law proposition: '{String.intercalate " " rest}'"

private def parseDecreasesArgs (toks : List String) : Except String MIRDecreasesCert := do
  match toks with
  | nTok :: rest =>
    let n ← parseNatTok nTok
    let (guards, r1) ← parseLawPropListFuel (n + 1) n rest
    let (curM, r2) ← parseLawExprFuel (r1.length + 1) r1
    let (nextM, r3) ← parseLawExprFuel (r2.length + 1) r2
    if r3.isEmpty then return ⟨guards, curM, nextM⟩
    else .error s!"trailing tokens in decreases certificate: '{String.intercalate " " r3}'"
  | [] => .error "expected guard count after 'decreases'"

private inductive ParseBlock where
  | top
  | inRecord (recDecl : MIRRecordDecl)
  | inFn (fnDecl : MIRFunctionDecl)
  | inLaw (name : String) (kind : MIRLawKind) (hyps : List LawProp) (goal : Option LawProp)

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
    | ["dyn_vec", name, "aos", fcTok, capTok] =>
      let fc ← parseNatTok fcTok
      let cap ← parseNatTok capTok
      match validateDynVec ⟨name, .aos, fc, cap⟩ with
      | .ok c => return { st with mod := { st.mod with collections := st.mod.collections ++ [c] } }
      | .error e => .error s!"invalid dynamic vector '{name}': {reprStr e}"
    | ["dyn_vec", name, "soa", fcTok, capTok] =>
      let fc ← parseNatTok fcTok
      let cap ← parseNatTok capTok
      match validateDynVec ⟨name, .soa, fc, cap⟩ with
      | .ok c => return { st with mod := { st.mod with collections := st.mod.collections ++ [c] } }
      | .error e => .error s!"invalid dynamic vector '{name}': {reprStr e}"
    | ["dyn_vec", name, "aosoa", wTok, fcTok, capTok] =>
      let w ← parseNatTok wTok
      let fc ← parseNatTok fcTok
      let cap ← parseNatTok capTok
      match validateDynVec ⟨name, .aosoa w, fc, cap⟩ with
      | .ok c => return { st with mod := { st.mod with collections := st.mod.collections ++ [c] } }
      | .error e => .error s!"invalid dynamic vector '{name}': {reprStr e}"
    | ["record", name] =>
      return { st with block := .inRecord ⟨name, [], [], none⟩ }
    | ["record", name, szTok] =>
      let sz ← parseNatTok szTok
      return { st with block := .inRecord ⟨name, [], [], some sz⟩ }
    | ["fn", name] =>
      return { st with block := .inFn { name := name, effects := .empty, preserves := [], body := [] } }
    | ["law_always", name] =>
      return { st with block := .inLaw name .always [] none }
    | ["law_never", name] =>
      return { st with block := .inLaw name .never [] none }
    | ["trait_law", name] =>
      return { st with block := .inLaw name .always [] none }
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
    | ["perm_alloc", lenTok] =>
      let len ← parseNatTok lenTok
      return { st with block := .inFn { f with permAllocSize := len } }
    | ["perm_reserve", vidTok, offTok, permTok] =>
      let vid ← parseNatTok vidTok
      let off ← parseNatTok offTok
      let perm ← parseBorrowPerm permTok
      return { st with block := .inFn { f with permTrace := f.permTrace ++ [.reserve vid ⟨0, off⟩ perm] } }
    | ["perm_activate", vidTok] =>
      let vid ← parseNatTok vidTok
      return { st with block := .inFn { f with permTrace := f.permTrace ++ [.activate vid] } }
    | ["perm_freeze", vidTok] =>
      let vid ← parseNatTok vidTok
      return { st with block := .inFn { f with permTrace := f.permTrace ++ [.freeze vid] } }
    | ["perm_read", vidTok] =>
      let vid ← parseNatTok vidTok
      return { st with block := .inFn { f with permTrace := f.permTrace ++ [.read vid] } }
    | ["perm_write", vidTok, valTok] =>
      let vid ← parseNatTok vidTok
      let val ← parseNatTok valTok
      return { st with block := .inFn { f with permTrace := f.permTrace ++ [.write vid val.toUInt8] } }
    | ["perm_release", vidTok] =>
      let vid ← parseNatTok vidTok
      return { st with block := .inFn { f with permTrace := f.permTrace ++ [.release vid] } }
    | ["disjoint_idx", envTok, aTok, bTok] =>
      let env ← parseOrderFactEnv envTok
      let a ← parseIdxExpr aTok
      let b ← parseIdxExpr bTok
      return { st with block := .inFn { f with disjointCerts := f.disjointCerts ++ [⟨env, .idxNe a b⟩] } }
    | ["disjoint_slice", envTok, lo1Tok, hi1Tok, lo2Tok, hi2Tok] =>
      let env ← parseOrderFactEnv envTok
      let lo1 ← parseIdxExpr lo1Tok
      let hi1 ← parseIdxExpr hi1Tok
      let lo2 ← parseIdxExpr lo2Tok
      let hi2 ← parseIdxExpr hi2Tok
      return { st with block := .inFn { f with disjointCerts := f.disjointCerts ++ [⟨env, .sliceDisjoint ⟨lo1, hi1⟩ ⟨lo2, hi2⟩⟩] } }
    | "decreases" :: rest =>
      let dc ← parseDecreasesArgs rest
      return { st with block := .inFn { f with decreasesCerts := f.decreasesCerts ++ [dc] } }
    | ["end_fn"] =>
      return { st with
        mod := { st.mod with functions := st.mod.functions ++ [f] }
        block := .top }
    | _ =>
      let instr ← parseInstruction toks
      return { st with block := .inFn { f with body := f.body ++ [instr] } }
  | .inLaw lname lkind hyps goal =>
    match toks with
    | "hyp" :: rest =>
      let hp ← parseLawPropExact rest
      return { st with block := .inLaw lname lkind (hyps ++ [hp]) goal }
    | "goal" :: rest =>
      let gp ← parseLawPropExact rest
      return { st with block := .inLaw lname lkind hyps (some gp) }
    | ["end_law"] =>
      match goal with
      | some gp =>
        return { st with
          mod := { st.mod with laws := st.mod.laws ++ [⟨lname, lkind, hyps, gp⟩] }
          block := .top }
      | none => .error s!"law '{lname}' missing 'goal' directive before 'end_law'"
    | _ => .error s!"unexpected law directive '{String.intercalate " " toks}'"

def parseMIR (input : String) : Except String MIRModule := do
  let lines := input.splitOn "\n"
  let init : ParseState := ⟨⟨0, [], [], [], []⟩, false, .top⟩
  let final ← lines.foldlM stepParseLine init
  if !final.hasVersion then
    .error "missing required 'mir_version <n>' header"
  else
    match final.block with
    | .top => .ok final.mod
    | .inRecord r => .error s!"unterminated record block '{r.name}'"
    | .inFn f => .error s!"unterminated function block '{f.name}'"
    | .inLaw n _ _ _ => .error s!"unterminated law block '{n}'"

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
  | .invalidPermTrace fnName =>
    s!"two-phase lazy permission trace failed in function '{fnName}'"
  | .invalidDisjointCert fnName =>
    s!"affine index/slice disjointness certificate failed in function '{fnName}'"
  | .invalidDecreasesCert fnName =>
    s!"termination 'decreases' certificate failed in function '{fnName}'"
  | .lawCounterexample lawName witness =>
    s!"constitutional law '{lawName}' falsified at {witness}"
  | .unprovedLaw lawName =>
    s!"constitutional law '{lawName}' could not be proved at Tier 3"

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
    validateMIR sampleValidCFMIR = .ok ⟨1, [], 1, 0⟩ ∧
    sampleValidCFMIR.Valid := by
  have hOk : validateMIR sampleValidCFMIR = .ok ⟨1, [], 1, 0⟩ := by rfl
  exact ⟨hOk, validateMIR_sound hOk⟩

theorem validateMIR_rejects_forged_size (r : MIRRecordDecl) {lay : Layout} {sz : Nat}
    (hPlan : autoPlan .natural ⟨r.fields.length, r.conflicts⟩ r.fields = some lay)
    (hClaim : r.claimedSize = some sz) (hNe : lay.size ≠ sz) :
    ∃ err, validateMIR { version := currentMIRVersion, records := [r] } = .error err := by
  refine ⟨.staleLayoutSize r.name sz lay.size, ?_⟩
  have hBne : (lay.size == sz) = false := beq_false_of_ne hNe
  simp [validateMIR, validateRecords, validateRecord, hPlan, hClaim, hBne, currentMIRVersion, bind, Except.bind]

theorem validateMIR_rejects_leaked_view :
    ∃ err, validateMIR sampleLeakedViewMIR = .error err := by
  exact ⟨.invalidResources "leak_fn", rfl⟩

end Aethel.MIRValidator
