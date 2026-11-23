import Aethel.RecordViews

namespace Aethel.Structured.Records

open Core Functional AutomaticLayout

/-- A source fragment scoped to one allocated record. Reads bind copied
integers. A view's authority is local to its body. -/
inductive RawRecordCode where
  | finish
  | letValue (value : Raw) (body : RawRecordCode)
  | load (path : List Nat) (body : RawRecordCode)
  | store (path : List Nat) (value : Raw) (next : RawRecordCode)
  | branch (condition : Raw) (yes no : RawRecordCode)
  | withView (path : List Nat) (mode : AccessMode) (body next : RawRecordCode)
  deriving Repr

inductive RecordCode : List Ty → Type where
  | finish : RecordCode ctx
  | letValue : Term ctx ty → RecordCode (ty :: ctx) → RecordCode ctx
  | load (path : List Nat) (kind : IntegerType) :
      RecordCode (.integer kind :: ctx) → RecordCode ctx
  | store (path : List Nat) (kind : IntegerType) :
      Term ctx (.integer kind) → RecordCode ctx → RecordCode ctx
  | branch : Term ctx .bool → RecordCode ctx → RecordCode ctx → RecordCode ctx
  | withView : List Nat → AccessMode → RecordCode ctx → RecordCode ctx → RecordCode ctx

inductive RecordError where
  | illTyped (error : TypeError)
  | invalidPath (path : List Nat)
  | outsideView (path : List Nat)
  | borrowConflict
  deriving Repr, DecidableEq

abbrev LexicalScope := Option (List Nat × AccessMode)

private def checkLeaf (record : RecordRef abi schema) (active : LexicalScope)
    (path : List Nat) (mode : AccessMode) : Except RecordError IntegerType := do
  let some field := resolveInteger record.conforms path | .error (.invalidPath path)
  if active.isNone ||
      active.any (fun (root, authority) => root.isPrefixOf path && decide (authority.Allows mode)) then
    return field.kind
  else .error (.outsideView path)

def elaborateRecord (record : RecordRef abi schema) (ctx : List Ty)
    (active : LexicalScope) : RawRecordCode → Except RecordError (RecordCode ctx)
  | .finish => .ok .finish
  | .letValue value body => do
    let bound ← (Functional.elaborate ctx value).mapError .illTyped
    return .letValue bound.term (← elaborateRecord record (bound.ty :: ctx) active body)
  | .load path body => do
    let kind ← checkLeaf record active path .shared
    return .load path kind (← elaborateRecord record (.integer kind :: ctx) active body)
  | .store path value next => do
    let kind ← checkLeaf record active path .exclusive
    let expression ← (Structured.elaborateAs ctx (.integer kind) value).mapError .illTyped
    return .store path kind expression (← elaborateRecord record ctx active next)
  | .branch condition yes no => do
    let expression ← (Structured.elaborateAs ctx .bool condition).mapError .illTyped
    return .branch expression (← elaborateRecord record ctx active yes)
      (← elaborateRecord record ctx active no)
  | .withView path mode body next => do
    if (inferView record.layout path).isNone then .error (.invalidPath path) else
      return .withView path mode (← elaborateRecord record ctx (some (path, mode)) body)
        (← elaborateRecord record ctx active next)

/-- The returned core state retains exactly the entry handles and views. The
ordinary release trace runs before the continuation is allowed to proceed. -/
def releaseScope (entry body : State) (scope : RecordView) : Option State := do
  let closed ← closeView scope body
  if closed.handles = entry.handles ∧ closed.views = entry.views then some closed else none

theorem releaseScope_correct {entry body closed : State} {scope : RecordView}
    (released : releaseScope entry body scope = some closed) :
    closeView scope body = some closed ∧ closed.handles = entry.handles ∧ closed.views = entry.views := by
  simp only [releaseScope, bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq] at released
  obtain ⟨_, traced, restored, rfl⟩ := released
  exact ⟨traced, restored⟩

inductive ViewLease where
  | owned (view : RecordView)
  | inherited (view : RecordView)

def ViewLease.view : ViewLease → RecordView
  | .owned view | .inherited view => view

private def openOwned (record : RecordRef abi schema) (state : State)
    (path : List Nat) (mode : AccessMode) : Option (ViewLease × State) := do
  let (view, opened) ← openView record state path mode
  return (.owned view, opened)

def enterView (record : RecordRef abi schema) (state : State) (active : Option RecordView)
    (path : List Nat) (mode : AccessMode) : Option (ViewLease × State) :=
  match active with
  | some parent =>
    if parent.path.isPrefixOf path then
      (reborrowView parent record state path mode).map fun child => (.inherited child, state)
    else openOwned record state path mode
  | none => openOwned record state path mode

/-- View entry either starts a fresh kernel reservation or narrows the active
parent in place. A covered child cannot fall back to a fresh reservation. -/
inductive Enters (record : RecordRef abi schema) (state : State)
    (path : List Nat) (mode : AccessMode) : Option RecordView → ViewLease → State → Prop where
  | owned (outside : ∀ parent, active = some parent → ¬ parent.path <+: path)
      (opened : openView record state path mode = some (view, next)) :
      Enters record state path mode active (.owned view) next
  | inherited (within : parent.path <+: path)
      (borrowed : reborrowView parent record state path mode = some child) :
      Enters record state path mode (some parent) (.inherited child) state

theorem enterView_correct {record : RecordRef abi schema} {state opened : State}
    {active : Option RecordView} {path : List Nat} {mode : AccessMode} {lease : ViewLease} :
    enterView record state active path mode = some (lease, opened) ↔
      Enters record state path mode active lease opened := by
  constructor
  · intro entered
    cases active with
    | none =>
      simp only [enterView, openOwned, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.exists, Prod.mk.injEq] at entered
      obtain ⟨view, stateAfter, ran, rfl, rfl⟩ := entered
      exact .owned (by simp) ran
    | some parent =>
      by_cases longest : parent.path.isPrefixOf path = true
      · simp only [enterView, ite_eq_left longest, Option.map_eq_some_iff, Prod.mk.injEq] at entered
        obtain ⟨child, borrowed, rfl, rfl⟩ := entered
        exact .inherited (List.isPrefixOf_iff_prefix.mp longest) borrowed
      · simp only [enterView, ite_eq_right longest, openOwned, bind, pure, Option.bind_eq_some_iff,
          Option.some.injEq, Prod.exists, Prod.mk.injEq] at entered
        obtain ⟨view, stateAfter, ran, rfl, rfl⟩ := entered
        refine .owned ?_ ran
        intro candidate eq h
        cases eq
        exact
          longest (List.isPrefixOf_iff_prefix.mpr h)
  · intro entered
    cases entered with
    | owned outside opened =>
      cases active with
      | none => simp [enterView, openOwned, opened, bind, pure]
      | some parent =>
        have missing : parent.path.isPrefixOf path ≠ true :=
          fun h => outside parent rfl (List.isPrefixOf_iff_prefix.mp h)
        simp [enterView, missing, openOwned, opened, bind, pure]
    | inherited within borrowed =>
      simp [enterView, List.isPrefixOf_iff_prefix.mpr within, borrowed]

theorem Enters.preserves_borrow_invariant {record : RecordRef abi schema} {state opened : State}
    {path : List Nat} {mode : AccessMode} {active : Option RecordView} {lease : ViewLease}
    (entered : Enters record state path mode active lease opened) (safe : state.ViewsCompatible) :
    opened.ViewsCompatible := by
  cases entered with
  | owned _ opened => exact openView_preserves_borrow_invariant opened safe
  | inherited _ _ => exact safe

def enterAccess (record : RecordRef abi schema) (state : State)
    (active : Option RecordView) (path : List Nat) (mode : AccessMode) : Option (ViewLease × State) :=
  match active with
  | none => openOwned record state path mode
  | some view => some (.inherited view, state)

theorem enterAccess_infers_owned {record : RecordRef abi schema} {state opened : State}
    {path : List Nat} {mode : AccessMode} {lease : ViewLease}
    (entered : enterAccess record state none path mode = some (lease, opened)) :
    ∃ view, lease = .owned view ∧ openView record state path mode = some (view, opened) := by
  simp only [enterAccess, openOwned, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.exists, Prod.mk.injEq] at entered
  obtain ⟨view, _, opened, rfl, rfl⟩ := entered
  exact ⟨view, rfl, opened⟩

def leaveView (lease : ViewLease) (entry body : State) : Option State :=
  match lease with
  | .owned view => releaseScope entry body view
  | .inherited _ =>
    if body.handles = entry.handles ∧ body.views = entry.views then some body else none

/-- Scope teardown consults the actual kernel release relation for fresh
reservations. The child of a reborrow releases only its lexical authority. -/
inductive Exits (entry body : State) : ViewLease → State → Prop where
  | owned : closeView view body = some closed →
      closed.handles = entry.handles → closed.views = entry.views →
      Exits entry body (.owned view) closed
  | inherited : body.handles = entry.handles → body.views = entry.views →
      Exits entry body (.inherited view) body

theorem leaveView_correct {lease : ViewLease} {entry body closed : State} :
    leaveView lease entry body = some closed ↔ Exits entry body lease closed := by
  constructor
  · intro left
    cases lease with
    | owned view =>
      obtain ⟨released, handles, views⟩ := releaseScope_correct left
      exact .owned released handles views
    | inherited view =>
      simp only [leaveView, Option.ite_none_right_eq_some, Option.some.injEq] at left
      obtain ⟨⟨handles, views⟩, rfl⟩ := left
      exact .inherited handles views
  · intro right
    cases right with
    | owned closed handles views => simp [leaveView, releaseScope, closed, handles, views, bind]
    | inherited handles views => simp [leaveView, handles, views]

theorem Exits.restores_scopes {entry body closed : State} {lease : ViewLease}
    (exit : Exits entry body lease closed) :
    closed.handles = entry.handles ∧ closed.views = entry.views := by
  cases exit <;> exact ⟨by assumption, by assumption⟩

/-- Any inferred scope created for a field operation ends before the next
expression or instruction executes. A load carries only its copied value. -/
def loadField (record : RecordRef abi schema) (state : State) (active : Option RecordView)
    (path : List Nat) : Option (IntegerBits × State) := do
  let (lease, opened) ← enterAccess record state active path .shared
  let targets ← lease.view.targets record path .shared
  let value ← record.read opened path targets
  let closed ← leaveView lease state opened
  return (value, closed)

def storeField (record : RecordRef abi schema) (state : State) (active : Option RecordView)
    (path : List Nat) (value : IntegerBits) : Option State := do
  let (lease, opened) ← enterAccess record state active path .exclusive
  let targets ← lease.view.targets record path .exclusive
  let written ← record.write opened path targets value
  leaveView lease state written

theorem loadField_restores {record : RecordRef abi schema} {state closed : State}
    {active : Option RecordView} {path : List Nat} {value : IntegerBits}
    (loaded : loadField record state active path = some (value, closed)) :
    closed.handles = state.handles ∧ closed.views = state.views := by
  simp only [loadField, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.exists, Prod.mk.injEq] at loaded
  obtain ⟨lease, opened, entered, targets, targeted, _, read, _, left, rfl, rfl⟩ := loaded
  exact (leaveView_correct.mp left).restores_scopes

theorem storeField_restores {record : RecordRef abi schema} {state closed : State}
    {active : Option RecordView} {path : List Nat} {value : IntegerBits}
    (stored : storeField record state active path value = some closed) :
    closed.handles = state.handles ∧ closed.views = state.views := by
  simp only [storeField, bind, Option.bind_eq_some_iff, Prod.exists] at stored
  obtain ⟨lease, opened, entered, targets, targeted, written, changed, left⟩ := stored
  exact (leaveView_correct.mp left).restores_scopes

def runRecord (record : RecordRef abi schema) (env : Env ctx) (state : State)
    (active : Option RecordView) : RecordCode ctx → Option (List IntegerBits × State)
  | .finish => some ([], state)
  | .letValue value body => runRecord record (env.extend (value.eval env)) state active body
  | .load path kind body => do
    let (value, closed) ← loadField record state active path
    if matchesKind : value.1 = kind then
      let localValue := kind.fromBits (matchesKind ▸ value.2)
      let (observations, final) ← runRecord record (env.extend (ty := .integer kind) localValue)
        closed active body
      return (value :: observations, final)
    else none
  | .store path kind value next => do
    let written ← storeField record state active path ⟨kind, kind.toBits (value.eval env)⟩
    runRecord record env written active next
  | .branch condition yes no =>
    if (show Bool from condition.eval env) then runRecord record env state active yes
    else runRecord record env state active no
  | .withView path mode body next => do
    let (lease, opened) ← enterView record state active path mode
    let (inside, afterBody) ← runRecord record env opened (some lease.view) body
    let closed ← leaveView lease state afterBody
    let (after, final) ← runRecord record env closed active next
    return (inside ++ after, final)

def executeRecord (record : RecordRef abi schema) (state : State) (source : RawRecordCode) :
    Except RecordError (List IntegerBits × State) := do
  let code ← elaborateRecord record [] none source
  match runRecord record Env.empty state none code with
  | some result => .ok result
  | none => .error .borrowConflict

/-- Evaluation relates copied values, resource operations, and lexical
scope teardown independently of the structured interpreter. -/
inductive Executes (record : RecordRef abi schema) :
    Env ctx → State → Option RecordView → RecordCode ctx → List IntegerBits → State → Prop where
  | finish : Executes record env state active .finish [] state
  | letValue : Evaluates env expression value →
      Executes record (env.extend value) state active body observations final →
      Executes record env state active (.letValue expression body) observations final
  | load (loaded : loadField record state active path = some (value, closed))
      (kindMatches : value.1 = kind) :
      Executes record (env.extend (ty := .integer kind) (kind.fromBits (kindMatches ▸ value.2)))
        closed active body observations final →
      Executes record env state active (.load path kind body) (value :: observations) final
  | store {expression : Term ctx (.integer kind)} : Evaluates env expression value →
      storeField record state active path ⟨kind, kind.toBits value⟩ = some middle →
      Executes record env middle active next observations final →
      Executes record env state active (.store path kind expression next) observations final
  | branchTrue : Evaluates env condition true →
      Executes record env state active yes observations final →
      Executes record env state active (.branch condition yes no) observations final
  | branchFalse : Evaluates env condition false →
      Executes record env state active no observations final →
      Executes record env state active (.branch condition yes no) observations final
  | withView : Enters record state path mode active lease opened →
      Executes record env opened (some lease.view) body inside afterBody →
      Exits state afterBody lease closed →
      Executes record env closed active next after final →
      Executes record env state active (.withView path mode body next) (inside ++ after) final

theorem runRecord_sound {record : RecordRef abi schema} {env : Env ctx} {state final : State}
    {active : Option RecordView} {code : RecordCode ctx} {observations : List IntegerBits}
    (ran : runRecord record env state active code = some (observations, final)) :
    Executes record env state active code observations final := by
  induction code generalizing state active observations final with
  | finish =>
    cases ran
    exact .finish
  | letValue value _ ih => exact .letValue (value.evaluates env) (ih ran)
  | load path kind body ih =>
    simp only [runRecord, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
      Option.dite_none_right_eq_some, Prod.exists, Prod.mk.injEq] at ran
    obtain ⟨value, closed, read, kindMatches, rest, next, continued, rfl, rfl⟩ := ran
    exact .load read kindMatches (ih continued)
  | store path kind value next ih =>
    simp only [runRecord, bind, Option.bind_eq_some_iff] at ran
    obtain ⟨middle, written, continued⟩ := ran
    exact .store (value.evaluates env) written (ih continued)
  | branch condition yes no hy hn =>
    cases h : condition.eval env <;>
      simp only [runRecord, h, Bool.false_eq_true, ite_false, ite_true] at ran
    · exact .branchFalse (h ▸ condition.evaluates env) (hn ran)
    · exact .branchTrue (h ▸ condition.evaluates env) (hy ran)
  | withView path mode body next hb hn =>
    simp only [runRecord, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
      Prod.exists, Prod.mk.injEq] at ran
    obtain ⟨view, opened, acquired, inside, afterBody, stepped, closed, released,
      after, finished, continued, rfl, rfl⟩ := ran
    exact .withView (enterView_correct.mp acquired) (hb stepped) (leaveView_correct.mp released) (hn continued)

theorem Executes.restores_scopes {record : RecordRef abi schema} {env : Env ctx}
    {state final : State} {active : Option RecordView} {code : RecordCode ctx}
    {observations : List IntegerBits}
    (ran : Executes record env state active code observations final) :
    final.handles = state.handles ∧ final.views = state.views := by
  induction ran with
  | finish => exact ⟨rfl, rfl⟩
  | letValue _ _ ih | branchTrue _ _ ih | branchFalse _ _ ih => exact ih
  | load read _ _ ih =>
    have scopes := loadField_restores read
    exact ⟨ih.1.trans scopes.1, ih.2.trans scopes.2⟩
  | store _ written _ ih =>
    have scopes := storeField_restores written
    exact ⟨ih.1.trans scopes.1, ih.2.trans scopes.2⟩
  | withView _ _ exited _ _ after =>
    have scopes := exited.restores_scopes
    exact ⟨after.1.trans scopes.1, after.2.trans scopes.2⟩

theorem Executes.agrees {record : RecordRef abi schema} {env : Env ctx} {state final : State}
    {active : Option RecordView} {code : RecordCode ctx} {observations : List IntegerBits}
    (execution : Executes record env state active code observations final) :
    runRecord record env state active code = some (observations, final) := by
  induction execution with
  | finish => rfl
  | letValue evaluated _ ih => simp [runRecord, evaluated.agrees, ih]
  | load loaded kindMatches _ ih =>
    simp [runRecord, loaded, kindMatches, ih, bind, pure]
  | store evaluated written _ ih =>
    simp [runRecord, evaluated.agrees, written, ih, bind]
  | branchTrue evaluated _ ih | branchFalse evaluated _ ih =>
    simp [runRecord, evaluated.agrees, ih]
  | withView opened _ exited _ inside after =>
    simp [runRecord, enterView_correct.mpr opened, leaveView_correct.mpr exited, inside, after, bind, pure]

theorem runRecord_correct {record : RecordRef abi schema} {env : Env ctx} {state final : State}
    {active : Option RecordView} {code : RecordCode ctx} {observations : List IntegerBits} :
    runRecord record env state active code = some (observations, final) ↔
      Executes record env state active code observations final :=
  ⟨runRecord_sound, Executes.agrees⟩

theorem executeRecord_restores_scopes {record : RecordRef abi schema} {state final : State}
    {source : RawRecordCode} {observations : List IntegerBits}
    (executed : executeRecord record state source = .ok (observations, final)) :
    final.handles = state.handles ∧ final.views = state.views := by
  cases h : elaborateRecord record [] none source with
  | error e => simp [executeRecord, bind, Except.bind, h] at executed
  | ok code =>
    cases r : runRecord record Env.empty state none code with
    | none => simp [executeRecord, bind, Except.bind, h, r] at executed
    | some result =>
      simp only [executeRecord, bind, Except.bind, h, r, Except.ok.injEq] at executed
      have ran := runRecord_sound (r.trans (congrArg some executed))
      exact ran.restores_scopes

end Aethel.Structured.Records
