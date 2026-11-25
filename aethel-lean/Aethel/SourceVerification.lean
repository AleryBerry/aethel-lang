import Aethel.SourceSyntax
import Lean.Data.Json.Parser

namespace Aethel.SourceVerification

open Core Functional Structured Lean

/-- Name resolution is relative to the current record parameter and to the
field paths named in that function's access contract. -/
def FieldAt (source : Source) (root : String) (paths : List String)
    (path : FieldPath) (offset : Nat) : Prop :=
  path.root = root ∧ path.field ∈ paths ∧
    ∃ value, source.fields[offset]? = some (path.field, value)

private def ContractSlot (source : Source) (paths : List String) (offset : Nat) : Prop :=
  ∃ field value, source.fields[offset]? = some (field, value) ∧ field ∈ paths

inductive StoresAt (source : Source) (root : String) (paths : List String) :
    SourceStoreTask → StoreTask → Prop where
  | done : StoresAt source root paths [] []
  | next : FieldAt source root paths field offset → StoresAt source root paths tail resolved →
      StoresAt source root paths ((field, value) :: tail) ((offset, value) :: resolved)

inductive TasksAt (source : Source) (root : String) (paths : List String) :
    List SourceStoreTask → List StoreTask → Prop where
  | empty : TasksAt source root paths [] []
  | next : StoresAt source root paths task resolved → TasksAt source root paths tail loweredTail →
      TasksAt source root paths (task :: tail) (resolved :: loweredTail)

abbrev Callees := List (String × FunctionMIR)

structure CallAt (callees : Callees) (root : String) (paths : List String)
    (name argument : String) (callee : FunctionMIR) : Prop where
  sameRoot : argument = root
  found : callees.lookup name = some callee
  covered : ∀ field ∈ callee.paths, field ∈ paths

private def FunctionMIR.discardResult (callee : FunctionMIR) (rest : Operations) : Operations :=
  match callee.result with
  | .unit => rest
  | .byte offset => .discard (.field offset) rest
  | .view mode offset => .withView mode offset .done rest

structure ViewBinding where
  name : String
  mode : AccessMode
  offset : Nat

abbrev ViewScopes := List ViewBinding

def ViewScopes.names (scopes : ViewScopes) : List String := scopes.map ViewBinding.name

private theorem ViewScopes.name_at {scopes : ViewScopes} {index : Nat} {binding : ViewBinding}
    (bound : scopes[index]? = some binding) : scopes.names[index]? = some binding.name := by
  simp [ViewScopes.names, bound]

inductive ReadAt (source : Source) (root : String) (paths : List String) (scopes : ViewScopes) :
    SourcePlace → Place → Prop where
  | field : FieldAt source root paths path offset → ReadAt source root paths scopes (.field path) (.field offset)
  | view : scopes[index]? = some ⟨name, mode, offset⟩ →
      ReadAt source root paths scopes (.view name) (.view index offset)

inductive OperandAt (source : Source) (root : String) (paths : List String) (scopes : ViewScopes) :
    ByteOperand SourcePlace → ByteOperand Place → Prop where
  | literal : OperandAt source root paths scopes (.literal value) (.literal value)
  | place : ReadAt source root paths scopes place resolved →
      OperandAt source root paths scopes (.place place) (.place resolved)

inductive WriteAt (source : Source) (root : String) (paths : List String) (scopes : ViewScopes) :
    SourcePlace → Place → Prop where
  | field : FieldAt source root paths path offset → WriteAt source root paths scopes (.field path) (.field offset)
  | view : scopes[index]? = some ⟨name, .exclusive, offset⟩ → ContractSlot source paths offset →
      WriteAt source root paths scopes (.view name) (.view index offset)

private def Operations.thenDo (body next : Operations) : Operations :=
  match body with
  | .done => next
  | _ => .sequence body next

private theorem Operations.thenDo_writes (body next : Operations) :
    (body.thenDo next).writes = body.writes ++ next.writes := by
  cases body <;> rfl

/-- The source body determines each operation, comparison, arm, and call.
The caller's path contract must cover the callee's complete contract. -/
inductive Lowers (source : Source) (callees : Callees) (root : String) (paths : List String) :
    ViewScopes → Body → Operations → Prop where
  | done : Lowers source callees root paths scopes .done .done
  | discard : ReadAt source root paths scopes place resolved → Lowers source callees root paths scopes next rest →
      Lowers source callees root paths scopes (.discard place next) (.discard resolved rest)
  | assign : WriteAt source root paths scopes place target → Lowers source callees root paths scopes next rest →
      Lowers source callees root paths scopes (.assign place value next) (.assign target value rest)
  | copy : WriteAt source root paths scopes place target → ReadAt source root paths scopes operand resolved →
      Lowers source callees root paths scopes next rest →
      Lowers source callees root paths scopes (.copy place operand next) (.copy target resolved rest)
  | subtractFrom : WriteAt source root paths scopes place target →
      ReadAt source root paths scopes operand resolved →
      Lowers source callees root paths scopes next rest →
      Lowers source callees root paths scopes (.subtractFrom place operand amount next)
        (.subtractFrom target resolved amount rest)
  | assignCall : WriteAt source root paths scopes place target → CallAt callees root paths name argument callee →
      callee.result = .byte result → Lowers source callees root paths scopes next rest →
      Lowers source callees root paths scopes (.assignCall place name argument next)
        (.call name callee.body (.copy target (.field result) rest))
  | view {inside : Body} :
      FieldAt source root paths path offset → name ≠ root → name ∉ ViewScopes.names scopes →
      Lowers source callees root paths (⟨name, mode, offset⟩ :: scopes) (inside.loanWindow name).before inner →
      Lowers source callees root paths scopes (inside.loanWindow name).after tail →
      Lowers source callees root paths scopes next rest →
      Lowers source callees root paths scopes (.view mode name (.field path) inside next)
        (.withView mode offset inner (tail.thenDo rest))
  | reborrow : scopes[index]? = some ⟨parent, authority, offset⟩ → authority.Allows mode →
      name ≠ root → name ∉ ViewScopes.names scopes →
      Lowers source callees root paths (scopes.set index ⟨name, mode, offset⟩) inside inner →
      Lowers source callees root paths scopes next rest →
      Lowers source callees root paths scopes (.view mode name (.view parent) inside next)
        (.reborrow index mode inner rest)
  | branch {kind : ByteBranch} : ReadAt source root paths scopes place resolved →
      OperandAt source root paths scopes kind.operand right →
      Lowers source callees root paths scopes yes yesOps → Lowers source callees root paths scopes no noOps →
      Lowers source callees root paths scopes next rest →
      Lowers source callees root paths scopes (.branch place kind yes no next)
        (.branch resolved kind.comparison right yesOps noOps rest)
  | range : OperandAt source root paths scopes first resolvedFirst →
      OperandAt source root paths scopes stop resolvedStop →
      Lowers source callees root paths scopes body loopOps → Lowers source callees root paths scopes next rest →
      Lowers source callees root paths scopes (.range first stop body next)
        (.range resolvedFirst resolvedStop loopOps rest)
  | countdown : FieldAt source root paths counter offset →
      Lowers source callees root paths scopes afterDecrease effects → offset ∉ effects.writes →
      Lowers source callees root paths scopes next rest →
      Lowers source callees root paths scopes (.countdown counter threshold amount positive afterDecrease next)
        (Operations.countdown offset threshold amount effects rest)
  | call : CallAt callees root paths name argument callee →
      Lowers source callees root paths scopes next rest →
      Lowers source callees root paths scopes (.call name argument next)
        (.call name callee.body (callee.discardResult rest))
  | bindView {inside : Body} : CallAt callees root paths name argument callee → callee.result = .view mode offset →
      binding ≠ root → binding ∉ ViewScopes.names scopes →
      Lowers source callees root paths (⟨binding, mode, offset⟩ :: scopes) (inside.loanWindow binding).before body →
      Lowers source callees root paths scopes (inside.loanWindow binding).after tail →
      Lowers source callees root paths scopes (.bindView binding name argument inside)
        (.call name callee.body (.withView mode offset body tail))
  | forkStores : TasksAt source root paths tasks resolved →
      Lowers source callees root paths scopes next rest →
      Lowers source callees root paths scopes (.forkStores tasks next) (.forkStores resolved rest)

private def fieldNames (source : Source) : List String := source.fields.map Prod.fst

private theorem uniqueLookup {names : List String} (unique : names.Nodup) {left right : Nat}
    {name : String} (first : names[left]? = some name) (second : names[right]? = some name) :
    left = right :=
  unique.eq_of_getElem?_eq (List.getElem?_eq_some_iff.mp first).choose (first.trans second.symm)

theorem ReadAt.reborrow_scope {scopes : ViewScopes} {index : Nat} {parent child : String}
    {authority mode : AccessMode} {offset : Nat} (parentAt : scopes[index]? = some ⟨parent, authority, offset⟩)
    (fresh : child ∉ scopes.names) (unique : scopes.names.Nodup)
    (source : Source) (root : String) (paths : List String) :
    let inner := scopes.set index ⟨child, mode, offset⟩
    ReadAt source root paths inner (.view child) (.view index offset) ∧
      ∀ resolved, ¬ ReadAt source root paths inner (.view parent) resolved := by
  have original := ViewScopes.name_at parentAt
  have active := (List.getElem?_eq_some_iff.mp original).choose
  have inScope := (List.getElem?_eq_some_iff.mp parentAt).choose
  have distinct : child ≠ parent := fun same => fresh (same.symm ▸ List.mem_of_getElem? original)
  have renamed : ViewScopes.names (scopes.set index ⟨child, mode, offset⟩) = scopes.names.set index child := by
    simp [ViewScopes.names]
  refine ⟨.view (List.getElem?_set_self inScope), ?_⟩
  intro resolved usable
  cases usable with
  | view bound =>
    rename_i seen _ _
    have visible := ViewScopes.name_at bound
    rw [renamed] at visible
    by_cases same : seen = index
    · subst seen
      rw [List.getElem?_set_self active] at visible
      exact distinct (Option.some.inj visible)
    · rw [List.getElem?_set_ne (Ne.symm same)] at visible
      exact same (uniqueLookup unique visible original)

private theorem FieldAt.unique {source : Source} {root : String} {paths : List String}
    {path : FieldPath} {left right : Nat} (first : FieldAt source root paths path left)
    (second : FieldAt source root paths path right) (names : (fieldNames source).Nodup) :
    left = right := by
  obtain ⟨_, _, _, leftField⟩ := first
  obtain ⟨_, _, _, rightField⟩ := second
  apply uniqueLookup names (name := path.field)
  · simp [fieldNames, List.getElem?_map, leftField]
  · simp [fieldNames, List.getElem?_map, rightField]

private theorem StoresAt.unique {source : Source} {root : String} {paths : List String}
    {task : SourceStoreTask} {first second : StoreTask}
    (left : StoresAt source root paths task first) (right : StoresAt source root paths task second)
    (fields : (fieldNames source).Nodup) : first = second := by
  induction left generalizing second with
  | done => cases right; rfl
  | next target _ ih =>
    cases right with
    | next field tail => rw [target.unique field fields, ih tail]

private theorem TasksAt.unique {source : Source} {root : String} {paths : List String}
    {tasks : List SourceStoreTask} {first second : List StoreTask}
    (left : TasksAt source root paths tasks first) (right : TasksAt source root paths tasks second)
    (fields : (fieldNames source).Nodup) : first = second := by
  induction left generalizing second with
  | empty => cases right; rfl
  | next task _ ih =>
    cases right with
    | next same rest => rw [task.unique same fields, ih rest]

private theorem ReadAt.unique {source : Source} {root : String} {paths : List String} {scopes : ViewScopes}
    {place : SourcePlace} {left right : Place} (first : ReadAt source root paths scopes place left)
    (second : ReadAt source root paths scopes place right) (names : (fieldNames source).Nodup)
    (views : scopes.names.Nodup) : left = right := by
  cases first with
  | field first =>
    cases second with
    | field second => exact congrArg Place.field (first.unique second names)
  | view first =>
    cases second with
    | view second =>
      have firstName := ViewScopes.name_at first
      have secondName := ViewScopes.name_at second
      obtain rfl := uniqueLookup views firstName secondName
      exact congrArg (Place.view _) (congrArg ViewBinding.offset (Option.some.inj (first.symm.trans second)))

private theorem OperandAt.unique {source : Source} {root : String} {paths : List String} {scopes : ViewScopes}
    {operand : ByteOperand SourcePlace} {left right : ByteOperand Place}
    (first : OperandAt source root paths scopes operand left) (second : OperandAt source root paths scopes operand right)
    (names : (fieldNames source).Nodup) (views : scopes.names.Nodup) : left = right := by
  cases first with
  | literal => cases second; rfl
  | place read =>
    cases second with
    | place other => exact congrArg ByteOperand.place (read.unique other names views)

private theorem WriteAt.readable {source : Source} {root : String} {paths : List String} {scopes : ViewScopes}
    {place : SourcePlace} {target : Place} (access : WriteAt source root paths scopes place target) :
    ReadAt source root paths scopes place target := by
  cases access with
  | field resolved => exact .field resolved
  | view found _ => exact .view found

private theorem WriteAt.unique {source : Source} {root : String} {paths : List String} {scopes : ViewScopes}
    {place : SourcePlace} {left right : Place} (first : WriteAt source root paths scopes place left)
    (second : WriteAt source root paths scopes place right) (names : (fieldNames source).Nodup)
    (views : scopes.names.Nodup) : left = right :=
  first.readable.unique second.readable names views

private theorem CallAt.unique {callees : Callees} {root : String} {paths : List String}
    {name argument : String} {left right : FunctionMIR}
    (first : CallAt callees root paths name argument left)
    (second : CallAt callees root paths name argument right) : left = right :=
  Option.some.inj (first.found.symm.trans second.found)

private theorem names_set_nodup {names : List String} {name : String} (unique : names.Nodup)
    (fresh : name ∉ names) (index : Nat) : (names.set index name).Nodup := by
  induction index generalizing names with
  | zero => cases names <;> simp_all
  | succ index ih =>
    cases names with
    | nil => simp
    | cons first rest =>
      obtain ⟨firstAbsent, restUnique⟩ := List.nodup_cons.mp unique
      simp only [List.set_cons_succ, List.nodup_cons]
      refine ⟨fun found => ?_, ih restUnique (fun member => fresh (.tail _ member))⟩
      rcases List.mem_or_eq_of_mem_set found with old | new
      · exact firstAbsent old
      · exact fresh (new ▸ List.mem_cons_self)

theorem Lowers.unique {source : Source} {callees : Callees} {root : String}
    {paths : List String} {scopes : ViewScopes} {body : Body} {left right : Operations}
    (first : Lowers source callees root paths scopes body left)
    (second : Lowers source callees root paths scopes body right)
    (names : (fieldNames source).Nodup) (views : scopes.names.Nodup) : left = right := by
  induction first generalizing right with
  | done =>
    cases second
    rfl
  | discard place _ ih =>
    cases second with
    | discard rhs rest => rw [place.unique rhs names views, ih rest views]
  | assign field _ ih =>
    cases second with
    | assign rhs rest => rw [field.unique rhs names views, ih rest views]
  | copy field place _ ih =>
    cases second with
    | copy target rhs rest => rw [field.unique target names views, place.unique rhs names views, ih rest views]
  | subtractFrom field place _ ih =>
    cases second with
    | subtractFrom target rhs rest =>
      rw [field.unique target names views, place.unique rhs names views, ih rest views]
  | assignCall field callee result _ ih =>
    cases second with
    | assignCall target invoked returned rest =>
      cases callee.unique invoked
      rw [field.unique target names views, FunctionResult.byte.inj (result.symm.trans returned), ih rest views]
  | view field _ fresh _ _ _ inner suffix after =>
    cases second with
    | view target _ _ body rest next =>
      obtain rfl := field.unique target names
      rw [inner body (List.nodup_cons.mpr ⟨fresh, views⟩), suffix rest views, after next views]
  | reborrow parent _ _ fresh _ _ inside after =>
    cases second with
    | reborrow other _ _ _ body rest =>
      have parentName := ViewScopes.name_at parent
      have otherName := ViewScopes.name_at other
      obtain rfl := uniqueLookup views parentName otherName
      obtain rfl := congrArg ViewBinding.offset (Option.some.inj (parent.symm.trans other))
      rw [inside body (by simpa only [ViewScopes.names, List.map_set] using names_set_nodup views fresh _),
        after rest views]
  | branch place operand _ _ _ positive negative after =>
    cases second with
    | branch lhs rhs yes no rest =>
      rw [place.unique lhs names views, operand.unique rhs names views, positive yes views,
        negative no views, after rest views]
  | range start stop _ _ inner after =>
    cases second with
    | range lhs rhs body rest =>
      rw [start.unique lhs names views, stop.unique rhs names views, inner body views, after rest views]
  | countdown counter _ _ _ inside after =>
    cases second with
    | countdown same body _ rest => rw [counter.unique same names, inside body views, after rest views]
  | call callee _ after =>
    cases second with
    | call invoked rest =>
      cases callee.unique invoked
      rw [after rest views]
  | bindView callee result _ fresh _ _ inner suffix =>
    cases second with
    | bindView invoked returned _ _ body rest =>
      cases callee.unique invoked
      obtain ⟨rfl, rfl⟩ := FunctionResult.view.inj (result.symm.trans returned)
      rw [inner body (List.nodup_cons.mpr ⟨fresh, views⟩), suffix rest views]
  | forkStores tasks _ after =>
    cases second with
    | forkStores same rest => rw [tasks.unique same names, after rest views]

def Contract (source : Source) (paths : List String) : Prop :=
  paths.Nodup ∧ (∀ field ∈ paths, field ∈ fieldNames source)

private def allowsCall (calleePaths callerPaths : List String) : Prop :=
  ∀ field ∈ calleePaths, field ∈ callerPaths

instance (source : Source) (paths : List String) : Decidable (Contract source paths) :=
  inferInstanceAs (Decidable (paths.Nodup ∧ (∀ field ∈ paths, field ∈ fieldNames source)))

instance (calleePaths callerPaths : List String) : Decidable (allowsCall calleePaths callerPaths) :=
  inferInstanceAs (Decidable (∀ field ∈ calleePaths, field ∈ callerPaths))

inductive ReturnsAt (source : Source) (root : String) (paths : List String) :
    HelperResult → FunctionResult → Prop where
  | unit : ReturnsAt source root paths .unit .unit
  | byte : FieldAt source root paths path offset → ReturnsAt source root paths (.byte path) (.byte offset)
  | view : FieldAt source root paths path offset →
      ReturnsAt source root paths (.view mode path) (.view mode offset)

private theorem ReturnsAt.unique {source : Source} {root : String} {paths : List String}
    {result : HelperResult} {left right : FunctionResult}
    (first : ReturnsAt source root paths result left) (second : ReturnsAt source root paths result right)
    (names : (fieldNames source).Nodup) : left = right := by
  cases first with
  | unit => cases second; rfl
  | byte first =>
    cases second with
    | byte second => exact congrArg FunctionResult.byte (first.unique second names)
  | view first =>
    cases second with
    | view second => exact congrArg (FunctionResult.view _) (first.unique second names)

/-- Only earlier declarations are visible within a helper. This gives an
acyclic call graph and prevents an unverified helper body from being used. -/
inductive Declares (source : Source) : Callees → List Helper → List FunctionMIR → Prop where
  | done : Declares source callees [] []
  | next : callees.lookup helper.name = none → Contract source helper.paths →
      Lowers source callees helper.parameter helper.paths [] helper.body body →
      ReturnsAt source helper.parameter helper.paths helper.result result →
      Declares source ((helper.name, ⟨helper.name, helper.paths, body, result⟩) :: callees) rest functions →
      Declares source callees (helper :: rest) (⟨helper.name, helper.paths, body, result⟩ :: functions)

private theorem Declares.unique {source : Source} {callees : Callees} {helpers : List Helper}
    {left right : List FunctionMIR} (first : Declares source callees helpers left)
    (second : Declares source callees helpers right) (names : (fieldNames source).Nodup) :
    left = right := by
  induction first generalizing right with
  | done => cases second; rfl
  | next _ _ body result _ ih =>
    cases second with
    | next _ _ otherBody otherResult rest =>
      cases body.unique otherBody names List.nodup_nil
      cases result.unique otherResult names
      rw [ih rest]

private def entryCallees (functions : List FunctionMIR) : Callees :=
  functions.reverse.map fun fnMir => (fnMir.name, fnMir)

inductive OwnershipMoves : List String → String → List OwnerMove → Prop where
  | done : OwnershipMoves spent owner []
  | advance : move.fromName = owner → move.toName ≠ owner → move.toName ∉ spent →
      OwnershipMoves (owner :: spent) move.toName rest →
      OwnershipMoves spent owner (move :: rest)

private theorem OwnershipMoves.keeps_fresh {spent : List String} {owner : String} {moves : List OwnerMove}
    (valid : OwnershipMoves spent owner moves) (fresh : owner ∉ spent) :
    ownerAfter owner moves ∉ spent ++ moves.map OwnerMove.fromName := by
  induction valid with
  | done => simpa only [ownerAfter, List.map_nil, List.append_nil] using fresh
  | advance fromName same reused _ ih =>
    have remaining := ih (by simpa only [List.mem_cons, not_or] using And.intro same reused)
    intro duplicate
    apply remaining
    simpa only [ownerAfter, List.map_cons, List.cons_append, List.mem_cons, List.mem_append, fromName,
      or_assoc, or_left_comm] using duplicate

structure SourceTrace (source : Source) (mir : SourceMIR) : Prop where
  distinctFields : (fieldNames source).Nodup
  nonemptyRecord : source.fields ≠ []
  version : mir.version = currentSourceMIRVersion
  recordName : mir.record = source.record
  initialBytes : mir.fields = source.fields
  ownership : OwnershipMoves [] source.root source.moves
  moved : mir.moves = source.moves
  declarations : Declares source [] source.functions mir.functions
  body : Lowers source (entryCallees mir.functions) source.currentRoot (fieldNames source) [] source.body mir.body
  result : FieldAt source source.currentRoot (fieldNames source) source.result mir.result

theorem SourceTrace.current_owner_not_retired {source : Source} {mir : SourceMIR}
    (linked : SourceTrace source mir) : source.currentRoot ∉ mir.moves.map OwnerMove.fromName := by
  rw [linked.moved]
  exact linked.ownership.keeps_fresh (by simp)

/-- The declared source operations, contracts, and results determine a unique
reference MIR independently of the encoder and the resource checker. -/
theorem SourceTrace.unique {source : Source} {left right : SourceMIR}
    (first : SourceTrace source left) (second : SourceTrace source right) : left = right := by
  obtain ⟨names, _, leftVersion, leftRecord, leftFields, _, leftMoves, leftFns, leftBody, leftResult⟩ := first
  obtain ⟨_, _, rightVersion, rightRecord, rightFields, _, rightMoves, rightFns, rightBody, rightResult⟩ := second
  have functions := leftFns.unique rightFns names
  rw [← functions] at rightBody
  have body := leftBody.unique rightBody names List.nodup_nil
  have result := leftResult.unique rightResult names
  cases left
  cases right
  simp_all

private theorem ReturnsAt.view_origin {source : Source} {root : String} {paths : List String}
    {syntaxResult : HelperResult} {result : FunctionResult}
    (returned : ReturnsAt source root paths syntaxResult result)
    {mode : AccessMode} {offset : Nat} (view : result = .view mode offset) :
    ∃ field, syntaxResult = .view mode field ∧ FieldAt source root paths field offset := by
  cases returned with
  | unit | byte => cases view
  | view located =>
    cases view
    exact ⟨_, rfl, located⟩

private theorem Declares.view_origin {source : Source} {callees : Callees} {helpers : List Helper}
    {functions : List FunctionMIR} (declared : Declares source callees helpers functions)
    {fnMir : FunctionMIR} (member : fnMir ∈ functions) {mode : AccessMode} {offset : Nat}
    (result : fnMir.result = .view mode offset) :
    ∃ helper ∈ helpers, helper.name = fnMir.name ∧
      ∃ field, helper.result = .view mode field ∧ FieldAt source helper.parameter fnMir.paths field offset := by
  induction declared with
  | done => cases member
  | next _ _ _ returned _ ih =>
    rcases List.mem_cons.mp member with rfl | remaining
    · exact ⟨_, List.mem_cons_self, rfl, returned.view_origin result⟩
    · obtain ⟨helper, inTail, origin⟩ := ih remaining
      exact ⟨helper, List.mem_cons_of_mem _ inTail, origin⟩

/-- A returned view names a byte in the caller's record parameter and in
the callee's declared access contract. -/
theorem SourceTrace.returned_view_origin {source : Source} {mir : SourceMIR}
    (linked : SourceTrace source mir) {fnMir : FunctionMIR} (member : fnMir ∈ mir.functions)
    {mode : AccessMode} {offset : Nat} (result : fnMir.result = .view mode offset) :
    ∃ helper ∈ source.functions, helper.name = fnMir.name ∧
      ∃ field, helper.result = .view mode field ∧ FieldAt source helper.parameter fnMir.paths field offset :=
  linked.declarations.view_origin member result

/-- Every potentially written byte is a field named by the caller's contract. -/
def WritesWithin (source : Source) (paths : List String) (body : Operations) : Prop :=
  ∀ offset ∈ body.writes, ContractSlot source paths offset

private theorem FieldAt.contractSlot {source : Source} {root : String} {paths : List String}
    {path : FieldPath} {offset : Nat} (located : FieldAt source root paths path offset) : ContractSlot source paths offset := by
  obtain ⟨_, allowed, initial, found⟩ := located
  exact ⟨_, initial, found, allowed⟩

private theorem WriteAt.contractSlot {source : Source} {root : String} {paths : List String} {scopes : ViewScopes}
    {place : SourcePlace} {target : Place} (located : WriteAt source root paths scopes place target) :
    ContractSlot source paths target.offset := by
  cases located with
  | field resolved => exact resolved.contractSlot
  | view _ contracted => exact contracted

private theorem StoresAt.writeWithin {source : Source} {root : String} {paths : List String}
    {statements : SourceStoreTask} {task : StoreTask} (lowered : StoresAt source root paths statements task)
    {offset : Nat} (written : offset ∈ task.map Prod.fst) :
    ∃ field initial, source.fields[offset]? = some (field, initial) ∧ field ∈ paths := by
  induction lowered with
  | done => cases written
  | next target _ ih =>
    rcases List.mem_cons.mp written with rfl | remaining
    · exact target.contractSlot
    · exact ih remaining

private theorem TasksAt.writeWithin {source : Source} {root : String} {paths : List String}
    {statements : List SourceStoreTask} {tasks : List StoreTask}
    (lowered : TasksAt source root paths statements tasks)
    {offset : Nat} (written : offset ∈ tasks.flatten.map Prod.fst) :
    ∃ field initial, source.fields[offset]? = some (field, initial) ∧ field ∈ paths := by
  induction lowered with
  | empty => cases written
  | next task _ ih =>
    simp only [List.flatten_cons, List.map_append, List.mem_append] at written
    exact written.elim task.writeWithin ih

private def Callees.WriteContracts (source : Source) (callees : Callees) : Prop :=
  ∀ name fnMir, callees.lookup name = some fnMir → WritesWithin source fnMir.paths fnMir.body

private theorem WritesWithin.weaken {source : Source} {narrower broader : List String}
    {body : Operations} (holds : WritesWithin source narrower body)
    (subset : ∀ name ∈ narrower, name ∈ broader) : WritesWithin source broader body := by
  intro offset written
  obtain ⟨field, value, found, h⟩ := holds offset written
  exact ⟨field, value, found, subset field h⟩

theorem Lowers.writesWithin {source : Source} {callees : Callees} {root : String}
    {paths : List String} {scopes : ViewScopes}
    {body : Body} {ops : Operations} (lowered : Lowers source callees root paths scopes body ops)
    (known : Callees.WriteContracts source callees) : WritesWithin source paths ops := by
  intro offset written
  induction lowered with
  | done => simp [Operations.writes] at written
  | discard _ _ ih => exact ih written
  | assign field _ ih | copy field _ _ ih | subtractFrom field _ _ ih =>
    rcases List.mem_cons.mp written with equal | remaining
    · subst offset
      exact field.contractSlot
    · exact ih remaining
  | assignCall field callee _ _ ih =>
    rcases List.mem_append.mp written with called | rest
    · exact ((known _ _ callee.found).weaken callee.covered) offset called
    · rcases List.mem_cons.mp rest with equal | remaining
      · subst offset
        exact field.contractSlot
      · exact ih remaining
  | reborrow _ _ _ _ _ _ inside after =>
    exact (List.mem_append.mp written).elim inside after
  | range _ _ _ _ inside after =>
    simp only [Operations.writes] at written
    split at written
    · exact after (by simpa only [List.nil_append] using written)
    · exact (List.mem_append.mp written).elim inside after
  | view _ _ _ _ _ _ inside tail after =>
    simp only [Operations.writes, Operations.thenDo_writes] at written
    rcases List.mem_append.mp written with borrowed | remaining
    · exact inside borrowed
    · exact (List.mem_append.mp remaining).elim tail after
  | countdown field _ _ _ inside after =>
    simp only [Operations.countdown, Operations.countdownIteration, Operations.writes, List.append_nil,
      List.cons_append, List.mem_cons, List.mem_append] at written
    rcases written with same | remaining
    · subst offset
      exact field.contractSlot
    · exact remaining.elim inside after
  | branch _ _ _ _ _ yes no after =>
    simp only [Operations.writes] at written
    split at written
    · exact (List.mem_append.mp written).elim yes after
    · exact (List.mem_append.mp written).elim no after
    · exact (List.mem_append.mp written).elim (fun either => (List.mem_append.mp either).elim yes no) after
  | call resolved _ ih =>
    rcases List.mem_append.mp written with called | rest
    · exact ((known _ _ resolved.found).weaken resolved.covered) offset called
    · apply ih
      unfold FunctionMIR.discardResult at rest
      split at rest <;> simpa [Operations.writes] using rest
  | bindView callee _ _ _ _ _ inside after =>
    rcases List.mem_append.mp written with called | remaining
    · exact ((known _ _ callee.found).weaken callee.covered) offset called
    · exact (List.mem_append.mp remaining).elim inside after
  | forkStores tasks _ after =>
    exact (List.mem_append.mp written).elim tasks.writeWithin after

theorem Declares.writesWithin {source : Source} {callees : Callees} {helpers : List Helper}
    {functions : List FunctionMIR} (declared : Declares source callees helpers functions)
    (known : Callees.WriteContracts source callees) :
    ∀ fnMir ∈ functions, WritesWithin source fnMir.paths fnMir.body := by
  induction declared with
  | done => simp
  | next _ _ lowered _ _ ih =>
    have bodyProof := lowered.writesWithin known
    intro fnMir member
    rcases List.mem_cons.mp member with rfl | rest
    · exact bodyProof
    · refine ih ?_ fnMir rest
      intro name candidate found
      simp only [List.lookup] at found
      split at found
      · cases found
        exact bodyProof
      · exact known name candidate found

theorem SourceTrace.helper_write_contract {source : Source} {mir : SourceMIR}
    (linked : SourceTrace source mir) (fnMir : FunctionMIR) (member : fnMir ∈ mir.functions) :
    WritesWithin source fnMir.paths fnMir.body :=
  linked.declarations.writesWithin (by simp [Callees.WriteContracts]) fnMir member

def resolveField (source : Source) (root : String) (paths : List String) (path : FieldPath) :
    Except Error (Subtype (FieldAt source root paths path)) := do
  if resolved : path.root = root then
    match found : source.fields.findIdx? (fun field => field.1 == path.field) with
    | some offset =>
      if allowed : path.field ∈ paths then
        return ⟨offset, resolved, allowed, by
          obtain ⟨bound, name, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
          exact ⟨source.fields[offset].2, (List.getElem?_eq_getElem bound).trans
            (congrArg some (Prod.ext (beq_iff_eq.mp name) rfl))⟩⟩
      else throw (.invalidContract path.field)
    | none => throw (.unknownField path.root path.field)
  else throw (.unknownField path.root path.field)

private structure ResolvedView (scopes : ViewScopes) (name : String) where
  index : Nat
  mode : AccessMode
  offset : Nat
  found : scopes[index]? = some ⟨name, mode, offset⟩

private def resolveView (scopes : ViewScopes) (name : String) : Except Error (ResolvedView scopes name) :=
  match found : scopes.findIdx? (fun entry => entry.name == name) with
  | some index =>
    have located := List.findIdx?_eq_some_iff_getElem.mp found
    have bound := located.choose
    .ok ⟨index, scopes[index].mode, scopes[index].offset, by
      rw [List.getElem?_eq_getElem bound]
      have named := beq_iff_eq.mp located.choose_spec.1
      rw [← named]⟩
  | none => .error (.unknownView name)

private def freshBinding (root : String) (scopes : ViewScopes) (name : String) :
    Except Error (PLift (name ≠ root ∧ name ∉ scopes.names)) :=
  if fresh : name ≠ root ∧ name ∉ scopes.names then .ok ⟨fresh⟩
  else .error (.duplicateView name)

private def lowerRead (source : Source) (root : String) (paths : List String) (scopes : ViewScopes)
    (place : SourcePlace) :
    Except Error (Subtype (ReadAt source root paths scopes place)) :=
  match place with
  | .field path => do
    let field ← resolveField source root paths path
    return ⟨.field field.val, .field field.property⟩
  | .view name => do
    let view ← resolveView scopes name
    return ⟨.view view.index view.offset, .view view.found⟩

private def lowerOperand (source : Source) (root : String) (paths : List String) (scopes : ViewScopes) :
    (operand : ByteOperand SourcePlace) → Except Error (Subtype (OperandAt source root paths scopes operand))
  | .literal value => .ok ⟨.literal value, .literal⟩
  | .place target => do
    let read ← lowerRead source root paths scopes target
    return ⟨.place read.val, .place read.property⟩

private def lowerStore (source : Source) (root : String) (paths : List String) (scopes : ViewScopes)
    (place : SourcePlace) : Except Error (Subtype (WriteAt source root paths scopes place)) :=
  match place with
  | .field path => do
    let field ← resolveField source root paths path
    return ⟨.field field.val, .field field.property⟩
  | .view name => do
    let view ← resolveView scopes name
    if exclusive : view.mode = .exclusive then
      match located : source.fields[view.offset]? with
      | none => throw (.unknownView name)
      | some (field, initial) =>
        if allowed : field ∈ paths then
          return ⟨.view view.index view.offset,
            .view (by simpa only [exclusive] using view.found) ⟨field, initial, located, allowed⟩⟩
        else throw (.invalidContract field)
    else throw (.immutableView name)

private def resolveCall (callees : Callees) (root : String) (paths : List String) (name argument : String) :
    Except Error (Subtype (CallAt callees root paths name argument)) := do
  match found : callees.lookup name with
  | none => throw (.unknownFunction name)
  | some callee =>
    if covered : allowsCall callee.paths paths then
      if same : argument = root then
        return ⟨callee, same, found, covered⟩
      else throw (.invalidArgument name)
    else throw (.invalidContract name)

private def lowerReturn (source : Source) (root : String) (paths : List String) :
    (result : HelperResult) → Except Error (Subtype (ReturnsAt source root paths result))
  | .unit => .ok ⟨.unit, .unit⟩
  | .byte field => do
    let offset ← resolveField source root paths field
    return ⟨.byte offset.val, .byte offset.property⟩
  | .view mode field => do
    let offset ← resolveField source root paths field
    return ⟨.view mode offset.val, .view offset.property⟩

private def lowerStores (source : Source) (root : String) (paths : List String) :
    (task : SourceStoreTask) → Except Error (Subtype (StoresAt source root paths task))
  | [] => .ok ⟨[], .done⟩
  | (field, value) :: tail => do
    let target ← resolveField source root paths field
    let rest ← lowerStores source root paths tail
    return ⟨(target.val, value) :: rest.val, .next target.property rest.property⟩

private def lowerTasks (source : Source) (root : String) (paths : List String) :
    (tasks : List SourceStoreTask) → Except Error (Subtype (TasksAt source root paths tasks))
  | [] => .ok ⟨[], .empty⟩
  | next :: tail => do
    let task ← lowerStores source root paths next
    let rest ← lowerTasks source root paths tail
    return ⟨task.val :: rest.val, .next task.property rest.property⟩

private def lowerLoanBody (source : Source) (callees : Callees) (root : String) (paths : List String)
    (scopes : ViewScopes) (binding : ViewBinding) (body : Body)
    (lower : (localScopes : ViewScopes) → (part : Body) → sizeOf part ≤ sizeOf body →
      Except Error (Subtype (Lowers source callees root paths localScopes part))) :
    Except Error { ops : Operations × Operations //
      Lowers source callees root paths (binding :: scopes) (body.loanWindow binding.name).before ops.1 ∧
      Lowers source callees root paths scopes (body.loanWindow binding.name).after ops.2 } := do
  let window := body.loanWindow binding.name
  let borrowed ← lower (binding :: scopes) window.before window.beforeSize
  let released ← lower scopes window.after window.afterSize
  return ⟨(borrowed.val, released.val), borrowed.property, released.property⟩

private def lowerBody (source : Source) (callees : Callees) (root : String) (paths : List String)
    (scopes : ViewScopes) :
    (body : Body) → Except Error (Subtype (Lowers source callees root paths scopes body))
  | .done => .ok ⟨.done, .done⟩
  | .discard place next => do
    let access ← lowerRead source root paths scopes place
    let rest ← lowerBody source callees root paths scopes next
    return ⟨.discard access.val rest.val, .discard access.property rest.property⟩
  | .assign place value next => do
    let target ← lowerStore source root paths scopes place
    let rest ← lowerBody source callees root paths scopes next
    return ⟨.assign target.val value rest.val, .assign target.property rest.property⟩
  | .copy place operand next => do
    let target ← lowerStore source root paths scopes place
    let loaded ← lowerRead source root paths scopes operand
    let rest ← lowerBody source callees root paths scopes next
    return ⟨.copy target.val loaded.val rest.val, .copy target.property loaded.property rest.property⟩
  | .subtractFrom place operand amount next => do
    let target ← lowerStore source root paths scopes place
    let loaded ← lowerRead source root paths scopes operand
    let rest ← lowerBody source callees root paths scopes next
    return ⟨.subtractFrom target.val loaded.val amount rest.val,
      .subtractFrom target.property loaded.property rest.property⟩
  | .assignCall place name argument next => do
    let target ← lowerStore source root paths scopes place
    let callee ← resolveCall callees root paths name argument
    match returns : callee.val.result with
    | .byte result =>
      let rest ← lowerBody source callees root paths scopes next
      return ⟨.call name callee.val.body (.copy target.val (.field result) rest.val),
        .assignCall target.property callee.property returns rest.property⟩
    | _ => throw (.invalidCallResult name)
  | .view mode name (.field path) inside next => do
    let fresh ← freshBinding root scopes name
    let field ← resolveField source root paths path
    let rest ← lowerBody source callees root paths scopes next
    let loan ← lowerLoanBody source callees root paths scopes ⟨name, mode, field.val⟩ inside fun localScopes part _ =>
      lowerBody source callees root paths localScopes part
    return ⟨.withView mode field.val loan.val.1 (loan.val.2.thenDo rest.val),
      .view field.property fresh.down.1 fresh.down.2 loan.property.1 loan.property.2 rest.property⟩
  | .view mode name (.view parent) inside next => do
    let fresh ← freshBinding root scopes name
    let loan ← resolveView scopes parent
    if allowed : loan.mode.Allows mode then
      let inner ← lowerBody source callees root paths (scopes.set loan.index ⟨name, mode, loan.offset⟩) inside
      let rest ← lowerBody source callees root paths scopes next
      return ⟨.reborrow loan.index mode inner.val rest.val,
        .reborrow loan.found allowed fresh.down.1 fresh.down.2 inner.property rest.property⟩
    else throw (.invalidReborrow parent)
  | .branch place kind yes no next => do
    let access ← lowerRead source root paths scopes place
    let bound ← lowerOperand source root paths scopes kind.operand
    let yes ← lowerBody source callees root paths scopes yes
    let no ← lowerBody source callees root paths scopes no
    let rest ← lowerBody source callees root paths scopes next
    return ⟨.branch access.val kind.comparison bound.val yes.val no.val rest.val,
      .branch access.property bound.property yes.property no.property rest.property⟩
  | .range first stop body next => do
    let start ← lowerOperand source root paths scopes first
    let finish ← lowerOperand source root paths scopes stop
    let loop ← lowerBody source callees root paths scopes body
    let rest ← lowerBody source callees root paths scopes next
    return ⟨.range start.val finish.val loop.val rest.val,
      .range start.property finish.property loop.property rest.property⟩
  | .countdown counter threshold amount _ afterDecrease next => do
    let field ← resolveField source root paths counter
    let effects ← lowerBody source callees root paths scopes afterDecrease
    let rest ← lowerBody source callees root paths scopes next
    if stable : field.val ∉ effects.val.writes then
      return ⟨Operations.countdown field.val threshold amount effects.val rest.val,
        .countdown field.property effects.property stable rest.property⟩
    else throw .invalidDecreases
  | .call name argument next => do
    let callee ← resolveCall callees root paths name argument
    let rest ← lowerBody source callees root paths scopes next
    return ⟨.call name callee.val.body (callee.val.discardResult rest.val), .call callee.property rest.property⟩
  | .bindView binding name argument inside => do
    let fresh ← freshBinding root scopes binding
    let callee ← resolveCall callees root paths name argument
    match returns : callee.val.result with
    | .view mode offset =>
      let loan ← lowerLoanBody source callees root paths scopes ⟨binding, mode, offset⟩ inside
        fun localScopes part _ => lowerBody source callees root paths localScopes part
      return ⟨.call name callee.val.body (.withView mode offset loan.val.1 loan.val.2),
        .bindView callee.property returns fresh.down.1 fresh.down.2 loan.property.1 loan.property.2⟩
    | _ => throw (.invalidCallResult name)
  | .forkStores tasks next => do
    let lowered ← lowerTasks source root paths tasks
    let rest ← lowerBody source callees root paths scopes next
    return ⟨.forkStores lowered.val rest.val, .forkStores lowered.property rest.property⟩
termination_by body => sizeOf body
decreasing_by
  all_goals simp_wf <;> omega

private def lowerHelpers (source : Source) (callees : Callees) :
    (helpers : List Helper) → Except Error (Subtype (Declares source callees helpers))
  | [] => .ok ⟨[], .done⟩
  | helper :: rest => do
    if valid : callees.lookup helper.name = none ∧ Contract source helper.paths then
      let body ← lowerBody source callees helper.parameter helper.paths [] helper.body
      let result ← lowerReturn source helper.parameter helper.paths helper.result
      let fnMir : FunctionMIR := ⟨helper.name, helper.paths, body.val, result.val⟩
      let remaining ← lowerHelpers source ((helper.name, fnMir) :: callees) rest
      return ⟨fnMir :: remaining.val, .next valid.1 valid.2 body.property result.property remaining.property⟩
    else throw (.invalidContract helper.name)

private def checkMoves (spent : List String) (owner : String) :
    (moves : List OwnerMove) → Except Error (PLift (OwnershipMoves spent owner moves))
  | [] => .ok ⟨.done⟩
  | move :: rest => do
    if allowed : move.fromName = owner ∧ move.toName ≠ owner ∧ move.toName ∉ spent then
      let tail ← checkMoves (owner :: spent) move.toName rest
      return ⟨.advance allowed.1 allowed.2.1 allowed.2.2 tail.down⟩
    else throw (.invalidMove move.fromName move.toName)

private def lower (source : Source) : Except Error (Subtype (SourceTrace source)) := do
  if fields : (fieldNames source).Nodup ∧ source.fields ≠ [] then
    let moves ← checkMoves [] source.root source.moves
    let functions ← lowerHelpers source [] source.functions
    let body ← lowerBody source (entryCallees functions.val) source.currentRoot (fieldNames source) [] source.body
    let result ← resolveField source source.currentRoot (fieldNames source) source.result
    return ⟨⟨currentSourceMIRVersion, source.record, source.fields, source.moves, functions.val, body.val, result.val⟩,
      fields.1, fields.2, rfl, rfl, rfl, moves.down, rfl, functions.property, body.property, result.property⟩
  else throw (.syntax "at least one distinct record field")

structure Verified (input : String) where
  source : Source
  mir : SourceMIR
  spelled : tokens input = source.tokens
  lowers : SourceTrace source mir
  checked : mir.check = true

/-- Check the actual source and build its operations in the reference MIR. -/
def verify (input : String) : Except Error (Verified input) := do
  let source ← parseSource (tokens input)
  if spelled : tokens input = source.tokens then
    let lowered ← lower source
    if safe : lowered.val.check = true then
      return ⟨source, lowered.val, spelled, lowered.property, safe⟩
    else throw .resourceConflict
  else throw (.syntax "canonical record fragment")

theorem Verified.executes {input : String} (accepted : Verified input) :
    ∃ steps final, Structured.Executes Env.empty {} accepted.mir.code steps final ∧ final.views = [] :=
  SourceMIR.executes accepted.checked

theorem Verified.prefix_safe {input : String} (accepted : Verified input) {first rest : Program}
    {final : State}
    (ran : Structured.Executes Env.empty {} accepted.mir.code (first ++ rest) final) :
    ∃ middle, Runs {} first middle ∧ Runs middle rest final ∧ final.views = [] ∧
      middle.OwnersValid ∧ middle.ReferencesLive ∧ middle.ViewsCompatible := by
  obtain ⟨_, checkedFinal, checkedRun, closed⟩ := accepted.executes
  have same : final = checkedFinal := congrArg Prod.snd (Option.some.inj (ran.agrees.symm.trans checkedRun.agrees))
  have finalClosed : final.views = [] := same ▸ closed
  obtain ⟨middle, _, initial, _, _, owners, live, views⟩ :=
    Core.verified_prefix_safe ((verifyResources_correct _).mpr ⟨final, ran.trace, finalClosed⟩)
  have traced := run_complete ran.trace
  rw [run_append, run_complete initial] at traced
  exact ⟨middle, initial, Core.run_sound traced, finalClosed, owners, live, views⟩

def execute {input : String} (accepted : Verified input) : Option UInt8 :=
  accepted.mir.run.bind fun state => state.observations.head?

theorem Verified.execute_correct {input : String} (accepted : Verified input) :
    ∃ steps final value, Structured.Executes Env.empty {} accepted.mir.code steps final ∧
      final.views = [] ∧ execute accepted = some value ∧
      ∃ before after, Step before (.read accepted.mir.result) after ∧ Step after (.destroy 0) final := by
  obtain ⟨steps, final, ran, closed⟩ := accepted.executes
  obtain ⟨before, after, value, read, drop, observed⟩ := accepted.mir.main_result ran
  exact ⟨steps, final, value, ran, closed, by simp [execute, ← accepted.mir.run_agrees, ran.agrees, observed], before, after, read, drop⟩

/-- A helper preserves each field outside its declared contract, including
writes made through any of its transitive callees. -/
theorem Verified.helper_preserves_unlisted_field {input : String} (accepted : Verified input)
    {fnMir : FunctionMIR} (declared : fnMir ∈ accepted.mir.functions)
    {state next : State} {offset depth : Nat} {field : String} {initial : UInt8}
    (rooted : RecordAddresses state) (knownField : accepted.source.fields[offset]? = some (field, initial))
    (unlisted : field ∉ fnMir.paths) (ran : fnMir.body.run depth state = some next) :
    next.byte ⟨0, offset⟩ = state.byte ⟨0, offset⟩ := by
  apply Operations.run_preserves_byte rooted ran
  intro written
  obtain ⟨name, value, found, allowed⟩ := accepted.lowers.helper_write_contract fnMir declared offset written
  have same : name = field := congrArg Prod.fst (Option.some.inj (found.symm.trans knownField))
  exact unlisted (same ▸ allowed)

def encodeCanonicalMIR {α : Type} [ToJson α] (mir : α) : String :=
  (toJson mir).compress

def decodeCanonicalMIR {α : Type} [ToJson α] [FromJson α] (text : String) : Except Error α := do
  let json ← (Json.parse text).mapError (fun _ => .invalidSourceMIR)
  let mir ← (fromJson? json).mapError (fun _ => .invalidSourceMIR)
  if text.trimAscii.toString = encodeCanonicalMIR mir then return mir
  else throw .invalidSourceMIR

def matchCanonicalMIR {α : Type} [ToJson α] [FromJson α] [DecidableEq α]
    (text : String) (expected : α) : Except Error (PLift (decodeCanonicalMIR text = .ok expected)) :=
  match decodeCanonicalMIR text with
  | .error err => .error err
  | .ok candidate =>
    if same : candidate = expected then .ok ⟨congrArg Except.ok same⟩
    else .error .sourceMIRMismatch

def encodeMIR (mir : SourceMIR) : String := encodeCanonicalMIR mir

def decodeMIR (text : String) : Except Error SourceMIR := decodeCanonicalMIR text

structure MatchingMIR (input text : String) where
  accepted : Verified input
  decoded : decodeMIR text = .ok accepted.mir

/-- A separately supplied reference MIR must agree with the whole rederived
module, including both branch arms and every helper's contract and body. -/
def verifyMIR (input text : String) : Except Error (MatchingMIR input text) := do
  let accepted ← verify input
  let matched ← matchCanonicalMIR text accepted.mir
  return ⟨accepted, matched.down⟩

theorem MatchingMIR.corresponds {input text : String} (matchMIR : MatchingMIR input text) :
    ∃ source mir, decodeMIR text = .ok mir ∧ tokens input = source.tokens ∧
      SourceTrace source mir ∧
      ∃ steps final, Structured.Executes Env.empty {} mir.code steps final ∧ final.views = [] :=
  ⟨matchMIR.accepted.source, matchMIR.accepted.mir, matchMIR.decoded,
    matchMIR.accepted.spelled, matchMIR.accepted.lowers, matchMIR.accepted.executes⟩

end Aethel.SourceVerification
