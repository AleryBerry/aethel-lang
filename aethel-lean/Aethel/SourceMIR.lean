import Aethel.Structured
import Lean.Elab.Deriving.FromToJson

namespace Aethel.SourceVerification

open Core Functional Structured Lean

private instance : ToJson UInt8 where
  toJson value := toJson value.toNat

private instance : FromJson UInt8 where
  fromJson? value := do
    let n : Nat ← fromJson? value
    if n < 256 then return UInt8.ofNat n
    else throw "byte outside 0..255"

inductive Place where
  | field (offset : Nat)
  | view (index : Nat)
  deriving Repr, DecidableEq, ToJson, FromJson

def Place.target (depth : Nat) : Place → AccessTarget
  | .field offset => .handle offset
  | .view index => .view (depth - (index + 1))

inductive Comparison where
  | equal
  | unequal
  | less
  | lessEqual
  deriving Repr, DecidableEq, ToJson, FromJson

private def Comparison.guard (comparison : Comparison) (literal : UInt8) :
    Term (.byte :: ctx) .bool :=
  let read : Term (.byte :: ctx) .byte := .var .here
  let bound : Term (.byte :: ctx) .byte := .byte literal
  match comparison with
  | .equal => .byteEq read bound
  | .unequal => .branch (.byteEq read bound) (.bool false) (.bool true)
  | .less => .byteLt read bound
  | .lessEqual => .byteLe read bound

/-- Byte operations with explicit control flow. A scope or branch carries its
continuation once. A call carries the resolved callee in its own lexical scope. -/
inductive Operations where
  | done
  | discard (place : Place) (next : Operations)
  | assign (offset : Nat) (value : UInt8) (next : Operations)
  | sharedScope (offset : Nat) (body next : Operations)
  | exclusiveScope (offset : Nat) (body next : Operations)
  | branch (place : Place) (comparison : Comparison) (value : UInt8)
      (yes no next : Operations)
  | call (name : String) (body next : Operations)
  deriving Repr, DecidableEq, ToJson, FromJson

def Operations.withView (mode : AccessMode) (offset : Nat) (body next : Operations) : Operations :=
  match mode with
  | .shared => .sharedScope offset body next
  | .exclusive => .exclusiveScope offset body next

abbrev Continuation := (ctx : List Ty) → Code ctx

def Operations.toCode : Operations → Nat → Continuation → Continuation
  | .done, _, rest => rest
  | .discard place next, depth, rest => fun ctx =>
    .instruction ((place.target depth).readInstruction) (next.toCode depth rest ctx)
  | .assign offset value next, depth, rest => fun ctx =>
    .instruction (.write offset value) (next.toCode depth rest ctx)
  | .sharedScope offset body next, depth, rest => fun ctx =>
    .instruction (.reserve depth offset .shared)
      (body.toCode (depth + 1) (fun inner => .instruction (.release depth) (next.toCode depth rest inner)) ctx)
  | .exclusiveScope offset body next, depth, rest => fun ctx =>
    .instruction (.reserve depth offset .exclusive)
      (body.toCode (depth + 1) (fun inner => .instruction (.release depth) (next.toCode depth rest inner)) ctx)
  | .branch place comparison value yes no next, depth, rest => fun ctx =>
    let join := next.toCode depth rest
    .read (place.target depth)
      (.branch (comparison.guard value) (yes.toCode depth join (.byte :: ctx))
        (no.toCode depth join (.byte :: ctx)))
  | .call _ body next, depth, rest => body.toCode depth (next.toCode depth rest)

structure FunctionMIR where
  name : String
  paths : List String
  body : Operations
  deriving Repr, DecidableEq, ToJson, FromJson

/-- The reference MIR includes the initialized record and every helper
definition as well as the executable entry, including unused helpers. -/
structure SourceMIR where
  version : Nat
  record : String
  fields : List (String × UInt8)
  functions : List FunctionMIR
  body : Operations
  result : Nat
  deriving Repr, DecidableEq, ToJson, FromJson

def currentSourceMIRVersion : Nat := 2

private def recordEntry (bytes : List UInt8) : Program :=
  .alloc 0 bytes :: (List.range bytes.length).map (fun i => .alias i 0 i .exclusive)

private def prepend (steps : Program) (rest : Code ctx) : Code ctx :=
  steps.foldr .instruction rest

def SourceMIR.code (mir : SourceMIR) : Code [] :=
  prepend (recordEntry (mir.fields.map Prod.snd))
    (mir.body.toCode 0 (fun _ => .instruction (.read mir.result) (.instruction (.destroy 0) .finish)) [])

private def FunctionMIR.code (fnMir : FunctionMIR) (fieldCount : Nat) : Code [] :=
  prepend (recordEntry (List.replicate fieldCount 0))
    (fnMir.body.toCode 0 (fun _ => .instruction (.destroy 0) .finish) [])

/-- Check each helper over a live initialized record and then check the main
body, where inlining also checks each call under its actual caller reservations. -/
def SourceMIR.check (mir : SourceMIR) : Bool :=
  mir.functions.all (fun fnMir => Structured.check {} (fnMir.code mir.fields.length)) &&
    Structured.check {} mir.code

theorem SourceMIR.executes {mir : SourceMIR} (ok : mir.check = true) :
    ∃ steps final, Structured.Executes Env.empty {} mir.code steps final ∧ final.views = [] :=
  check_executes mir.code Env.empty {} (Bool.and_eq_true_iff.mp ok).2

theorem SourceMIR.helpers_execute {mir : SourceMIR} (ok : mir.check = true)
    (fnMir : FunctionMIR) (declared : fnMir ∈ mir.functions) :
    ∃ steps final, Structured.Executes Env.empty {} (fnMir.code mir.fields.length) steps final ∧
      final.views = [] :=
  check_executes _ Env.empty {} (List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).1 fnMir declared)

private theorem Operations.toCode_post (ops : Operations) (P : State → Prop)
    (rest : Continuation) (depth : Nat)
    (post : ∀ {ctx} {env : Env ctx} {state steps final},
      Structured.Executes env state (rest ctx) steps final → P final)
    {ctx} {env : Env ctx} {state steps final}
    (run : Structured.Executes env state (ops.toCode depth rest ctx) steps final) : P final := by
  induction ops generalizing rest depth ctx state steps final with
  | done => exact post run
  | discard _ _ ih | assign _ _ _ ih =>
    cases run with
    | instruction _ continued => exact ih rest depth post continued
  | sharedScope offset body next inside after | exclusiveScope offset body next inside after =>
    cases run with
    | instruction _ continued =>
      refine inside _ (depth + 1) ?_ continued
      intro _ _ _ _ _ released
      cases released with
      | instruction _ resumed => exact after rest depth post resumed
  | branch place comparison value yes no next left right joined =>
    cases run with
    | read _ _ chosen =>
      cases chosen with
      | branchTrue _ ran => exact left _ depth (joined rest depth post) ran
      | branchFalse _ ran => exact right _ depth (joined rest depth post) ran
  | call name body next inside after =>
    exact inside _ depth (after rest depth post) run

private theorem prepend_post {ctx} {env : Env ctx} (entry : Program) {rest : Code ctx}
    (P : State → Prop) (post : ∀ {state steps final}, Structured.Executes env state rest steps final → P final)
    {state steps final} (ran : Structured.Executes env state (prepend entry rest) steps final) :
    P final := by
  induction entry generalizing state steps final with
  | nil => exact post ran
  | cons _ _ ih =>
    cases ran with
    | instruction _ continued => exact ih continued

theorem SourceMIR.main_result {mir : SourceMIR} {steps final}
    (ran : Structured.Executes Env.empty {} mir.code steps final) :
    ∃ before after value, Step before (.read mir.result) after ∧
      Step after (.destroy 0) final ∧ final.observations.head? = some value := by
  let P : State → Prop := fun state =>
    ∃ before after value, Step before (.read mir.result) after ∧
      Step after (.destroy 0) state ∧ state.observations.head? = some value
  change P final
  apply prepend_post _ P (fun bodyRun =>
    Operations.toCode_post mir.body P _ 0 ?_ bodyRun) ran
  intro ctx env state steps final ran
  cases ran with
  | instruction reads continued =>
    cases continued with
    | instruction destroys finished =>
      cases finished
      refine ⟨_, _, _, reads, destroys, ?_⟩
      cases reads
      cases destroys
      rfl

end Aethel.SourceVerification
