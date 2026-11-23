import Aethel.Functions
import Aethel.FunctionSummaries
import Aethel.Structured
import Aethel.BorrowGraph
import Aethel.Iteration

namespace Aethel.CoreAST

open Functional Core Structured

/-- The unified type system of the sequential core language. -/
inductive CoreType where
  | unit : CoreType
  | bool : CoreType
  | nat : CoreType
  | int (signed : Bool) (bits : Nat) : CoreType
  | prod (left right : CoreType) : CoreType
  | adt (tag : Nat) (payload : CoreType) : CoreType
  | handle (elemTy : CoreType) : CoreType
  | view (elemTy : CoreType) (mode : AccessMode) : CoreType
  | arrow (dom cod : CoreType) (eff : Effect) : CoreType
  deriving DecidableEq, Repr

abbrev CoreType.byte : CoreType := .int false 8
abbrev CoreType.uint16 : CoreType := .int false 16

/-- The unified abstract syntax tree of the sequential core language. -/
inductive CoreExpr where
  | unit : CoreExpr
  | bool (b : Bool) : CoreExpr
  | nat (n : Nat) : CoreExpr
  | int (signed : Bool) (bits : Nat) (val : Int) : CoreExpr
  | pair (fst snd : CoreExpr) : CoreExpr
  | fst (p : CoreExpr) : CoreExpr
  | snd (p : CoreExpr) : CoreExpr
  | adt (tag : Nat) (payload : CoreExpr) : CoreExpr
  | matchTag (scrutinee : CoreExpr) (tag : Nat) (onMatch : CoreExpr) (onElse : CoreExpr) : CoreExpr
  | var (id : Nat) : CoreExpr
  | letBind (id : Nat) (val : CoreExpr) (body : CoreExpr) : CoreExpr
  | alloc (size : Nat) (initByte : UInt8) : CoreExpr
  | readHandle (handleId : Nat) (offset : Nat) : CoreExpr
  | writeHandle (handleId : Nat) (offset : Nat) (val : CoreExpr) : CoreExpr
  | borrowView (viewId : Nat) (handleId : Nat) (mode : AccessMode) (offset : Nat) (body : CoreExpr) : CoreExpr
  | readView (viewId : Nat) : CoreExpr
  | writeView (viewId : Nat) (val : CoreExpr) : CoreExpr
  | lam (param : Nat) (paramTy : CoreType) (body : CoreExpr) (eff : Effect) : CoreExpr
  | app (fn : CoreExpr) (arg : CoreExpr) : CoreExpr
  | loop (cond : CoreExpr) (body : CoreExpr) : CoreExpr
  | abort (reason : String) : CoreExpr
  deriving Repr, DecidableEq

/-- Syntactic value predicate decider. -/
def isVal : CoreExpr → Bool
  | .unit | .bool _ | .nat _ | .int _ _ _ => true
  | .lam _ _ _ _ => true
  | .pair a b => isVal a && isVal b
  | .adt _ p => isVal p
  | _ => false

/-- Inductive value predicate characterizing irreducibles. -/
inductive Value : CoreExpr → Prop where
  | unit : Value .unit
  | bool (b : Bool) : Value (.bool b)
  | nat (n : Nat) : Value (.nat n)
  | int (s : Bool) (bits : Nat) (v : Int) : Value (.int s bits v)
  | lam (p : Nat) (ty : CoreType) (body : CoreExpr) (eff : Effect) :
      Value (.lam p ty body eff)
  | pair {a b : CoreExpr} : Value a → Value b → Value (.pair a b)
  | adt (tag : Nat) {p : CoreExpr} : Value p → Value (.adt tag p)

theorem isVal_correct (e : CoreExpr) : isVal e = true ↔ Value e := by
  induction e with
  | unit => simp [isVal, Value.unit]
  | bool b => simp [isVal, Value.bool]
  | nat n => simp [isVal, Value.nat]
  | int s bits v => simp [isVal, Value.int]
  | pair a b iha ihb =>
    simp only [isVal, Bool.and_eq_true]
    constructor
    · rintro ⟨ha, hb⟩
      exact .pair (iha.mp ha) (ihb.mp hb)
    · intro h
      cases h with
      | pair ha hb => exact ⟨iha.mpr ha, ihb.mpr hb⟩
  | fst _ => simp [isVal]; intro h; cases h
  | snd _ => simp [isVal]; intro h; cases h
  | adt tag p ih =>
    simp only [isVal]
    constructor
    · intro h; exact .adt tag (ih.mp h)
    · intro h; cases h with | adt _ hp => exact ih.mpr hp
  | matchTag _ _ _ _ => simp [isVal]; intro h; cases h
  | var _ => simp [isVal]; intro h; cases h
  | letBind _ _ _ => simp [isVal]; intro h; cases h
  | alloc _ _ => simp [isVal]; intro h; cases h
  | readHandle _ _ => simp [isVal]; intro h; cases h
  | writeHandle _ _ _ => simp [isVal]; intro h; cases h
  | borrowView _ _ _ _ _ => simp [isVal]; intro h; cases h
  | readView _ => simp [isVal]; intro h; cases h
  | writeView _ _ => simp [isVal]; intro h; cases h
  | lam p ty body eff => simp [isVal, Value.lam]
  | app _ _ => simp [isVal]; intro h; cases h
  | loop _ _ => simp [isVal]; intro h; cases h
  | abort _ => simp [isVal]; intro h; cases h

/-- Capture-avoiding substitution of free variable `varId` by `val`. -/
def subst (varId : Nat) (val : CoreExpr) : CoreExpr → CoreExpr
  | .unit => .unit
  | .bool b => .bool b
  | .nat n => .nat n
  | .int s bits v => .int s bits v
  | .pair a b => .pair (subst varId val a) (subst varId val b)
  | .fst p => .fst (subst varId val p)
  | .snd p => .snd (subst varId val p)
  | .adt tag p => .adt tag (subst varId val p)
  | .matchTag s tag onMatch onElse =>
    .matchTag (subst varId val s) tag (subst varId val onMatch) (subst varId val onElse)
  | .var id => if id = varId then val else .var id
  | .letBind id v body =>
    let v' := subst varId val v
    let body' := if id = varId then body else subst varId val body
    .letBind id v' body'
  | .alloc sz init => .alloc sz init
  | .readHandle h off => .readHandle h off
  | .writeHandle h off v => .writeHandle h off (subst varId val v)
  | .borrowView vId h mode off body =>
    let body' := if vId = varId then body else subst varId val body
    .borrowView vId h mode off body'
  | .readView vId => .readView vId
  | .writeView vId v => .writeView vId (subst varId val v)
  | .lam p ty body eff =>
    let body' := if p = varId then body else subst varId val body
    .lam p ty body' eff
  | .app fn arg => .app (subst varId val fn) (subst varId val arg)
  | .loop c b => .loop (subst varId val c) (subst varId val b)
  | .abort reason => .abort reason

abbrev Ctx := List (Nat × CoreType)

def Ctx.lookup (ctx : Ctx) (id : Nat) : Option CoreType :=
  match ctx.find? fun (k, _) => k == id with
  | some (_, ty) => some ty
  | none => none

/-- Static typing judgment for unified sequential expressions. -/
inductive WellTyped : Ctx → CoreExpr → CoreType → Effect → Prop where
  | unit (ctx : Ctx) :
      WellTyped ctx .unit .unit .empty
  | bool (ctx : Ctx) (b : Bool) :
      WellTyped ctx (.bool b) .bool .empty
  | nat (ctx : Ctx) (n : Nat) :
      WellTyped ctx (.nat n) .nat .empty
  | int (ctx : Ctx) (s : Bool) (bits : Nat) (v : Int) :
      WellTyped ctx (.int s bits v) (.int s bits) .empty
  | pair {ctx : Ctx} {a b : CoreExpr} {tyA tyB : CoreType} {effA effB : Effect} :
      WellTyped ctx a tyA effA →
      WellTyped ctx b tyB effB →
      WellTyped ctx (.pair a b) (.prod tyA tyB) (effA.union effB)
  | fst {ctx : Ctx} {p : CoreExpr} {tyA tyB : CoreType} {eff : Effect} :
      WellTyped ctx p (.prod tyA tyB) eff →
      WellTyped ctx (.fst p) tyA eff
  | snd {ctx : Ctx} {p : CoreExpr} {tyA tyB : CoreType} {eff : Effect} :
      WellTyped ctx p (.prod tyA tyB) eff →
      WellTyped ctx (.snd p) tyB eff
  | adt {ctx : Ctx} (tag : Nat) {p : CoreExpr} {tyP : CoreType} {eff : Effect} :
      WellTyped ctx p tyP eff →
      WellTyped ctx (.adt tag p) (.adt tag tyP) eff
  | matchTag {ctx : Ctx} {s : CoreExpr} (tag : Nat) {pTy resTy : CoreType}
      {onMatch onElse : CoreExpr} {effS effM effE : Effect} :
      WellTyped ctx s (.adt tag pTy) effS →
      WellTyped ctx onMatch resTy effM →
      WellTyped ctx onElse resTy effE →
      WellTyped ctx (.matchTag s tag onMatch onElse) resTy (effS.union (effM.union effE))
  | matchBool {ctx : Ctx} {s : CoreExpr} {resTy : CoreType}
      {onTrue onFalse : CoreExpr} {effS effT effF : Effect} :
      WellTyped ctx s .bool effS →
      WellTyped ctx onTrue resTy effT →
      WellTyped ctx onFalse resTy effF →
      WellTyped ctx (.matchTag s 1 onTrue onFalse) resTy (effS.union (effT.union effF))
  | var {ctx : Ctx} (id : Nat) {ty : CoreType} :
      ctx.lookup id = some ty →
      WellTyped ctx (.var id) ty .empty
  | letBind {ctx : Ctx} (id : Nat) {v body : CoreExpr} {tyV tyBody : CoreType}
      {effV effBody : Effect} :
      WellTyped ctx v tyV effV →
      WellTyped ((id, tyV) :: ctx) body tyBody effBody →
      WellTyped ctx (.letBind id v body) tyBody (effV.union effBody)
  | alloc (ctx : Ctx) (sz : Nat) (init : UInt8) :
      WellTyped ctx (.alloc sz init) (.handle .byte) ⟨[], [[sz]], []⟩
  | readHandle (ctx : Ctx) (h off : Nat) :
      WellTyped ctx (.readHandle h off) .byte ⟨[[h, off]], [], []⟩
  | writeHandle {ctx : Ctx} (h off : Nat) {v : CoreExpr} {effV : Effect} :
      WellTyped ctx v .byte effV →
      WellTyped ctx (.writeHandle h off v) .unit (effV.union ⟨[], [[h, off]], []⟩)
  | borrowView {ctx : Ctx} (vId h : Nat) (mode : AccessMode) (off : Nat)
      {body : CoreExpr} {tyBody : CoreType} {effBody : Effect} :
      WellTyped ((vId, .view .byte mode) :: ctx) body tyBody effBody →
      WellTyped ctx (.borrowView vId h mode off body) tyBody effBody
  | readView (ctx : Ctx) (vId : Nat) :
      WellTyped ctx (.readView vId) .byte ⟨[[vId]], [], []⟩
  | writeView {ctx : Ctx} (vId : Nat) {v : CoreExpr} {effV : Effect} :
      WellTyped ctx v .byte effV →
      WellTyped ctx (.writeView vId v) .unit (effV.union ⟨[], [[vId]], []⟩)
  | lam {ctx : Ctx} (p : Nat) (tyP : CoreType) {body : CoreExpr} {tyBody : CoreType}
      (effBody : Effect) :
      WellTyped ((p, tyP) :: ctx) body tyBody effBody →
      WellTyped ctx (.lam p tyP body effBody) (.arrow tyP tyBody effBody) .empty
  | app {ctx : Ctx} {fn arg : CoreExpr} {dom cod : CoreType} {effBody effFn effArg : Effect} :
      WellTyped ctx fn (.arrow dom cod effBody) effFn →
      WellTyped ctx arg dom effArg →
      WellTyped ctx (.app fn arg) cod (effFn.union (effArg.union effBody))
  | loop {ctx : Ctx} {cond body : CoreExpr} {effC effB : Effect} :
      WellTyped ctx cond .bool effC →
      WellTyped ctx body .unit effB →
      WellTyped ctx (.loop cond body) .unit (effC.union effB)

end Aethel.CoreAST
