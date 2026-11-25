import Aethel.StatusCodec
import Aethel.IntegerTypes

namespace Aethel.Functional

inductive Ty where
  | bool | nat | status
  | integer (kind : IntegerType)
  | option (element : Ty)
  | arrow (input output : Ty)
  deriving DecidableEq, Repr

abbrev Ty.byte : Ty := .integer (.unsigned .w8)
abbrev Ty.uint16 : Ty := .integer (.unsigned .w16)

abbrev Ty.Value : Ty → Type
  | .bool => Bool
  | .nat => Nat
  | .integer kind => kind.Value
  | .status => Status
  | .option element => Option element.Value
  | .arrow input output => input.Value → output.Value

/-- Decode two bytes in little-endian order without a native wide access. -/
def decodeUInt16LE (low high : UInt8) : UInt16 :=
  (low.toNat + 256 * high.toNat).toUInt16

theorem decodeUInt16LE_value (low high : UInt8) :
    (decodeUInt16LE low high).toNat = low.toNat + 256 * high.toNat := by
  simp only [decodeUInt16LE, UInt16.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by have l := low.toNat_lt; have h := high.toNat_lt; omega)

def splitLow (v : UInt16) : UInt8 :=
  v.toNat.toUInt8

def splitHigh (v : UInt16) : UInt8 :=
  (v.toNat / 256).toUInt8

theorem decodeUInt16LE_split (v : UInt16) :
    decodeUInt16LE (splitLow v) (splitHigh v) = v := by
  rw [← UInt16.toNat_inj]
  simp only [decodeUInt16LE_value, splitLow, splitHigh,
    UInt8.toNat_ofNat', Nat.toUInt8]
  change v.toNat % 256 + 256 * (v.toNat / 256 % 256) = v.toNat
  have vlt := v.toNat_lt
  have h2 : v.toNat / 256 < 256 := by
    have : v.toNat < 256 * 256 := vlt
    exact Nat.div_lt_of_lt_mul this
  rw [Nat.mod_eq_of_lt h2]
  rw [Nat.mul_comm 256]
  exact Nat.mod_add_div' v.toNat 256

/-- Unsigned saturating subtraction keeps the mathematical truncated difference. -/
def subtractByteSat (left right : UInt8) : UInt8 :=
  UInt8.ofNat (left.toNat - right.toNat)

theorem subtractByteSat_toNat (left right : UInt8) :
    (subtractByteSat left right).toNat = left.toNat - right.toNat := by
  simp only [subtractByteSat, UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le ..) left.toNat_lt)

theorem subtractByteSat_strict_decrease {left right : UInt8}
    (leftPositive : 0 < left.toNat) (rightPositive : 0 < right.toNat) :
    (subtractByteSat left right).toNat < left.toNat := by
  rw [subtractByteSat_toNat]
  omega

inductive Var : List Ty → Ty → Type where
  | here : Var (ty :: ctx) ty
  | there : Var ctx ty → Var (other :: ctx) ty

inductive Term : List Ty → Ty → Type where
  | var : Var ctx ty → Term ctx ty
  | nat : Nat → Term ctx .nat
  | integer (kind : IntegerType) (value : Int) (fits : kind.Fits value) : Term ctx (.integer kind)
  | byte : UInt8 → Term ctx .byte
  | uint16 : UInt16 → Term ctx .uint16
  | uint16Eq : Term ctx .uint16 → Term ctx .uint16 → Term ctx .bool
  | byteEq : Term ctx .byte → Term ctx .byte → Term ctx .bool
  | byteLt : Term ctx .byte → Term ctx .byte → Term ctx .bool
  | byteLe : Term ctx .byte → Term ctx .byte → Term ctx .bool
  | byteSubSat : Term ctx .byte → Term ctx .byte → Term ctx .byte
  | uint16Lt : Term ctx .uint16 → Term ctx .uint16 → Term ctx .bool
  | uint16Le : Term ctx .uint16 → Term ctx .uint16 → Term ctx .bool
  | bool : Bool → Term ctx .bool
  | status : Status → Term ctx .status
  | lam : Term (input :: ctx) output → Term ctx (.arrow input output)
  | app : Term ctx (.arrow input output) → Term ctx input → Term ctx output
  | branch : Term ctx .bool → Term ctx ty → Term ctx ty → Term ctx ty
  | none : Term ctx (.option ty)
  | some : Term ctx ty → Term ctx (.option ty)
  | optionCase : Term ctx (.option ty) → Term ctx result → Term (ty :: ctx) result → Term ctx result
  | encodeStatus : Term ctx .status → Term ctx .nat
  | decodeStatus : Term ctx .nat → Term ctx (.option .status)

structure Env (ctx : List Ty) where
  get : {ty : Ty} → Var ctx ty → ty.Value

def Env.empty : Env [] := ⟨fun v => nomatch v⟩

def Env.extend (env : Env ctx) (x : ty.Value) : Env (ty :: ctx) :=
  ⟨fun v => match v with
    | .here => x
    | .there outer => env.get outer⟩

/-- Total denotation of the pure typed fragment. Function values are modeled
extensionally. The elaborator admits no recursive binding or foreign call. -/
def Term.eval {ctx : List Ty} {ty : Ty} (env : Env ctx) : Term ctx ty → ty.Value
  | .var v => env.get v
  | .nat n => n
  | .integer kind value fits => kind.literalValue value fits
  | .byte b => b
  | .uint16 n => n
  | .uint16Eq a b => (show UInt16 from a.eval env) == b.eval env
  | .byteEq a b => (show UInt8 from a.eval env) == b.eval env
  | .byteLt a b => (show UInt8 from a.eval env) < b.eval env
  | .byteLe a b => (show UInt8 from a.eval env) ≤ b.eval env
  | .byteSubSat a b => subtractByteSat (a.eval env) (b.eval env)
  | .uint16Lt a b => (show UInt16 from a.eval env) < b.eval env
  | .uint16Le a b => (show UInt16 from a.eval env) ≤ b.eval env
  | .bool b => b
  | .status s => s
  | .lam body => fun x => body.eval (env.extend x)
  | .app f x =>
    let function := f.eval env
    let argument := x.eval env
    function argument
  | .branch cond yes no => if (show Bool from cond.eval env) then yes.eval env else no.eval env
  | .none => Option.none
  | .some value => Option.some (value.eval env)
  | .optionCase subject absent present =>
    match subject.eval env with
    | Option.none => absent.eval env
    | Option.some x => present.eval (env.extend x)
  | .encodeStatus value => Status.encode (value.eval env)
  | .decodeStatus value => Status.decode (value.eval env)

inductive Raw where
  | var (index : Nat)
  | nat (value : Nat)
  | integer (kind : IntegerType) (value : Int)
  | byte (value : UInt8)
  | uint16 (value : UInt16)
  | uint16Eq (left right : Raw)
  | byteEq (left right : Raw)
  | byteLt (left right : Raw)
  | byteLe (left right : Raw)
  | byteSubSat (left right : Raw)
  | uint16Lt (left right : Raw)
  | uint16Le (left right : Raw)
  | bool (value : Bool)
  | status (value : Status)
  | lam (input : Ty) (body : Raw)
  | app (function argument : Raw)
  | branch (condition yes no : Raw)
  | none (ty : Ty)
  | some (value : Raw)
  | optionCase (subject absent present : Raw)
  | encodeStatus (value : Raw)
  | decodeStatus (value : Raw)
  deriving Repr, DecidableEq

def Var.atIndex (ctx : List Ty) (index : Nat) : Option ((ty : Ty) × Var ctx ty) :=
  match ctx, index with
  | [], _ => none
  | ty :: _, 0 => some ⟨ty, .here⟩
  | _ :: rest, i + 1 => (atIndex rest i).map fun ⟨ty, v⟩ => ⟨ty, .there v⟩

inductive TypeError where
  | unbound (index : Nat)
  | expected (required actual : Ty)
  | expectedFunction (actual : Ty)
  | expectedOption (actual : Ty)
  | integerOutOfRange (kind : IntegerType) (value : Int)
  | translationMismatch
  deriving Repr, DecidableEq

private def expect (required : Ty) (inferred : (actual : Ty) × Term ctx actual) :
    Except TypeError (Term ctx required) :=
  if same : inferred.1 = required then .ok (same ▸ inferred.2)
  else .error (.expected required inferred.1)

/-- Elaboration produces a term indexed by its inferred type. -/
def infer (ctx : List Ty) : Raw → Except TypeError ((ty : Ty) × Term ctx ty)
  | .var i =>
    match Var.atIndex ctx i with
    | none => .error (.unbound i)
    | some ⟨ty, v⟩ => .ok ⟨ty, .var v⟩
  | .nat n => .ok ⟨.nat, .nat n⟩
  | .integer kind value =>
    if fits : kind.Fits value then .ok ⟨.integer kind, .integer kind value fits⟩
    else .error (.integerOutOfRange kind value)
  | .byte b => .ok ⟨.byte, .byte b⟩
  | .uint16 n => .ok ⟨.uint16, .uint16 n⟩
  | .uint16Eq a b => do
    let left ← expect .uint16 (← infer ctx a)
    let right ← expect .uint16 (← infer ctx b)
    return ⟨.bool, .uint16Eq left right⟩
  | .byteEq a b => do
    let left ← expect .byte (← infer ctx a)
    let right ← expect .byte (← infer ctx b)
    return ⟨.bool, .byteEq left right⟩
  | .byteLt a b => do
    let left ← expect .byte (← infer ctx a)
    let right ← expect .byte (← infer ctx b)
    return ⟨.bool, .byteLt left right⟩
  | .byteLe a b => do
    let left ← expect .byte (← infer ctx a)
    let right ← expect .byte (← infer ctx b)
    return ⟨.bool, .byteLe left right⟩
  | .byteSubSat a b => do
    let left ← expect .byte (← infer ctx a)
    let right ← expect .byte (← infer ctx b)
    return ⟨.byte, .byteSubSat left right⟩
  | .uint16Lt a b => do
    let left ← expect .uint16 (← infer ctx a)
    let right ← expect .uint16 (← infer ctx b)
    return ⟨.bool, .uint16Lt left right⟩
  | .uint16Le a b => do
    let left ← expect .uint16 (← infer ctx a)
    let right ← expect .uint16 (← infer ctx b)
    return ⟨.bool, .uint16Le left right⟩
  | .bool b => .ok ⟨.bool, .bool b⟩
  | .status s => .ok ⟨.status, .status s⟩
  | .lam input body => do
    let ⟨output, checked⟩ ← infer (input :: ctx) body
    return ⟨.arrow input output, .lam checked⟩
  | .app function argument => do
    match ← infer ctx function with
    | ⟨.arrow input output, checked⟩ =>
      let arg ← expect input (← infer ctx argument)
      return ⟨output, .app checked arg⟩
    | ⟨ty, _⟩ => .error (.expectedFunction ty)
  | .branch condition yes no => do
    let cond ← expect .bool (← infer ctx condition)
    let ⟨ty, thenTerm⟩ ← infer ctx yes
    let elseTerm ← expect ty (← infer ctx no)
    return ⟨ty, .branch cond thenTerm elseTerm⟩
  | .none ty => .ok ⟨.option ty, .none⟩
  | .some value => do
    let ⟨ty, checked⟩ ← infer ctx value
    return ⟨.option ty, .some checked⟩
  | .optionCase subject absent present => do
    match ← infer ctx subject with
    | ⟨.option element, checked⟩ =>
      let ⟨result, noValue⟩ ← infer ctx absent
      let hasValue ← expect result (← infer (element :: ctx) present)
      return ⟨result, .optionCase checked noValue hasValue⟩
    | ⟨ty, _⟩ => .error (.expectedOption ty)
  | .encodeStatus value => do
    let checked ← expect .status (← infer ctx value)
    return ⟨.nat, .encodeStatus checked⟩
  | .decodeStatus value => do
    let checked ← expect .nat (← infer ctx value)
    return ⟨.option .status, .decodeStatus checked⟩

def Var.index : Var ctx ty → Nat
  | .here => 0
  | .there outer => outer.index + 1

/-- Recover the raw syntax, including annotations, from an indexed term. -/
def Term.erase : Term ctx ty → Raw
  | .var v => .var v.index
  | .nat n => .nat n
  | .integer kind value _ => .integer kind value
  | .byte b => .byte b
  | .uint16 n => .uint16 n
  | .uint16Eq a b => .uint16Eq a.erase b.erase
  | .byteEq a b => .byteEq a.erase b.erase
  | .byteLt a b => .byteLt a.erase b.erase
  | .byteLe a b => .byteLe a.erase b.erase
  | .byteSubSat a b => .byteSubSat a.erase b.erase
  | .uint16Lt a b => .uint16Lt a.erase b.erase
  | .uint16Le a b => .uint16Le a.erase b.erase
  | .bool b => .bool b
  | .status s => .status s
  | .lam (input := input) body => .lam input body.erase
  | .app f x => .app f.erase x.erase
  | .branch cond yes no => .branch cond.erase yes.erase no.erase
  | .none (ty := element) => .none element
  | .some value => .some value.erase
  | .optionCase subject absent present => .optionCase subject.erase absent.erase present.erase
  | .encodeStatus value => .encodeStatus value.erase
  | .decodeStatus value => .decodeStatus value.erase

structure Elaboration (ctx : List Ty) (source : Raw) where
  ty : Ty
  term : Term ctx ty
  preservesSource : term.erase = source

/-- Validate fidelity before handing a typed term to consumers. The evidence
is erased at runtime. -/
def elaborate (ctx : List Ty) (source : Raw) : Except TypeError (Elaboration ctx source) := do
  let ⟨ty, term⟩ ← infer ctx source
  if preserves : term.erase = source then
    return ⟨ty, term, preserves⟩
  else .error .translationMismatch

/-- An evaluation derivation for the typed fragment. A semantic closure must
evaluate its body on every supplied argument. -/
inductive Evaluates : Env ctx → Term ctx ty → ty.Value → Prop where
  | var : Evaluates env (.var v) (env.get v)
  | nat : Evaluates env (.nat n) n
  | integer {fits : kind.Fits value} :
      Evaluates env (.integer kind value fits) (kind.literalValue value fits)
  | byte : Evaluates env (.byte b) b
  | uint16 : Evaluates env (.uint16 n) n
  | uint16Eq {a b : Term ctx .uint16} {x y : UInt16} :
      Evaluates env a x → Evaluates env b y → Evaluates env (.uint16Eq a b) (x == y)
  | byteEq {a b : Term ctx .byte} {x y : UInt8} :
      Evaluates env a x → Evaluates env b y → Evaluates env (.byteEq a b) (x == y)
  | byteLt {a b : Term ctx .byte} {x y : UInt8} :
      Evaluates env a x → Evaluates env b y → Evaluates env (.byteLt a b) (x < y)
  | byteLe {a b : Term ctx .byte} {x y : UInt8} :
      Evaluates env a x → Evaluates env b y → Evaluates env (.byteLe a b) (x ≤ y)
  | byteSubSat {a b : Term ctx .byte} {x y : UInt8} :
      Evaluates env a x → Evaluates env b y → Evaluates env (.byteSubSat a b) (subtractByteSat x y)
  | uint16Lt {a b : Term ctx .uint16} {x y : UInt16} :
      Evaluates env a x → Evaluates env b y → Evaluates env (.uint16Lt a b) (x < y)
  | uint16Le {a b : Term ctx .uint16} {x y : UInt16} :
      Evaluates env a x → Evaluates env b y → Evaluates env (.uint16Le a b) (x ≤ y)
  | bool : Evaluates env (.bool b) b
  | status : Evaluates env (.status s) s
  | lam (bodyRuns : ∀ x, Evaluates (Env.extend env x) body (f x)) :
      Evaluates env (.lam body) f
  | app : Evaluates env f function → Evaluates env arg value →
      Evaluates env (.app f arg) (function value)
  | ifTrue {cond : Term ctx .bool} : Evaluates env cond true → Evaluates env yes value →
      Evaluates env (.branch cond yes no) value
  | ifFalse {cond : Term ctx .bool} : Evaluates env cond false → Evaluates env no value →
      Evaluates env (.branch cond yes no) value
  | none : Evaluates env (.none (ty := element)) Option.none
  | some : Evaluates env term value → Evaluates env (.some term) (Option.some value)
  | optionAbsent {subject : Term ctx (.option ty)} : Evaluates env subject Option.none → Evaluates env absent value →
      Evaluates env (.optionCase subject absent present) value
  | optionPresent {subject : Term ctx (.option ty)} : Evaluates env subject (Option.some element) →
      Evaluates (Env.extend env element) present value →
      Evaluates env (.optionCase subject absent present) value
  | encodeStatus : Evaluates env term value →
      Evaluates env (.encodeStatus term) (Status.encode value)
  | decodeStatus : Evaluates env term value →
      Evaluates env (.decodeStatus term) (Status.decode value)

theorem Term.evaluates (term : Term ctx ty) (env : Env ctx) :
    Evaluates env term (term.eval env) := by
  induction term with
  | var => exact .var
  | nat => exact .nat
  | integer => exact .integer
  | byte => exact .byte
  | uint16 => exact .uint16
  | uint16Eq _ _ left right => exact .uint16Eq (left env) (right env)
  | byteEq _ _ left right => exact .byteEq (left env) (right env)
  | byteLt _ _ left right => exact .byteLt (left env) (right env)
  | byteLe _ _ left right => exact .byteLe (left env) (right env)
  | byteSubSat _ _ left right => exact .byteSubSat (left env) (right env)
  | uint16Lt _ _ left right => exact .uint16Lt (left env) (right env)
  | uint16Le _ _ left right => exact .uint16Le (left env) (right env)
  | bool => exact .bool
  | status => exact .status
  | lam _ ih => exact .lam fun x => ih (env.extend x)
  | app _ _ f x => exact .app (f env) (x env)
  | none => exact .none
  | some _ ih => exact .some (ih env)
  | encodeStatus _ ih => exact .encodeStatus (ih env)
  | decodeStatus _ ih => exact .decodeStatus (ih env)
  | branch cond _ _ hc hy hn =>
    cases h : cond.eval env <;> simp only [Term.eval, h, Bool.false_eq_true, ite_false, ite_true]
    · exact .ifFalse (h ▸ hc env) (hn env)
    · exact .ifTrue (h ▸ hc env) (hy env)
  | optionCase subject _ _ hs hn hy =>
    cases h : subject.eval env <;> simp only [Term.eval, h]
    · exact .optionAbsent (h ▸ hs env) (hn env)
    · exact .optionPresent (h ▸ hs env) (hy (env.extend _))

theorem Evaluates.agrees {ctx : List Ty} {ty : Ty} {env : Env ctx}
    {term : Term ctx ty} {value : ty.Value} (h : Evaluates env term value) :
    term.eval env = value := by
  induction h <;> simp_all [Term.eval] <;> rfl

end Aethel.Functional
