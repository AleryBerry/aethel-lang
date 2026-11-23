import Aethel.Structured
import Aethel.StructuredLaws

namespace Aethel

open Core Functional Structured

/-- Origin tracking for returned references and views. -/
inductive Origin where
  | param (index : Nat)
  | global
  | fresh
  deriving DecidableEq, Repr

def Origin.resolve (origin : Origin) (args : List HandleId) : Option HandleId :=
  match origin with
  | .param i => args[i]?
  | .global => none
  | .fresh => none

theorem Origin.resolve_param_in_bounds {args : List HandleId} {i : Nat}
    (h : i < args.length) :
    (Origin.param i).resolve args = some args[i] := by
  simp only [Origin.resolve, List.getElem?_eq_getElem h]

theorem Origin.resolve_param_none {args : List HandleId} {i : Nat}
    (h : args.length ≤ i) :
    (Origin.param i).resolve args = none := by
  simp only [Origin.resolve, List.getElem?_eq_none h]

/-- Rank-one polymorphic types with type variables. -/
inductive PolyTy where
  | var (id : Nat)
  | mono (ty : Ty)
  | arrow (input output : PolyTy)
  deriving DecidableEq, Repr

def PolyTy.subst (sub : List Ty) : PolyTy → Option Ty
  | .var id => sub[id]?
  | .mono ty => some ty
  | .arrow input output => do
    let inTy ← input.subst sub
    let outTy ← output.subst sub
    return .arrow inTy outTy

structure TypeScheme where
  arity : Nat
  body : PolyTy
  deriving DecidableEq, Repr

def TypeScheme.instantiate (scheme : TypeScheme) (args : List Ty) : Option Ty :=
  if args.length = scheme.arity then
    scheme.body.subst args
  else none

theorem TypeScheme.instantiate_mono (ty : Ty) :
    (TypeScheme.mk 0 (.mono ty)).instantiate [] = some ty := rfl

theorem TypeScheme.instantiate_arity_mismatch (scheme : TypeScheme) (args : List Ty)
    (h : args.length ≠ scheme.arity) :
    scheme.instantiate args = none := by
  simp [TypeScheme.instantiate, h]

theorem PolyTy.subst_mono (ty : Ty) (sub : List Ty) :
    (PolyTy.mono ty).subst sub = some ty := rfl

theorem PolyTy.subst_var_in_bounds {id : Nat} {sub : List Ty} (h : id < sub.length) :
    (PolyTy.var id).subst sub = some sub[id] := by
  simp only [PolyTy.subst, List.getElem?_eq_getElem h]

/-- General Algebraic Data Types (tagged sums with structured payloads). -/
structure VariantDef where
  tag : Nat
  name : String
  payloadTypes : List Ty
  deriving DecidableEq, Repr

structure ADTDef where
  name : String
  variants : List VariantDef
  deriving DecidableEq, Repr

def ADTDef.findVariant (adt : ADTDef) (tag : Nat) : Option VariantDef :=
  adt.variants.find? fun v => v.tag == tag

structure ADTValue (adt : ADTDef) where
  tag : Nat
  payloadLengths : Nat
  valid : ∃ v ∈ adt.variants, v.tag = tag ∧ v.payloadTypes.length = payloadLengths

def ADTDef.isExhaustive (adt : ADTDef) (coveredTags : List Nat) : Bool :=
  adt.variants.all fun v => coveredTags.contains v.tag

theorem ADTDef.exhaustive_covers {adt : ADTDef} {covered : List Nat}
    (exhaustive : adt.isExhaustive covered = true)
    (val : ADTValue adt) :
    covered.contains val.tag = true := by
  simp only [isExhaustive, List.all_eq_true] at exhaustive
  obtain ⟨v, hv, htag, _⟩ := val.valid
  rw [← htag]
  exact exhaustive v hv

def boolExhaustive (hasFalse hasTrue : Bool) : Bool := hasFalse && hasTrue

theorem boolExhaustive_covers {hasFalse hasTrue : Bool}
    (h : boolExhaustive hasFalse hasTrue = true) (b : Bool) :
    (b = false ∧ hasFalse = true) ∨ (b = true ∧ hasTrue = true) := by
  simp only [boolExhaustive, Bool.and_eq_true] at h
  cases b
  · exact Or.inl ⟨rfl, h.1⟩
  · exact Or.inr ⟨rfl, h.2⟩

def optionExhaustive (hasNone hasSome : Bool) : Bool := hasNone && hasSome

theorem optionExhaustive_covers {α : Type} {hasNone hasSome : Bool}
    (h : optionExhaustive hasNone hasSome = true) (o : Option α) :
    (o = none ∧ hasNone = true) ∨ (∃ x, o = some x ∧ hasSome = true) := by
  simp only [optionExhaustive, Bool.and_eq_true] at h
  cases o with
  | none => exact Or.inl ⟨rfl, h.1⟩
  | some x => exact Or.inr ⟨x, rfl, h.2⟩

def resultExhaustive (hasOk hasErr : Bool) : Bool := hasOk && hasErr

theorem resultExhaustive_covers {α ε : Type} {hasOk hasErr : Bool}
    (h : resultExhaustive hasOk hasErr = true) (r : Except ε α) :
    (∃ v, r = .ok v ∧ hasOk = true) ∨ (∃ e, r = .error e ∧ hasErr = true) := by
  simp only [resultExhaustive, Bool.and_eq_true] at h
  cases r with
  | ok v => exact Or.inl ⟨v, rfl, h.1⟩
  | error e => exact Or.inr ⟨e, rfl, h.2⟩

def intervalCoversFrom (hi cur : Int) : List (Int × Int) → Bool
  | [] => decide (hi < cur)
  | (a, b) :: rest =>
    if hi < cur then true
    else if a ≤ cur then
      let next := if cur ≤ b then b + 1 else cur
      intervalCoversFrom hi next rest
    else false

def intRangeExhaustive (lo hi : Int) (sortedIntervals : List (Int × Int)) : Bool :=
  intervalCoversFrom hi lo sortedIntervals

theorem intervalCoversFrom_sound {hi cur : Int} {ivs : List (Int × Int)}
    (hOk : intervalCoversFrom hi cur ivs = true) :
    ∀ x : Int, cur ≤ x → x ≤ hi → ∃ p ∈ ivs, p.1 ≤ x ∧ x ≤ p.2 := by
  induction ivs generalizing cur with
  | nil =>
    intro x hLo hHi
    simp only [intervalCoversFrom, decide_eq_true_eq] at hOk
    omega
  | cons p rest ih =>
    obtain ⟨a, b⟩ := p
    dsimp [intervalCoversFrom] at hOk
    by_cases hDone : hi < cur
    · intro x hLo hHi
      omega
    · by_cases hCover : a ≤ cur
      · simp only [hDone, ↓reduceIte, hCover] at hOk
        intro x hLo hHi
        let next := if cur ≤ b then b + 1 else cur
        have hRec := ih hOk x
        by_cases hIn : x ≤ b
        · exact ⟨(a, b), List.mem_cons.mpr (.inl rfl), by omega, hIn⟩
        · have hNextLeX : next ≤ x := by
            dsimp [next]
            split <;> omega
          obtain ⟨q, hqMem, hqLo, hqHi⟩ := hRec hNextLeX hHi
          exact ⟨q, List.mem_cons_of_mem _ hqMem, hqLo, hqHi⟩
      · simp only [hDone, ↓reduceIte, hCover] at hOk
        cases hOk

theorem intRangeExhaustive_covers {lo hi : Int} {ivs : List (Int × Int)}
    (hOk : intRangeExhaustive lo hi ivs = true) :
    ∀ x : Int, lo ≤ x → x ≤ hi → ∃ p ∈ ivs, p.1 ≤ x ∧ x ≤ p.2 :=
  intervalCoversFrom_sound hOk

/-- Effect footprints: accessed, modified, and invalidated paths. -/
structure Effect where
  reads : List (List Nat)
  writes : List (List Nat)
  invalidates : List (List Nat)
  deriving DecidableEq, Repr

def Effect.empty : Effect := ⟨[], [], []⟩

def Effect.union (e1 e2 : Effect) : Effect :=
  ⟨e1.reads ++ e2.reads, e1.writes ++ e2.writes, e1.invalidates ++ e2.invalidates⟩

@[simp]
theorem Effect.union_empty_left (e : Effect) : Effect.empty.union e = e := rfl

@[simp]
theorem Effect.union_empty_right (e : Effect) : e.union Effect.empty = e := by
  cases e
  simp [union, empty]

def pathConflicts (p1 p2 : List Nat) : Bool :=
  p1.isPrefixOf p2 || p2.isPrefixOf p1

theorem pathConflicts_symm (p1 p2 : List Nat) :
    pathConflicts p1 p2 = pathConflicts p2 p1 := by
  simp only [pathConflicts, Bool.or_comm]

def Effect.Disjoint (e1 e2 : Effect) : Prop :=
  (∀ w ∈ e1.writes, ∀ r ∈ e2.reads, pathConflicts w r = false) ∧
  (∀ w ∈ e1.writes, ∀ w2 ∈ e2.writes, pathConflicts w w2 = false) ∧
  (∀ w ∈ e2.writes, ∀ r ∈ e1.reads, pathConflicts w r = false) ∧
  (∀ inv ∈ e1.invalidates, ∀ r ∈ e2.reads, pathConflicts inv r = false) ∧
  (∀ inv ∈ e1.invalidates, ∀ w ∈ e2.writes, pathConflicts inv w = false) ∧
  (∀ inv ∈ e2.invalidates, ∀ r ∈ e1.reads, pathConflicts inv r = false) ∧
  (∀ inv ∈ e2.invalidates, ∀ w ∈ e1.writes, pathConflicts inv w = false)

theorem Effect.disjoint_empty (e : Effect) : Effect.Disjoint .empty e := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw; cases hw
  · intro w hw; cases hw
  · intro w _ r hr; cases hr
  · intro inv hinv; cases hinv
  · intro inv hinv; cases hinv
  · intro inv _ r hr; cases hr
  · intro inv _ w hw; cases hw

theorem Effect.disjoint_symm {e1 e2 : Effect} (h : Effect.Disjoint e1 e2) :
    Effect.Disjoint e2 e1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h3, fun w2 hw2 w1 hw1 => by rw [pathConflicts_symm]; exact h2 w1 hw1 w2 hw2,
    h1, h6, h7, h4, h5⟩

/-- Function summaries specify interface contracts: effects, origins, and schemes. -/
structure FunctionSummary where
  name : String
  scheme : TypeScheme
  effects : Effect
  returnedOrigin : Option Origin
  deriving DecidableEq, Repr

/-- Closure ownership and captured resources. -/
inductive CapturedResource where
  | handle (id : HandleId)
  | view (id : ViewId) (mode : AccessMode)
  deriving DecidableEq, Repr

structure Closure where
  captures : List CapturedResource
  codeId : Nat
  deriving DecidableEq, Repr

def Closure.handles (c : Closure) : List HandleId :=
  c.captures.filterMap fun cap =>
    match cap with | .handle id => some id | .view _ _ => none

def Closure.views (c : Closure) : List ViewId :=
  c.captures.filterMap fun cap =>
    match cap with | .handle _ => none | .view id _ => some id

def Closure.isLive (c : Closure) (state : State) : Prop :=
  ∀ cap ∈ c.captures,
    match cap with
    | .handle id => (state.handle id).isSome
    | .view id _ => (state.view id).isSome

theorem Closure.isLive_preserved {c : Closure} {s next : State}
    (hLive : c.isLive s)
    (hHandle : ∀ id ∈ c.handles, next.handle id = s.handle id)
    (hView : ∀ id ∈ c.views, next.view id = s.view id) :
    c.isLive next := by
  intro cap hcap
  cases cap with
  | handle id =>
    have inHandles : id ∈ c.handles := by
      simp only [Closure.handles, List.mem_filterMap]
      exact ⟨.handle id, hcap, rfl⟩
    dsimp [isLive]
    rw [hHandle id inHandles]
    have := hLive (.handle id) hcap
    dsimp [isLive] at this
    exact this
  | view id mode =>
    have inViews : id ∈ c.views := by
      simp only [Closure.views, List.mem_filterMap]
      exact ⟨.view id mode, hcap, rfl⟩
    dsimp [isLive]
    rw [hView id inViews]
    have := hLive (.view id mode) hcap
    dsimp [isLive] at this
    exact this

end Aethel
