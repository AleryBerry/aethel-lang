import Aethel.Functions
import Aethel.Disjointness

namespace Aethel.Structured

open Functional

/-- Guard facts attach to an immutable byte binding, including a copied load. -/
structure ByteGuard (ctx : List Ty) where
  localByte : Var ctx .byte
  compared : UInt8

def ByteGuard.eval (guard : ByteGuard ctx) (env : Env ctx) : Bool :=
  env.get guard.localByte == guard.compared

def ByteGuard.ofCondition : Term ctx .bool → Option (ByteGuard ctx)
  | .byteEq (.var localByte) (.byte compared) => some ⟨localByte, compared⟩
  | .byteEq (.byte compared) (.var localByte) => some ⟨localByte, compared⟩
  | _ => none

theorem ByteGuard.ofCondition_sound {condition : Term ctx .bool} {guard : ByteGuard ctx}
    (found : ofCondition condition = some guard) (env : Env ctx) :
    guard.eval env = condition.eval env := by
  unfold ofCondition at found
  split at found <;> simp_all [ByteGuard.eval, Term.eval]
  all_goals subst guard
  all_goals try rfl
  exact Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact eq_comm)

private theorem same_index (x : Var ctx ty) : ∀ y : Var ctx ty, x.index = y.index → x = y := by
  induction x with
  | here => intro y same; cases y <;> simp_all [Var.index]
  | there x ih =>
    intro y same
    cases y with
    | here => simp [Var.index] at same
    | there y => exact congrArg Var.there (ih y (Nat.add_right_cancel same))

def Var.decEq (x y : Var ctx ty) : Decidable (x = y) :=
  if h : x.index = y.index then
    isTrue (same_index x y h)
  else
    isFalse (fun eq => h (congrArg Var.index eq))

instance : DecidableEq (Var ctx ty) := Var.decEq

/-- Extended guards over scalar bindings and variables. -/
inductive Guard (ctx : List Ty) where
  | byteConst (v : Var ctx .byte) (c : UInt8)
  | uint16Const (v : Var ctx .uint16) (c : UInt16)
  | byteVar (v1 v2 : Var ctx .byte)
  | uint16Var (v1 v2 : Var ctx .uint16)
  | byteLtConst (v : Var ctx .byte) (c : UInt8)
  | byteLeConst (v : Var ctx .byte) (c : UInt8)
  | uint16LtConst (v : Var ctx .uint16) (c : UInt16)
  | uint16LeConst (v : Var ctx .uint16) (c : UInt16)
  | byteInterval (v : Var ctx .byte) (lo hi : UInt8)
  | uint16Interval (v : Var ctx .uint16) (lo hi : UInt16)
  deriving DecidableEq

def Guard.eval (guard : Guard ctx) (env : Env ctx) : Bool :=
  match guard with
  | .byteConst v c => env.get v == c
  | .uint16Const v c => env.get v == c
  | .byteVar v1 v2 => env.get v1 == env.get v2
  | .uint16Var v1 v2 => env.get v1 == env.get v2
  | .byteLtConst v c => (env.get v < c : Bool)
  | .byteLeConst v c => (env.get v ≤ c : Bool)
  | .uint16LtConst v c => (env.get v < c : Bool)
  | .uint16LeConst v c => (env.get v ≤ c : Bool)
  | .byteInterval v lo hi => (lo ≤ env.get v : Bool) && (env.get v < hi : Bool)
  | .uint16Interval v lo hi => (lo ≤ env.get v : Bool) && (env.get v < hi : Bool)

def Guard.ofCondition : Term ctx .bool → Option (Guard ctx)
  | .byteEq (.var v) (.byte c) => some (.byteConst v c)
  | .byteEq (.byte c) (.var v) => some (.byteConst v c)
  | .byteEq (.var v1) (.var v2) => some (.byteVar v1 v2)
  | .uint16Eq (.var v) (.uint16 c) => some (.uint16Const v c)
  | .uint16Eq (.uint16 c) (.var v) => some (.uint16Const v c)
  | .uint16Eq (.var v1) (.var v2) => some (.uint16Var v1 v2)
  | .byteLt (.var v) (.byte c) => some (.byteLtConst v c)
  | .byteLe (.var v) (.byte c) => some (.byteLeConst v c)
  | .uint16Lt (.var v) (.uint16 c) => some (.uint16LtConst v c)
  | .uint16Le (.var v) (.uint16 c) => some (.uint16LeConst v c)
  | _ => none

theorem Guard.ofCondition_sound {condition : Term ctx .bool} {guard : Guard ctx}
    (found : ofCondition condition = some guard) (env : Env ctx) :
    guard.eval env = condition.eval env := by
  unfold ofCondition at found
  split at found <;> simp_all [Guard.eval, Term.eval]
  all_goals subst guard
  all_goals try rfl
  · exact Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact eq_comm)
  · exact Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact eq_comm)

def Guard.underBinder (guard : Guard ctx) (ty : Ty) : Guard (ty :: ctx) :=
  match guard with
  | .byteConst v c => .byteConst (.there v) c
  | .uint16Const v c => .uint16Const (.there v) c
  | .byteVar v1 v2 => .byteVar (.there v1) (.there v2)
  | .uint16Var v1 v2 => .uint16Var (.there v1) (.there v2)
  | .byteLtConst v c => .byteLtConst (.there v) c
  | .byteLeConst v c => .byteLeConst (.there v) c
  | .uint16LtConst v c => .uint16LtConst (.there v) c
  | .uint16LeConst v c => .uint16LeConst (.there v) c
  | .byteInterval v lo hi => .byteInterval (.there v) lo hi
  | .uint16Interval v lo hi => .uint16Interval (.there v) lo hi

theorem Guard.underBinder_eval {guard : Guard ctx} {env : Env ctx} (value : ty.Value) :
    (guard.underBinder ty).eval (env.extend value) = guard.eval env := by
  cases guard <;> rfl

structure BranchFact (ctx : List Ty) where
  guard : Guard ctx
  result : Bool
  deriving DecidableEq

abbrev BranchFacts (ctx : List Ty) := List (BranchFact ctx)

def BranchFacts.Valid (facts : BranchFacts ctx) (env : Env ctx) : Prop :=
  ∀ fact ∈ facts, fact.guard.eval env = fact.result

def BranchFacts.underBinder (facts : BranchFacts ctx) (ty : Ty) : BranchFacts (ty :: ctx) :=
  facts.map fun fact => ⟨fact.guard.underBinder ty, fact.result⟩

theorem BranchFacts.Valid.underBinder {facts : BranchFacts ctx} {env : Env ctx}
    (valid : facts.Valid env) (value : ty.Value) :
    (facts.underBinder ty).Valid (env.extend value) := by
  intro fact member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  simp only [Guard.underBinder_eval]
  exact valid original present

def BranchFacts.learn (facts : BranchFacts ctx) (condition : Term ctx .bool)
    (result : Bool) : BranchFacts ctx :=
  match Guard.ofCondition condition with
  | some guard => ⟨guard, result⟩ :: facts
  | none => facts

theorem BranchFacts.Valid.learn {facts : BranchFacts ctx} {env : Env ctx}
    (valid : facts.Valid env) {condition : Term ctx .bool} {result : Bool}
    (evaluated : condition.eval env = result) : (facts.learn condition result).Valid env := by
  unfold BranchFacts.learn
  split
  next guard found =>
    intro fact member
    exact (List.mem_cons.mp member).elim
      (fun equal => equal ▸ (Guard.ofCondition_sound found env).trans evaluated)
      (valid fact)
  next => exact valid

theorem byte_lt_sound (v c fc : UInt8) (hfc : (v < fc : Bool) = true) (hle : fc ≤ c) :
    (v < c : Bool) = true := by
  simp only [decide_eq_true_eq] at hfc ⊢
  have : v.toNat < fc.toNat := hfc
  have : fc.toNat ≤ c.toNat := hle
  show v.toNat < c.toNat
  omega

theorem byte_nlt_sound (v c fc : UInt8) (hnfc : (v < fc : Bool) = false) (hle : c ≤ fc) :
    (v < c : Bool) = false := by
  simp only [decide_eq_false_iff_not] at hnfc ⊢
  have : ¬ (v.toNat < fc.toNat) := hnfc
  have : c.toNat ≤ fc.toNat := hle
  show ¬ (v.toNat < c.toNat)
  omega

theorem byte_le_sound (v c fc : UInt8) (hfc : (v ≤ fc : Bool) = true) (hle : fc ≤ c) :
    (v ≤ c : Bool) = true := by
  simp only [decide_eq_true_eq] at hfc ⊢
  have : v.toNat ≤ fc.toNat := hfc
  have : fc.toNat ≤ c.toNat := hle
  show v.toNat ≤ c.toNat
  omega

theorem byte_nle_sound (v c fc : UInt8) (hnfc : (v ≤ fc : Bool) = false) (hle : c ≤ fc) :
    (v ≤ c : Bool) = false := by
  simp only [decide_eq_false_iff_not] at hnfc ⊢
  have : ¬ (v.toNat ≤ fc.toNat) := hnfc
  have : c.toNat ≤ fc.toNat := hle
  show ¬ (v.toNat ≤ c.toNat)
  omega

theorem byte_lt_le_sound (v c fc : UInt8) (hfc : (v < fc : Bool) = true) (hle : fc ≤ c) :
    (v ≤ c : Bool) = true := by
  simp only [decide_eq_true_eq] at hfc ⊢
  have : v.toNat < fc.toNat := hfc
  have : fc.toNat ≤ c.toNat := hle
  show v.toNat ≤ c.toNat
  omega

theorem byte_lt_ne_sound (v c fc : UInt8) (hfc : (v < fc : Bool) = true) (hle : fc ≤ c) :
    (v == c) = false := by
  simp only [decide_eq_true_eq] at hfc
  have hne : v ≠ c := by
    intro heq
    have : v.toNat = c.toNat := congrArg UInt8.toNat heq
    have : v.toNat < fc.toNat := hfc
    have : fc.toNat ≤ c.toNat := hle
    omega
  simp [hne]

theorem uint16_lt_sound (v c fc : UInt16) (hfc : (v < fc : Bool) = true) (hle : fc ≤ c) :
    (v < c : Bool) = true := by
  simp only [decide_eq_true_eq] at hfc ⊢
  have : v.toNat < fc.toNat := hfc
  have : fc.toNat ≤ c.toNat := hle
  show v.toNat < c.toNat
  omega

theorem uint16_nlt_sound (v c fc : UInt16) (hnfc : (v < fc : Bool) = false) (hle : c ≤ fc) :
    (v < c : Bool) = false := by
  simp only [decide_eq_false_iff_not] at hnfc ⊢
  have : ¬ (v.toNat < fc.toNat) := hnfc
  have : c.toNat ≤ fc.toNat := hle
  show ¬ (v.toNat < c.toNat)
  omega

theorem uint16_le_sound (v c fc : UInt16) (hfc : (v ≤ fc : Bool) = true) (hle : fc ≤ c) :
    (v ≤ c : Bool) = true := by
  simp only [decide_eq_true_eq] at hfc ⊢
  have : v.toNat ≤ fc.toNat := hfc
  have : fc.toNat ≤ c.toNat := hle
  show v.toNat ≤ c.toNat
  omega

theorem uint16_nle_sound (v c fc : UInt16) (hnfc : (v ≤ fc : Bool) = false) (hle : c ≤ fc) :
    (v ≤ c : Bool) = false := by
  simp only [decide_eq_false_iff_not] at hnfc ⊢
  have : ¬ (v.toNat ≤ fc.toNat) := hnfc
  have : c.toNat ≤ fc.toNat := hle
  show ¬ (v.toNat ≤ c.toNat)
  omega

theorem uint16_lt_le_sound (v c fc : UInt16) (hfc : (v < fc : Bool) = true) (hle : fc ≤ c) :
    (v ≤ c : Bool) = true := by
  simp only [decide_eq_true_eq] at hfc ⊢
  have : v.toNat < fc.toNat := hfc
  have : fc.toNat ≤ c.toNat := hle
  show v.toNat ≤ c.toNat
  omega

theorem uint16_lt_ne_sound (v c fc : UInt16) (hfc : (v < fc : Bool) = true) (hle : fc ≤ c) :
    (v == c) = false := by
  simp only [decide_eq_true_eq] at hfc
  have hne : v ≠ c := by
    intro heq
    have : v.toNat = c.toNat := congrArg UInt16.toNat heq
    have : v.toNat < fc.toNat := hfc
    have : fc.toNat ≤ c.toNat := hle
    omega
  simp [hne]

/-- Intersect facts known across two diverging branch arms at their join point. -/
def BranchFacts.join (facts1 facts2 : BranchFacts ctx) : BranchFacts ctx :=
  facts1.filter fun f => facts2.any fun f2 => decide (f = f2)

theorem BranchFacts.join_valid_left {facts1 facts2 : BranchFacts ctx} {env : Env ctx}
    (valid : facts1.Valid env) : (facts1.join facts2).Valid env := by
  intro fact member
  have in1 : fact ∈ facts1 := (List.mem_filter.mp member).1
  exact valid fact in1

theorem BranchFacts.join_valid_right {facts1 facts2 : BranchFacts ctx} {env : Env ctx}
    (valid : facts2.Valid env) : (facts1.join facts2).Valid env := by
  intro fact member
  have matched : (facts2.any fun f => decide (fact = f)) = true :=
    (List.mem_filter.mp member).2
  simp only [List.any_eq_true, decide_eq_true_eq] at matched
  obtain ⟨a, ha, eq⟩ := matched
  subst eq
  exact valid fact ha

theorem BranchFacts.join_sound {facts1 facts2 : BranchFacts ctx} {env : Env ctx}
    (either : facts1.Valid env ∨ facts2.Valid env) : (facts1.join facts2).Valid env := by
  cases either with
  | inl h1 => exact join_valid_left h1
  | inr h2 => exact join_valid_right h2

def BranchFacts.resolve (facts : BranchFacts ctx) (condition : Term ctx .bool) : Option Bool := do
  let guard ← Guard.ofCondition condition
  match guard with
  | .byteConst v c =>
    let fact ← facts.find? fun f =>
      match f.guard with
      | .byteConst fv fc => fv = v && (f.result || fc == c)
      | .byteLtConst fv fc => fv = v && f.result && fc ≤ c
      | _ => false
    match fact.guard with
    | .byteConst _ fc => return fact.result && (fc == c)
    | .byteLtConst _ _ => return false
    | _ => none
  | .uint16Const v c =>
    let fact ← facts.find? fun f =>
      match f.guard with
      | .uint16Const fv fc => fv = v && (f.result || fc == c)
      | .uint16LtConst fv fc => fv = v && f.result && fc ≤ c
      | _ => false
    match fact.guard with
    | .uint16Const _ fc => return fact.result && (fc == c)
    | .uint16LtConst _ _ => return false
    | _ => none
  | .byteVar v1 v2 =>
    if v1 = v2 then some true
    else
      let fact ← facts.find? fun f =>
        match f.guard with
        | .byteVar fv1 fv2 => (fv1 = v1 && fv2 = v2) || (fv1 = v2 && fv2 = v1)
        | _ => false
      return fact.result
  | .uint16Var v1 v2 =>
    if v1 = v2 then some true
    else
      let fact ← facts.find? fun f =>
        match f.guard with
        | .uint16Var fv1 fv2 => (fv1 = v1 && fv2 = v2) || (fv1 = v2 && fv2 = v1)
        | _ => false
      return fact.result
  | .byteLtConst v c =>
    let fact ← facts.find? fun f =>
      match f.guard with
      | .byteLtConst fv fc => fv = v && ((f.result && fc ≤ c) || (!f.result && c ≤ fc))
      | .byteConst fv _ => fv = v && f.result
      | _ => false
    match fact.guard with
    | .byteLtConst _ _ => return fact.result
    | .byteConst _ fc => return fc < c
    | _ => none
  | .byteLeConst v c =>
    let fact ← facts.find? fun f =>
      match f.guard with
      | .byteLeConst fv fc => fv = v && ((f.result && fc ≤ c) || (!f.result && c ≤ fc))
      | .byteLtConst fv fc => fv = v && f.result && fc ≤ c
      | .byteConst fv _ => fv = v && f.result
      | _ => false
    match fact.guard with
    | .byteLeConst _ _ => return fact.result
    | .byteLtConst _ _ => return true
    | .byteConst _ fc => return fc ≤ c
    | _ => none
  | .uint16LtConst v c =>
    let fact ← facts.find? fun f =>
      match f.guard with
      | .uint16LtConst fv fc => fv = v && ((f.result && fc ≤ c) || (!f.result && c ≤ fc))
      | .uint16Const fv _ => fv = v && f.result
      | _ => false
    match fact.guard with
    | .uint16LtConst _ _ => return fact.result
    | .uint16Const _ fc => return fc < c
    | _ => none
  | .uint16LeConst v c =>
    let fact ← facts.find? fun f =>
      match f.guard with
      | .uint16LeConst fv fc => fv = v && ((f.result && fc ≤ c) || (!f.result && c ≤ fc))
      | .uint16LtConst fv fc => fv = v && f.result && fc ≤ c
      | .uint16Const fv _ => fv = v && f.result
      | _ => false
    match fact.guard with
    | .uint16LeConst _ _ => return fact.result
    | .uint16LtConst _ _ => return true
    | .uint16Const _ fc => return fc ≤ c
    | _ => none
  | .byteInterval _ _ _ => none
  | .uint16Interval _ _ _ => none

theorem BranchFacts.resolve_sound {facts : BranchFacts ctx} {env : Env ctx}
    (valid : facts.Valid env) {condition : Term ctx .bool} {result : Bool}
    (resolved : facts.resolve condition = some result) : condition.eval env = result := by
  simp only [BranchFacts.resolve, bind, pure, Option.bind_eq_some_iff] at resolved
  obtain ⟨guard, recognized, res⟩ := resolved
  have guardSound := Guard.ofCondition_sound recognized env
  rw [← guardSound]
  cases guard with
  | byteConst v c =>
    simp only [Option.bind_eq_some_iff] at res
    obtain ⟨fact, found, eq⟩ := res
    have inFacts := List.mem_of_find?_eq_some found
    have factValid := valid fact inFacts
    have condMatch := List.find?_some found
    split at condMatch
    · rename_i fv fc hguard
      rw [hguard] at eq
      simp only [Option.some.injEq] at eq
      subst eq
      rw [hguard] at factValid
      dsimp [Guard.eval] at factValid
      dsimp [Guard.eval]
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at condMatch
      have hfv := condMatch.1
      subst hfv
      rcases condMatch.2 with hres | hfc
      · rw [hres] at factValid
        simp only [beq_iff_eq] at factValid
        rw [factValid, hres]
        rfl
      · subst hfc
        rw [factValid]
        simp
    · rename_i fv fc hguard
      rw [hguard] at eq
      simp only [Option.some.injEq] at eq
      subst eq
      rw [hguard] at factValid
      dsimp [Guard.eval] at factValid
      dsimp [Guard.eval]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at condMatch
      obtain ⟨⟨hfv, hres⟩, hle⟩ := condMatch
      subst hfv
      rw [hres] at factValid
      exact byte_lt_ne_sound (env.get fv) c fc factValid hle
    · contradiction
  | uint16Const v c =>
    simp only [Option.bind_eq_some_iff] at res
    obtain ⟨fact, found, eq⟩ := res
    have inFacts := List.mem_of_find?_eq_some found
    have factValid := valid fact inFacts
    have condMatch := List.find?_some found
    split at condMatch
    · rename_i fv fc hguard
      rw [hguard] at eq
      simp only [Option.some.injEq] at eq
      subst eq
      rw [hguard] at factValid
      dsimp [Guard.eval] at factValid
      dsimp [Guard.eval]
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at condMatch
      have hfv := condMatch.1
      subst hfv
      rcases condMatch.2 with hres | hfc
      · rw [hres] at factValid
        simp only [beq_iff_eq] at factValid
        rw [factValid, hres]
        rfl
      · subst hfc
        rw [factValid]
        simp
    · rename_i fv fc hguard
      rw [hguard] at eq
      simp only [Option.some.injEq] at eq
      subst eq
      rw [hguard] at factValid
      dsimp [Guard.eval] at factValid
      dsimp [Guard.eval]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at condMatch
      obtain ⟨⟨hfv, hres⟩, hle⟩ := condMatch
      subst hfv
      rw [hres] at factValid
      exact uint16_lt_ne_sound (env.get fv) c fc factValid hle
    · contradiction
  | byteVar v1 v2 =>
    dsimp at res
    split at res
    · rename_i heq
      subst heq
      cases res
      dsimp [Guard.eval]
      simp
    · rename_i hne
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at res
      obtain ⟨fact, found, rfl⟩ := res
      have inFacts := List.mem_of_find?_eq_some found
      have factValid := valid fact inFacts
      have condMatch := List.find?_some found
      split at condMatch
      · rename_i fv1 fv2 hguard
        rw [hguard] at factValid
        dsimp [Guard.eval] at factValid
        dsimp [Guard.eval]
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at condMatch
        rcases condMatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact factValid
        · rw [← factValid]
          exact Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact eq_comm)
      · contradiction
  | uint16Var v1 v2 =>
    dsimp at res
    split at res
    · rename_i heq
      subst heq
      cases res
      dsimp [Guard.eval]
      simp
    · rename_i hne
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at res
      obtain ⟨fact, found, rfl⟩ := res
      have inFacts := List.mem_of_find?_eq_some found
      have factValid := valid fact inFacts
      have condMatch := List.find?_some found
      split at condMatch
      · rename_i fv1 fv2 hguard
        rw [hguard] at factValid
        dsimp [Guard.eval] at factValid
        dsimp [Guard.eval]
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at condMatch
        rcases condMatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact factValid
        · rw [← factValid]
          exact Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq]; exact eq_comm)
      · contradiction
  | byteLtConst v c =>
    simp only [Option.bind_eq_some_iff] at res
    obtain ⟨fact, found, eq⟩ := res
    have inFacts := List.mem_of_find?_eq_some found
    have factValid := valid fact inFacts
    have condMatch := List.find?_some found
    split at condMatch
    · rename_i fv fc hguard
      rw [hguard] at eq
      simp only [Option.some.injEq] at eq
      subst eq
      rw [hguard] at factValid
      dsimp [Guard.eval] at factValid
      dsimp [Guard.eval]
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at condMatch
      obtain ⟨hfv, hmatch⟩ := condMatch
      subst hfv
      rcases hmatch with ⟨hres, hle⟩ | ⟨hnres, hle⟩
      · rw [hres] at factValid ⊢
        exact byte_lt_sound (env.get fv) c fc factValid hle
      · simp only [Bool.not_eq_true'] at hnres
        rw [hnres] at factValid ⊢
        exact byte_nlt_sound (env.get fv) c fc factValid hle
    · rename_i fv fc hguard
      rw [hguard] at eq
      simp only [Option.some.injEq] at eq
      subst eq
      rw [hguard] at factValid
      dsimp [Guard.eval] at factValid
      dsimp [Guard.eval]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at condMatch
      obtain ⟨hfv, hres⟩ := condMatch
      subst hfv
      rw [hres] at factValid
      simp only [beq_iff_eq] at factValid
      subst factValid
      rfl
    · contradiction
  | byteLeConst v c =>
    simp only [Option.bind_eq_some_iff] at res
    obtain ⟨fact, found, eq⟩ := res
    have inFacts := List.mem_of_find?_eq_some found
    have factValid := valid fact inFacts
    have condMatch := List.find?_some found
    split at condMatch
    · rename_i fv fc hguard
      rw [hguard] at eq
      simp only [Option.some.injEq] at eq
      subst eq
      rw [hguard] at factValid
      dsimp [Guard.eval] at factValid
      dsimp [Guard.eval]
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at condMatch
      obtain ⟨hfv, hmatch⟩ := condMatch
      subst hfv
      rcases hmatch with ⟨hres, hle⟩ | ⟨hnres, hle⟩
      · rw [hres] at factValid ⊢
        exact byte_le_sound (env.get fv) c fc factValid hle
      · simp only [Bool.not_eq_true'] at hnres
        rw [hnres] at factValid ⊢
        exact byte_nle_sound (env.get fv) c fc factValid hle
    · rename_i fv fc hguard
      rw [hguard] at eq
      simp only [Option.some.injEq] at eq
      subst eq
      rw [hguard] at factValid
      dsimp [Guard.eval] at factValid
      dsimp [Guard.eval]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at condMatch
      obtain ⟨⟨hfv, hres⟩, hle⟩ := condMatch
      subst hfv
      rw [hres] at factValid
      exact byte_lt_le_sound (env.get fv) c fc factValid hle
    · rename_i fv fc hguard
      rw [hguard] at eq
      simp only [Option.some.injEq] at eq
      subst eq
      rw [hguard] at factValid
      dsimp [Guard.eval] at factValid
      dsimp [Guard.eval]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at condMatch
      obtain ⟨hfv, hres⟩ := condMatch
      subst hfv
      rw [hres] at factValid
      simp only [beq_iff_eq] at factValid
      subst factValid
      rfl
    · contradiction
  | uint16LtConst v c =>
    simp only [Option.bind_eq_some_iff] at res
    obtain ⟨fact, found, eq⟩ := res
    have inFacts := List.mem_of_find?_eq_some found
    have factValid := valid fact inFacts
    have condMatch := List.find?_some found
    split at condMatch
    · rename_i fv fc hguard
      rw [hguard] at eq
      simp only [Option.some.injEq] at eq
      subst eq
      rw [hguard] at factValid
      dsimp [Guard.eval] at factValid
      dsimp [Guard.eval]
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at condMatch
      obtain ⟨hfv, hmatch⟩ := condMatch
      subst hfv
      rcases hmatch with ⟨hres, hle⟩ | ⟨hnres, hle⟩
      · rw [hres] at factValid ⊢
        exact uint16_lt_sound (env.get fv) c fc factValid hle
      · simp only [Bool.not_eq_true'] at hnres
        rw [hnres] at factValid ⊢
        exact uint16_nlt_sound (env.get fv) c fc factValid hle
    · rename_i fv fc hguard
      rw [hguard] at eq
      simp only [Option.some.injEq] at eq
      subst eq
      rw [hguard] at factValid
      dsimp [Guard.eval] at factValid
      dsimp [Guard.eval]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at condMatch
      obtain ⟨hfv, hres⟩ := condMatch
      subst hfv
      rw [hres] at factValid
      simp only [beq_iff_eq] at factValid
      subst factValid
      rfl
    · contradiction
  | uint16LeConst v c =>
    simp only [Option.bind_eq_some_iff] at res
    obtain ⟨fact, found, eq⟩ := res
    have inFacts := List.mem_of_find?_eq_some found
    have factValid := valid fact inFacts
    have condMatch := List.find?_some found
    split at condMatch
    · rename_i fv fc hguard
      rw [hguard] at eq
      simp only [Option.some.injEq] at eq
      subst eq
      rw [hguard] at factValid
      dsimp [Guard.eval] at factValid
      dsimp [Guard.eval]
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at condMatch
      obtain ⟨hfv, hmatch⟩ := condMatch
      subst hfv
      rcases hmatch with ⟨hres, hle⟩ | ⟨hnres, hle⟩
      · rw [hres] at factValid ⊢
        exact uint16_le_sound (env.get fv) c fc factValid hle
      · simp only [Bool.not_eq_true'] at hnres
        rw [hnres] at factValid ⊢
        exact uint16_nle_sound (env.get fv) c fc factValid hle
    · rename_i fv fc hguard
      rw [hguard] at eq
      simp only [Option.some.injEq] at eq
      subst eq
      rw [hguard] at factValid
      dsimp [Guard.eval] at factValid
      dsimp [Guard.eval]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at condMatch
      obtain ⟨⟨hfv, hres⟩, hle⟩ := condMatch
      subst hfv
      rw [hres] at factValid
      exact uint16_lt_le_sound (env.get fv) c fc factValid hle
    · rename_i fv fc hguard
      rw [hguard] at eq
      simp only [Option.some.injEq] at eq
      subst eq
      rw [hguard] at factValid
      dsimp [Guard.eval] at factValid
      dsimp [Guard.eval]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at condMatch
      obtain ⟨hfv, hres⟩ := condMatch
      subst hfv
      rw [hres] at factValid
      simp only [beq_iff_eq] at factValid
      subst factValid
      rfl
    · contradiction
  | byteInterval _ _ _ => contradiction
  | uint16Interval _ _ _ => contradiction

def BranchFacts.checkArms (facts : BranchFacts ctx) (condition : Term ctx .bool)
    (yes no : BranchFacts ctx → Bool) : Bool :=
  let yesFacts := facts.learn condition true
  let noFacts := facts.learn condition false
  match facts.resolve condition with
  | some true => yes yesFacts
  | some false => no noFacts
  | none => yes yesFacts && no noFacts

theorem BranchFacts.checkArms_sound {facts : BranchFacts ctx} {env : Env ctx}
    {condition : Term ctx .bool} {yes no : BranchFacts ctx → Bool} {result : Bool}
    (valid : facts.Valid env) (evaluated : condition.eval env = result)
    (checked : facts.checkArms condition yes no = true) :
    (if result then yes (facts.learn condition true) else no (facts.learn condition false)) = true := by
  cases found : facts.resolve condition with
  | none =>
    have both := Bool.and_eq_true_iff.mp (by simpa only [checkArms, found] using checked)
    cases result
    · exact both.2
    · exact both.1
  | some known =>
    have equal := (resolve_sound valid found).symm.trans evaluated
    subst known
    cases result <;> simpa [checkArms, found] using checked

private def Guard.bytePeer (guard : Guard ctx) (v : Var ctx .byte) : Option (Var ctx .byte) :=
  match guard with
  | .byteVar left right =>
    if v = left then some right else if v = right then some left else none
  | _ => none

private theorem Guard.bytePeer_sound {guard : Guard ctx} {v peer : Var ctx .byte}
    (found : guard.bytePeer v = some peer) (env : Env ctx) : guard.eval env = (env.get v == env.get peer) := by
  cases guard <;> simp only [bytePeer, reduceCtorEq] at found
  case byteVar left right =>
    split at found
    · rename_i same
      subst v
      cases found
      rfl
    · obtain ⟨rfl, same⟩ := Option.ite_none_right_eq_some.mp found
      cases same
      exact Bool.eq_iff_iff.mpr (by simp only [Guard.eval, beq_iff_eq]; exact eq_comm)

private def BranchFacts.excludesBytePeer (facts : BranchFacts ctx) : Term ctx .byte → UInt8 → Bool
  | .var v, value =>
    facts.any fun fact => (fact.guard.bytePeer v).any fun peer =>
      facts.resolve (.byteEq (.var peer) (.byte value)) == some (!fact.result)
  | _, _ => false

private theorem BranchFacts.excludesBytePeer_sound {facts : BranchFacts ctx} {env : Env ctx}
    (valid : facts.Valid env) {term : Term ctx .byte} {value : UInt8}
    (observed : term.eval env = value) : facts.excludesBytePeer term value = false := by
  cases term <;> try rfl
  case var v =>
    apply Bool.eq_false_iff.mpr
    intro excluded
    obtain ⟨fact, member, excluded⟩ := List.any_eq_true.mp excluded
    obtain ⟨peer, found, disagrees⟩ := (Option.any_eq_true _ _).mp excluded
    have relation := (Guard.bytePeer_sound found env).symm.trans (valid fact member)
    have other := BranchFacts.resolve_sound valid (beq_iff_eq.mp disagrees)
    change (env.get peer == value) = !fact.result at other
    change env.get v = value at observed
    rw [observed] at relation
    rw [BEq.comm] at relation
    have impossible := relation.symm.trans other
    generalize fact.result = result at impossible
    cases result <;> contradiction

/-- A byte dispatch checks reachability and records the value of a
captured operand. Equality and inequality facts can constrain its peers. -/
def BranchFacts.byteCase (facts : BranchFacts ctx) (operand : Term ctx .byte) (index : Fin 256) :
    Option (BranchFacts ctx) :=
  let value := UInt8.ofFin index
  let selected := Term.byteEq operand (.byte value)
  if facts.resolve selected == some false || facts.excludesBytePeer operand value then none
  else some (facts.learn selected true)

theorem BranchFacts.byteCase_reachable {facts : BranchFacts ctx} {env : Env ctx}
    (valid : facts.Valid env) (operand : Term ctx .byte) :
    ∃ selected, facts.byteCase operand (operand.eval env : UInt8).toFin = some selected ∧ selected.Valid env := by
  let condition := Term.byteEq operand (.byte (UInt8.ofFin (operand.eval env : UInt8).toFin))
  have evaluated : condition.eval env = true := by
    change ((operand.eval env : UInt8) == UInt8.ofFin (operand.eval env : UInt8).toFin) = true
    simp
  have possible : facts.resolve condition ≠ some false := by
    intro impossible
    exact Bool.noConfusion ((BranchFacts.resolve_sound valid impossible).symm.trans evaluated)
  refine ⟨facts.learn condition true, ?_, valid.learn evaluated⟩
  have peer := BranchFacts.excludesBytePeer_sound valid (term := operand)
    (value := UInt8.ofFin (operand.eval env : UInt8).toFin) (by simp)
  change (if facts.resolve condition == some false ||
      facts.excludesBytePeer operand (UInt8.ofFin (operand.eval env : UInt8).toFin) then none
    else some (facts.learn condition true)) = some (facts.learn condition true)
  rw [beq_false_of_ne possible, peer]
  rfl

private def allBytes : Interval := ⟨0, 256⟩

private def oneByte (byte : UInt8) : Interval := ⟨byte.toNat, byte.toNat + 1⟩

private def byteCut (exclusiveBound : Nat) (result : Bool) : Interval :=
  if result then ⟨0, exclusiveBound⟩ else ⟨exclusiveBound, 256⟩

private theorem allBytes_contains (byte : UInt8) : allBytes.Contains byte.toNat :=
  ⟨Nat.zero_le _, byte.toNat_lt⟩

private theorem oneByte_contains (byte : UInt8) : (oneByte byte).Contains byte.toNat :=
  ⟨Nat.le_refl _, Nat.lt_succ_self _⟩

private theorem byteCut_contains {byte : UInt8} {bound : Nat} {result : Bool}
    (tested : decide (byte.toNat < bound) = result) : (byteCut bound result).Contains byte.toNat := by
  cases result
  · exact ⟨Nat.le_of_not_lt (of_decide_eq_false tested), byte.toNat_lt⟩
  · exact ⟨Nat.zero_le _, of_decide_eq_true tested⟩

private def BranchFact.byteInterval (fact : BranchFact ctx) (slot : Var ctx .byte) : Interval :=
  match fact.guard with
  | .byteConst tested value =>
    if tested = slot ∧ fact.result = true then oneByte value else allBytes
  | .byteLtConst tested bound =>
    if tested = slot then byteCut bound.toNat fact.result else allBytes
  | .byteLeConst tested bound =>
    if tested = slot then byteCut (bound.toNat + 1) fact.result else allBytes
  | _ => allBytes

private theorem BranchFact.byteInterval_sound {fact : BranchFact ctx} {env : Env ctx}
    (valid : fact.guard.eval env = fact.result) (target : Var ctx .byte) :
    (fact.byteInterval target).Contains (env.get target).toNat := by
  cases fact with
  | mk guard result =>
    cases guard <;> try exact allBytes_contains (env.get target)
    case byteConst tested value =>
      simp only [byteInterval]
      split
      · rename_i same
        obtain ⟨rfl, rfl⟩ := same
        exact (beq_iff_eq.mp valid) ▸ oneByte_contains value
      · exact allBytes_contains _
    case byteLtConst tested bound =>
      simp only [byteInterval]
      split
      · rename_i same
        subst tested
        exact byteCut_contains valid
      · exact allBytes_contains _
    case byteLeConst tested bound =>
      simp only [byteInterval]
      split
      · rename_i same
        subst tested
        apply byteCut_contains
        change decide ((env.get target).toNat ≤ bound.toNat) = result at valid
        simpa only [Nat.lt_succ_iff] using valid
      · exact allBytes_contains _

private def BranchFacts.byteBounds (facts : BranchFacts ctx) : Term ctx .byte → Interval
  | .byte byte => oneByte byte
  | .var v => facts.foldr (fun fact remaining => (fact.byteInterval v).intersect remaining) allBytes
  | _ => allBytes

private theorem BranchFacts.byteBounds_sound {facts : BranchFacts ctx} {env : Env ctx}
    (valid : facts.Valid env) (operand : Term ctx .byte) :
    (facts.byteBounds operand).Contains (operand.eval env : UInt8).toNat := by
  cases operand <;> try exact allBytes_contains _
  case byte => exact oneByte_contains _
  case var v =>
    induction facts with
    | nil => exact allBytes_contains _
    | cons head rest ih =>
      exact (Interval.intersect_contains ..).mpr
        ⟨BranchFact.byteInterval_sound (valid head List.mem_cons_self) v,
          ih (fun fact member => valid fact (.tail _ member))⟩

/-- Enumerate only the interval still allowed by the captured byte facts. -/
def BranchFacts.byteCandidates (facts : BranchFacts ctx) (operand : Term ctx .byte) : List (Fin 256) :=
  let bounds := facts.byteBounds operand
  (List.range' bounds.lo (bounds.hi - bounds.lo)).filterMap fun value =>
    if fits : value < 256 then some ⟨value, fits⟩ else none

theorem BranchFacts.byteCandidates_contains {facts : BranchFacts ctx} {env : Env ctx}
    (valid : facts.Valid env) (operand : Term ctx .byte) :
    (operand.eval env : UInt8).toFin ∈ facts.byteCandidates operand := by
  let value : UInt8 := operand.eval env
  have ⟨low, high⟩ := BranchFacts.byteBounds_sound valid operand
  change (facts.byteBounds operand).lo ≤ value.toNat at low
  change value.toNat < (facts.byteBounds operand).hi at high
  apply List.mem_filterMap.mpr
  refine ⟨value.toNat, List.mem_range'_1.mpr ⟨low, ?_⟩, ?_⟩
  · omega
  · change (if fits : value.toNat < 256 then some (⟨value.toNat, fits⟩ : Fin 256) else none) = some value.toFin
    rw [dite_eq_left value.toNat_lt]
    rfl

end Aethel.Structured
