import Aethel.CoreAST
import Aethel.CoreSemantics

namespace Aethel.CoreSoundness

open Functional Core Structured CoreAST CoreSemantics

/-- Inductive characterization of the sequential core expression fragment. -/
inductive IsSequentialCore : CoreExpr → Prop where
  | unit : IsSequentialCore .unit
  | bool (b : Bool) : IsSequentialCore (.bool b)
  | nat (n : Nat) : IsSequentialCore (.nat n)
  | int (s : Bool) (bits : Nat) (v : Int) : IsSequentialCore (.int s bits v)
  | pair {a b} : IsSequentialCore a → IsSequentialCore b → IsSequentialCore (.pair a b)
  | fst {p} : IsSequentialCore p → IsSequentialCore (.fst p)
  | snd {p} : IsSequentialCore p → IsSequentialCore (.snd p)
  | adt (tag : Nat) {p} : IsSequentialCore p → IsSequentialCore (.adt tag p)
  | matchTag {s} (tag : Nat) {onM onE} :
      IsSequentialCore s → IsSequentialCore onM → IsSequentialCore onE →
      IsSequentialCore (.matchTag s tag onM onE)
  | var (id : Nat) : IsSequentialCore (.var id)
  | letBind (id : Nat) {v body} :
      IsSequentialCore v → IsSequentialCore body → IsSequentialCore (.letBind id v body)
  | lam (p : Nat) (ty : CoreType) {body} (eff : Effect) :
      IsSequentialCore body → IsSequentialCore (.lam p ty body eff)
  | app {fn arg} : IsSequentialCore fn → IsSequentialCore arg → IsSequentialCore (.app fn arg)
  | loop {cond body} : IsSequentialCore cond → IsSequentialCore body → IsSequentialCore (.loop cond body)

/-- Progress: a well-typed closed sequential core expression is either a value
or can take an operational step in any machine state. -/
theorem progress (e : CoreExpr) (hSeq : IsSequentialCore e) (ty : CoreType) (eff : Effect)
    (hTyped : WellTyped [] e ty eff) (s : State) :
    Value e ∨ ∃ s' e', Step s e s' e' := by
  induction hSeq generalizing ty eff with
  | unit => exact Or.inl Value.unit
  | bool b => exact Or.inl (Value.bool b)
  | nat n => exact Or.inl (Value.nat n)
  | int s bits v => exact Or.inl (Value.int s bits v)
  | pair ha hb iha ihb =>
    cases hTyped with
    | pair hA hB =>
      rcases iha _ _ hA with hValA | ⟨s', a', hStepA⟩
      · rcases ihb _ _ hB with hValB | ⟨s', b', hStepB⟩
        · exact Or.inl (Value.pair hValA hValB)
        · exact Or.inr ⟨s', .pair _ b', Step.pair_right hValA hStepB⟩
      · exact Or.inr ⟨s', .pair a' _, Step.pair_left hStepA⟩
  | fst hp ih =>
    cases hTyped with
    | fst hP =>
      rcases ih _ _ hP with hValP | ⟨s', p', hStepP⟩
      · obtain ⟨a, b, rfl, hValA, hValB⟩ := canonical_prod hValP hP
        exact Or.inr ⟨s, a, Step.fst_val hValA hValB⟩
      · exact Or.inr ⟨s', .fst p', Step.fst_eval hStepP⟩
  | snd hp ih =>
    cases hTyped with
    | snd hP =>
      rcases ih _ _ hP with hValP | ⟨s', p', hStepP⟩
      · obtain ⟨a, b, rfl, hValA, hValB⟩ := canonical_prod hValP hP
        exact Or.inr ⟨s, b, Step.snd_val hValA hValB⟩
      · exact Or.inr ⟨s', .snd p', Step.snd_eval hStepP⟩
  | adt tag hp ih =>
    cases hTyped with
    | adt _ hP =>
      rcases ih _ _ hP with hValP | ⟨s', p', hStepP⟩
      · exact Or.inl (Value.adt tag hValP)
      · exact Or.inr ⟨s', .adt tag p', Step.adt_eval tag hStepP⟩
  | matchTag tag hs hm he ihs _ _ =>
    cases hTyped with
    | matchTag _ hS _ _ =>
      rcases ihs _ _ hS with hValS | ⟨s', sc', hStepS⟩
      · obtain ⟨p, rfl, hValP⟩ := canonical_adt hValS hS
        exact Or.inr ⟨s, _, Step.match_hit tag hValP⟩
      · exact Or.inr ⟨s', .matchTag sc' tag _ _, Step.match_eval tag hStepS⟩
    | matchBool hS _ _ =>
      rcases ihs _ _ hS with hValS | ⟨s', sc', hStepS⟩
      · obtain ⟨b, rfl⟩ := canonical_bool hValS hS
        cases b with
        | true => exact Or.inr ⟨s, _, Step.match_bool_true⟩
        | false => exact Or.inr ⟨s, _, Step.match_bool_false⟩
      · exact Or.inr ⟨s', .matchTag sc' 1 _ _, Step.match_eval 1 hStepS⟩
  | var id =>
    cases hTyped with
    | var _ hLookup =>
      contradiction
  | letBind id hv hb ihv _ =>
    cases hTyped with
    | letBind _ hV hB =>
      rcases ihv _ _ hV with hValV | ⟨s', v', hStepV⟩
      · exact Or.inr ⟨s, subst id _ _, Step.let_subst id hValV⟩
      · exact Or.inr ⟨s', .letBind id v' _, Step.let_eval id hStepV⟩
  | lam p paramTy effBody _ =>
    exact Or.inl (Value.lam p paramTy _ effBody)
  | app hfn harg ihfn iharg =>
    cases hTyped with
    | app hFn hArg =>
      rcases ihfn _ _ hFn with hValFn | ⟨s', fn', hStepFn⟩
      · obtain ⟨p, ty, body, rfl⟩ := canonical_arrow hValFn hFn
        rcases iharg _ _ hArg with hValArg | ⟨s', arg', hStepArg⟩
        · exact Or.inr ⟨s, subst p _ body, Step.app_beta p ty body _ hValArg⟩
        · exact Or.inr ⟨s', .app _ arg', Step.app_arg hValFn hStepArg⟩
      · exact Or.inr ⟨s', .app fn' _, Step.app_fn hStepFn⟩
  | loop hc hb _ _ =>
    cases hTyped with
    | loop hC hB =>
      exact Or.inr ⟨s, _, Step.loop_step⟩

/-- Every value has empty effect footprint. -/
theorem value_effect_empty {v : CoreExpr} (hVal : Value v) {ty : CoreType} {eff : Effect}
    (hTyped : WellTyped [] v ty eff) : eff = .empty := by
  induction hVal generalizing ty eff with
  | unit => cases hTyped; rfl
  | bool b => cases hTyped; rfl
  | nat n => cases hTyped; rfl
  | int s bits val => cases hTyped; rfl
  | lam p t b eb => cases hTyped; rfl
  | pair ha hb iha ihb =>
    cases hTyped with
    | pair hA hB =>
      have ea := iha hA
      have eb := ihb hB
      subst ea eb
      exact Effect.union_empty_left .empty
  | adt tag hp ih =>
    cases hTyped with
    | adt _ hP =>
      exact ih hP

theorem lookup_head (x : Nat) (tyX : CoreType) (ctx : Ctx) :
    Ctx.lookup ((x, tyX) :: ctx) x = some tyX := by
  simp [Ctx.lookup]

theorem lookup_tail {x y : Nat} (hne : y ≠ x) (tyX : CoreType) (ctx : Ctx) :
    Ctx.lookup ((x, tyX) :: ctx) y = Ctx.lookup ctx y := by
  dsimp [Ctx.lookup]
  have h : (x == y) = false := by simp [beq_eq_false_iff_ne, Ne.symm hne]
  simp [h]

theorem lookup_exchange {x y : Nat} (hne : x ≠ y) (tyX tyY : CoreType) (ctx : Ctx) (k : Nat) :
    Ctx.lookup ((x, tyX) :: (y, tyY) :: ctx) k = Ctx.lookup ((y, tyY) :: (x, tyX) :: ctx) k := by
  dsimp [Ctx.lookup]
  by_cases hx : x == k <;> by_cases hy : y == k
  · have hx_eq : x = k := beq_iff_eq.mp hx
    have hy_eq : y = k := beq_iff_eq.mp hy
    subst hx_eq hy_eq
    contradiction
  · simp [hx, hy]
  · simp [hx, hy]
  · simp [hx, hy]

theorem lookup_shadow (x : Nat) (ty1 ty2 : CoreType) (ctx : Ctx) (k : Nat) :
    Ctx.lookup ((x, ty1) :: (x, ty2) :: ctx) k = Ctx.lookup ((x, ty1) :: ctx) k := by
  dsimp [Ctx.lookup]
  by_cases hx : x == k
  · simp [hx]
  · simp [hx]

def CtxSub (ctx1 ctx2 : Ctx) : Prop :=
  ∀ id ty, ctx1.lookup id = some ty → ctx2.lookup id = some ty

theorem ctxSub_empty (ctx : Ctx) : CtxSub [] ctx := by
  intro id ty h
  contradiction

theorem ctxSub_cons {ctx1 ctx2 : Ctx} (hsub : CtxSub ctx1 ctx2) (x : Nat) (tyX : CoreType) :
    CtxSub ((x, tyX) :: ctx1) ((x, tyX) :: ctx2) := by
  intro id ty h
  by_cases heq : id = x
  · subst heq
    rw [lookup_head] at h ⊢
    exact h
  · rw [lookup_tail heq] at h ⊢
    exact hsub id ty h

/-- Context weakening preserves typing. -/
theorem wellTyped_weaken {ctx1 ctx2 : Ctx} {e : CoreExpr} {ty : CoreType} {eff : Effect}
    (hTyped : WellTyped ctx1 e ty eff) (hsub : CtxSub ctx1 ctx2) :
    WellTyped ctx2 e ty eff := by
  induction hTyped generalizing ctx2 with
  | unit => exact .unit ctx2
  | bool _ b => exact .bool ctx2 b
  | nat _ n => exact .nat ctx2 n
  | int _ s bits v => exact .int ctx2 s bits v
  | pair ha hb iha ihb =>
    exact .pair (iha hsub) (ihb hsub)
  | fst hp ih =>
    exact .fst (ih hsub)
  | snd hp ih =>
    exact .snd (ih hsub)
  | adt tag hp ih =>
    exact .adt tag (ih hsub)
  | matchTag tag hs hm he ihs ihm ihe =>
    exact .matchTag tag (ihs hsub) (ihm hsub) (ihe hsub)
  | matchBool hs ht hf ihs iht ihf =>
    exact .matchBool (ihs hsub) (iht hsub) (ihf hsub)
  | var id h =>
    exact .var id (hsub id _ h)
  | letBind id hv hb ihv ihb =>
    exact .letBind id (ihv hsub) (ihb (ctxSub_cons hsub id _))
  | alloc _ sz init =>
    exact .alloc ctx2 sz init
  | readHandle _ h off =>
    exact .readHandle ctx2 h off
  | writeHandle h off hv ihv =>
    exact .writeHandle h off (ihv hsub)
  | borrowView vId h mode off hb ihb =>
    exact .borrowView vId h mode off (ihb (ctxSub_cons hsub vId _))
  | readView _ vId =>
    exact .readView ctx2 vId
  | writeView vId hv ihv =>
    exact .writeView vId (ihv hsub)
  | lam p tyP effBody hb ihb =>
    exact .lam p tyP effBody (ihb (ctxSub_cons hsub p _))
  | app hfn harg ihfn iharg =>
    exact .app (ihfn hsub) (iharg hsub)
  | loop hc hb ihc ihb =>
    exact .loop (ihc hsub) (ihb hsub)

theorem wellTyped_closed_weaken {e : CoreExpr} {ty : CoreType} {eff : Effect}
    (hTyped : WellTyped [] e ty eff) (ctx : Ctx) :
    WellTyped ctx e ty eff :=
  wellTyped_weaken hTyped (ctxSub_empty ctx)

theorem ctxSub_exchange {x y : Nat} (hne : x ≠ y) (tyX tyY : CoreType) (ctx : Ctx) :
    CtxSub ((x, tyX) :: (y, tyY) :: ctx) ((y, tyY) :: (x, tyX) :: ctx) := by
  intro id ty h
  rw [lookup_exchange (Ne.symm hne)]
  exact h

theorem wellTyped_exchange {x y : Nat} (hne : x ≠ y) {tyX tyY ty : CoreType} {eff : Effect}
    {e : CoreExpr} {ctx : Ctx}
    (h : WellTyped ((x, tyX) :: (y, tyY) :: ctx) e ty eff) :
    WellTyped ((y, tyY) :: (x, tyX) :: ctx) e ty eff :=
  wellTyped_weaken h (ctxSub_exchange hne tyX tyY ctx)

theorem ctxSub_shadow (x : Nat) (ty1 ty2 : CoreType) (ctx : Ctx) :
    CtxSub ((x, ty1) :: (x, ty2) :: ctx) ((x, ty1) :: ctx) := by
  intro id ty h
  rw [lookup_shadow] at h
  exact h

theorem wellTyped_shadow {x : Nat} {ty1 ty2 ty : CoreType} {eff : Effect}
    {e : CoreExpr} {ctx : Ctx}
    (h : WellTyped ((x, ty1) :: (x, ty2) :: ctx) e ty eff) :
    WellTyped ((x, ty1) :: ctx) e ty eff :=
  wellTyped_weaken h (ctxSub_shadow x ty1 ty2 ctx)

/-- Substitution theorem for closed values. -/
theorem substitution_value {val : CoreExpr} {tyV : CoreType}
    (_hVal : Value val) (hValTyped : WellTyped [] val tyV .empty) (body : CoreExpr) :
    ∀ {ctx : Ctx} {varId : Nat} {tyBody : CoreType} {effBody : Effect},
      WellTyped ((varId, tyV) :: ctx) body tyBody effBody →
      WellTyped ctx (subst varId val body) tyBody effBody := by
  induction body with
  | unit =>
    intro ctx varId tyBody effBody hBody
    cases hBody
    exact .unit ctx
  | bool b =>
    intro ctx varId tyBody effBody hBody
    cases hBody
    exact .bool ctx b
  | nat n =>
    intro ctx varId tyBody effBody hBody
    cases hBody
    exact .nat ctx n
  | int s bits v =>
    intro ctx varId tyBody effBody hBody
    cases hBody
    exact .int ctx s bits v
  | pair a b iha ihb =>
    intro ctx varId tyBody effBody hBody
    cases hBody with
    | pair ha hb =>
      exact .pair (iha ha) (ihb hb)
  | fst p ih =>
    intro ctx varId tyBody effBody hBody
    cases hBody with
    | fst hp =>
      exact .fst (ih hp)
  | snd p ih =>
    intro ctx varId tyBody effBody hBody
    cases hBody with
    | snd hp =>
      exact .snd (ih hp)
  | adt tag p ih =>
    intro ctx varId tyBody effBody hBody
    cases hBody with
    | adt _ hp =>
      exact .adt tag (ih hp)
  | matchTag s tag onM onE ihs ihm ihe =>
    intro ctx varId tyBody effBody hBody
    cases hBody with
    | matchTag _ hs hm he =>
      exact .matchTag tag (ihs hs) (ihm hm) (ihe he)
    | matchBool hs ht hf =>
      exact .matchBool (ihs hs) (ihm ht) (ihe hf)
  | var id =>
    intro ctx varId tyBody effBody hBody
    cases hBody with
    | var _ h =>
      by_cases heq : id = varId
      · subst heq
        simp only [subst, ite_true]
        rw [lookup_head] at h
        have hty : tyV = tyBody := Option.some.inj h
        subst hty
        exact wellTyped_closed_weaken hValTyped ctx
      · have hne : (id = varId) = False := eq_false heq
        simp only [subst, hne, ↓reduceIte]
        rw [lookup_tail heq] at h
        exact .var id h
  | letBind id v b ihv ihb =>
    intro ctx varId tyBody effBody hBody
    cases hBody with
    | letBind _ hv hb =>
      have hv' := ihv hv
      by_cases heq : id = varId
      · subst heq
        simp only [subst, ite_true]
        have hb_shadowed := wellTyped_shadow hb
        exact .letBind id hv' hb_shadowed
      · have hne : (id = varId) = False := eq_false heq
        simp only [subst, hne, ↓reduceIte]
        have hb_exchanged := wellTyped_exchange heq hb
        have hb' := ihb hb_exchanged
        exact .letBind id hv' hb'
  | alloc sz init =>
    intro ctx varId tyBody effBody hBody
    cases hBody
    exact .alloc ctx sz init
  | readHandle h off =>
    intro ctx varId tyBody effBody hBody
    cases hBody
    exact .readHandle ctx h off
  | writeHandle h off v ihv =>
    intro ctx varId tyBody effBody hBody
    cases hBody with
    | writeHandle _ _ hv =>
      exact .writeHandle h off (ihv hv)
  | borrowView vId h mode off b ihb =>
    intro ctx varId tyBody effBody hBody
    cases hBody with
    | borrowView _ _ _ _ hb =>
      by_cases heq : vId = varId
      · subst heq
        simp only [subst, ite_true]
        have hb_shadowed := wellTyped_shadow hb
        exact .borrowView vId h mode off hb_shadowed
      · have hne : (vId = varId) = False := eq_false heq
        simp only [subst, hne, ↓reduceIte]
        have hb_exchanged := wellTyped_exchange heq hb
        have hb' := ihb hb_exchanged
        exact .borrowView vId h mode off hb'
  | readView vId =>
    intro ctx varId tyBody effBody hBody
    cases hBody
    exact .readView ctx vId
  | writeView vId v ihv =>
    intro ctx varId tyBody effBody hBody
    cases hBody with
    | writeView _ hv =>
      exact .writeView vId (ihv hv)
  | lam p tyP b effBody ihb =>
    intro ctx varId tyBody effBody' hBody
    cases hBody with
    | lam _ _ _ hb =>
      by_cases heq : p = varId
      · subst heq
        simp only [subst, ite_true]
        have hb_shadowed := wellTyped_shadow hb
        exact .lam p tyP effBody hb_shadowed
      · have hne : (p = varId) = False := eq_false heq
        simp only [subst, hne, ↓reduceIte]
        have hb_exchanged := wellTyped_exchange heq hb
        have hb' := ihb hb_exchanged
        exact .lam p tyP effBody hb'
  | app fn arg ihfn iharg =>
    intro ctx varId tyBody effBody hBody
    cases hBody with
    | app hfn harg =>
      exact .app (ihfn hfn) (iharg harg)
  | loop c b ihc ihb =>
    intro ctx varId tyBody effBody hBody
    cases hBody with
    | loop hc hb =>
      exact .loop (ihc hc) (ihb hb)
  | abort reason =>
    intro ctx varId tyBody effBody hBody
    cases hBody

/-- Single-variable substitution for closed values in step reductions. -/
theorem substitution_step {val : CoreExpr} {tyV : CoreType} {effV : Effect}
    (hVal : Value val) (hValTyped : WellTyped [] val tyV effV) (body : CoreExpr)
    {ctx : Ctx} {varId : Nat} {tyBody : CoreType} {effBody : Effect}
    (hBody : WellTyped ((varId, tyV) :: ctx) body tyBody effBody) :
    WellTyped ctx (subst varId val body) tyBody effBody := by
  have heff := value_effect_empty hVal hValTyped
  subst heff
  exact substitution_value hVal hValTyped body hBody

/-- Preservation (Subject Reduction): evaluation steps preserve well-typedness. -/
theorem preservation {s s' : State} {e e' : CoreExpr} {ty : CoreType} {eff : Effect}
    (hStep : Step s e s' e') (hTyped : WellTyped [] e ty eff) :
    ∃ eff', WellTyped [] e' ty eff' := by
  induction hStep generalizing ty eff with
  | pair_left h ih =>
    cases hTyped with
    | pair ha hb =>
      obtain ⟨effA', ha'⟩ := ih ha
      exact ⟨effA'.union _, .pair ha' hb⟩
  | pair_right _ h ih =>
    cases hTyped with
    | pair ha hb =>
      obtain ⟨effB', hb'⟩ := ih hb
      exact ⟨_, .pair ha hb'⟩
  | fst_eval h ih =>
    cases hTyped with
    | fst hp =>
      obtain ⟨effP', hp'⟩ := ih hp
      exact ⟨effP', .fst hp'⟩
  | fst_val _ _ =>
    cases hTyped with
    | fst hp =>
      cases hp with
      | pair ha _ =>
        exact ⟨_, ha⟩
  | snd_eval h ih =>
    cases hTyped with
    | snd hp =>
      obtain ⟨effP', hp'⟩ := ih hp
      exact ⟨effP', .snd hp'⟩
  | snd_val _ _ =>
    cases hTyped with
    | snd hp =>
      cases hp with
      | pair _ hb =>
        exact ⟨_, hb⟩
  | adt_eval tag h ih =>
    cases hTyped with
    | adt _ hp =>
      obtain ⟨effP', hp'⟩ := ih hp
      exact ⟨effP', .adt tag hp'⟩
  | match_eval tag h ih =>
    cases hTyped with
    | matchTag _ hs hm he =>
      obtain ⟨effS', hs'⟩ := ih hs
      exact ⟨effS'.union _, .matchTag tag hs' hm he⟩
    | matchBool hs ht hf =>
      obtain ⟨effS', hs'⟩ := ih hs
      exact ⟨effS'.union _, .matchBool hs' ht hf⟩
  | match_hit tag hp =>
    cases hTyped with
    | matchTag _ hs hm he =>
      exact ⟨_, hm⟩
    | matchBool hs _ _ =>
      cases hs
  | match_miss tag1 tag2 hne hp =>
    cases hTyped with
    | matchTag _ hs hm he =>
      exact ⟨_, he⟩
    | matchBool hs _ _ =>
      cases hs
  | match_bool_true =>
    cases hTyped with
    | matchBool _ ht _ =>
      exact ⟨_, ht⟩
    | matchTag _ hs _ _ =>
      cases hs
  | match_bool_false =>
    cases hTyped with
    | matchBool _ _ hf =>
      exact ⟨_, hf⟩
    | matchTag _ hs _ _ =>
      cases hs
  | let_eval id h ih =>
    cases hTyped with
    | letBind _ hv hb =>
      obtain ⟨effV', hv'⟩ := ih hv
      exact ⟨effV'.union _, .letBind id hv' hb⟩
  | let_subst id hv =>
    cases hTyped with
    | letBind _ hvTyped hb =>
      exact ⟨_, substitution_step hv hvTyped _ hb⟩
  | app_fn h ih =>
    cases hTyped with
    | app hfn harg =>
      obtain ⟨effFn', hfn'⟩ := ih hfn
      exact ⟨effFn'.union _, .app hfn' harg⟩
  | app_arg _ h ih =>
    cases hTyped with
    | app hfn harg =>
      obtain ⟨effArg', harg'⟩ := ih harg
      exact ⟨_, .app hfn harg'⟩
  | app_beta p tyP body effBody hv =>
    cases hTyped with
    | app hfn harg =>
      cases hfn with
      | lam _ _ _ hb =>
        exact ⟨_, substitution_step hv harg _ hb⟩
  | loop_step =>
    cases hTyped with
    | loop hc hb =>
      have hLoopRec : WellTyped [(0, .unit)] (.loop _ _) .unit _ :=
        wellTyped_closed_weaken (.loop hc hb) [(0, .unit)]
      have hLet : WellTyped [] (.letBind 0 _ (.loop _ _)) .unit _ :=
        .letBind 0 hb hLoopRec
      have hUnit : WellTyped [] .unit .unit .empty := .unit []
      have hMatch := WellTyped.matchBool hc hLet hUnit
      exact ⟨_, hMatch⟩

-- Proof Erasure

inductive ErasedExpr where
  | unit : ErasedExpr
  | bool (b : Bool) : ErasedExpr
  | nat (n : Nat) : ErasedExpr
  | int (signed : Bool) (bits : Nat) (val : Int) : ErasedExpr
  | pair (fst snd : ErasedExpr) : ErasedExpr
  | fst (p : ErasedExpr) : ErasedExpr
  | snd (p : ErasedExpr) : ErasedExpr
  | adt (tag : Nat) (payload : ErasedExpr) : ErasedExpr
  | matchTag (scrutinee : ErasedExpr) (tag : Nat) (onMatch onElse : ErasedExpr) : ErasedExpr
  | var (id : Nat) : ErasedExpr
  | letBind (id : Nat) (val body : ErasedExpr) : ErasedExpr
  | lam (param : Nat) (body : ErasedExpr) : ErasedExpr
  | app (fn arg : ErasedExpr) : ErasedExpr
  | loop (cond body : ErasedExpr) : ErasedExpr
  deriving Repr, DecidableEq

/-- Erasure of access certificates, type annotations, and effect footprints. -/
def erase : CoreExpr → ErasedExpr
  | .unit => .unit
  | .bool b => .bool b
  | .nat n => .nat n
  | .int s bits v => .int s bits v
  | .pair a b => .pair (erase a) (erase b)
  | .fst p => .fst (erase p)
  | .snd p => .snd (erase p)
  | .adt tag p => .adt tag (erase p)
  | .matchTag s tag onM onE => .matchTag (erase s) tag (erase onM) (erase onE)
  | .var id => .var id
  | .letBind id v body => .letBind id (erase v) (erase body)
  | .lam p _ body _ => .lam p (erase body)
  | .app fn arg => .app (erase fn) (erase arg)
  | .loop c b => .loop (erase c) (erase b)
  | _ => .unit

def erasedSubst (varId : Nat) (val : ErasedExpr) : ErasedExpr → ErasedExpr
  | .unit => .unit
  | .bool b => .bool b
  | .nat n => .nat n
  | .int s bits v => .int s bits v
  | .pair a b => .pair (erasedSubst varId val a) (erasedSubst varId val b)
  | .fst p => .fst (erasedSubst varId val p)
  | .snd p => .snd (erasedSubst varId val p)
  | .adt tag p => .adt tag (erasedSubst varId val p)
  | .matchTag s tag onMatch onElse =>
    .matchTag (erasedSubst varId val s) tag (erasedSubst varId val onMatch) (erasedSubst varId val onElse)
  | .var id => if id = varId then val else .var id
  | .letBind id v body =>
    let v' := erasedSubst varId val v
    let body' := if id = varId then body else erasedSubst varId val body
    .letBind id v' body'
  | .lam p body =>
    let body' := if p = varId then body else erasedSubst varId val body
    .lam p body'
  | .app fn arg => .app (erasedSubst varId val fn) (erasedSubst varId val arg)
  | .loop c b => .loop (erasedSubst varId val c) (erasedSubst varId val b)

theorem erase_subst (varId : Nat) (val : CoreExpr) (body : CoreExpr) :
    erase (subst varId val body) = erasedSubst varId (erase val) (erase body) := by
  induction body with
  | unit => rfl
  | bool b => rfl
  | nat n => rfl
  | int s bits v => rfl
  | pair a b iha ihb =>
    simp only [subst, erase, iha, ihb, erasedSubst]
  | fst p ih =>
    simp only [subst, erase, ih, erasedSubst]
  | snd p ih =>
    simp only [subst, erase, ih, erasedSubst]
  | adt tag p ih =>
    simp only [subst, erase, ih, erasedSubst]
  | matchTag s tag onM onE ihs ihm ihe =>
    simp only [subst, erase, ihs, ihm, ihe, erasedSubst]
  | var id =>
    simp only [subst, erase]
    dsimp [erasedSubst]
    split <;> rfl
  | letBind id v b ihv ihb =>
    simp only [subst, erase, ihv, erasedSubst]
    split <;> simp [ihb]
  | lam p ty b eff ihb =>
    simp only [subst, erase, erasedSubst]
    split <;> simp [ihb]
  | app fn arg ihfn iharg =>
    simp only [subst, erase, ihfn, iharg, erasedSubst]
  | loop c b ihc ihb =>
    simp only [subst, erase, ihc, ihb, erasedSubst]
  | _ => rfl

inductive ErasedValue : ErasedExpr → Prop where
  | unit : ErasedValue .unit
  | bool (b : Bool) : ErasedValue (.bool b)
  | nat (n : Nat) : ErasedValue (.nat n)
  | int (s : Bool) (bits : Nat) (v : Int) : ErasedValue (.int s bits v)
  | lam (p : Nat) (body : ErasedExpr) : ErasedValue (.lam p body)
  | pair {a b : ErasedExpr} : ErasedValue a → ErasedValue b → ErasedValue (.pair a b)
  | adt (tag : Nat) {p : ErasedExpr} : ErasedValue p → ErasedValue (.adt tag p)

theorem value_erase {e : CoreExpr} (h : Value e) : ErasedValue (erase e) := by
  induction h with
  | unit => exact .unit
  | bool b => exact .bool b
  | nat n => exact .nat n
  | int s bits v => exact .int s bits v
  | lam p ty body eff => exact .lam p (erase body)
  | pair ha hb iha ihb => exact .pair iha ihb
  | adt tag hp ih => exact .adt tag ih

inductive ErasedStep : State → ErasedExpr → State → ErasedExpr → Prop where
  | pair_left {s s' : State} {a a' b : ErasedExpr} :
      ErasedStep s a s' a' →
      ErasedStep s (.pair a b) s' (.pair a' b)
  | pair_right {s s' : State} {a b b' : ErasedExpr} :
      ErasedValue a → ErasedStep s b s' b' →
      ErasedStep s (.pair a b) s' (.pair a b')
  | fst_eval {s s' : State} {p p' : ErasedExpr} :
      ErasedStep s p s' p' →
      ErasedStep s (.fst p) s' (.fst p')
  | fst_val {s : State} {a b : ErasedExpr} :
      ErasedValue a → ErasedValue b →
      ErasedStep s (.fst (.pair a b)) s a
  | snd_eval {s s' : State} {p p' : ErasedExpr} :
      ErasedStep s p s' p' →
      ErasedStep s (.snd p) s' (.snd p')
  | snd_val {s : State} {a b : ErasedExpr} :
      ErasedValue a → ErasedValue b →
      ErasedStep s (.snd (.pair a b)) s b
  | adt_eval {s s' : State} (tag : Nat) {p p' : ErasedExpr} :
      ErasedStep s p s' p' →
      ErasedStep s (.adt tag p) s' (.adt tag p')
  | match_eval {s s' : State} {sc sc' : ErasedExpr} (tag : Nat) {onM onE : ErasedExpr} :
      ErasedStep s sc s' sc' →
      ErasedStep s (.matchTag sc tag onM onE) s' (.matchTag sc' tag onM onE)
  | match_hit {s : State} (tag : Nat) {p : ErasedExpr} {onM onE : ErasedExpr} :
      ErasedValue p →
      ErasedStep s (.matchTag (.adt tag p) tag onM onE) s onM
  | match_miss {s : State} (tag1 tag2 : Nat) {p : ErasedExpr} {onM onE : ErasedExpr} :
      tag1 ≠ tag2 → ErasedValue p →
      ErasedStep s (.matchTag (.adt tag1 p) tag2 onM onE) s onE
  | match_bool_true {s : State} {onM onE : ErasedExpr} :
      ErasedStep s (.matchTag (.bool true) 1 onM onE) s onM
  | match_bool_false {s : State} {onM onE : ErasedExpr} :
      ErasedStep s (.matchTag (.bool false) 1 onM onE) s onE
  | let_eval {s s' : State} (id : Nat) {v v' body : ErasedExpr} :
      ErasedStep s v s' v' →
      ErasedStep s (.letBind id v body) s' (.letBind id v' body)
  | let_subst {s : State} (id : Nat) {v body : ErasedExpr} :
      ErasedValue v →
      ErasedStep s (.letBind id v body) s (erasedSubst id v body)
  | app_fn {s s' : State} {fn fn' arg : ErasedExpr} :
      ErasedStep s fn s' fn' →
      ErasedStep s (.app fn arg) s' (.app fn' arg)
  | app_arg {s s' : State} {fn arg arg' : ErasedExpr} :
      ErasedValue fn → ErasedStep s arg s' arg' →
      ErasedStep s (.app fn arg) s' (.app fn arg')
  | app_beta {s : State} (p : Nat) (body : ErasedExpr) {v : ErasedExpr} :
      ErasedValue v →
      ErasedStep s (.app (.lam p body) v) s (erasedSubst p v body)
  | loop_step {s : State} {cond body : ErasedExpr} :
      ErasedStep s (.loop cond body) s
        (.matchTag cond 1 (.letBind 0 body (.loop cond body)) .unit)

/-- Proof erasure simulation: typed steps project onto identical erased steps. -/
theorem proof_erasure_simulation {s s' : State} {e e' : CoreExpr}
    (hStep : Step s e s' e') :
    ErasedStep s (erase e) s' (erase e') := by
  induction hStep with
  | pair_left h ih =>
    exact .pair_left ih
  | pair_right ha h ih =>
    exact .pair_right (value_erase ha) ih
  | fst_eval h ih =>
    exact .fst_eval ih
  | fst_val ha hb =>
    exact .fst_val (value_erase ha) (value_erase hb)
  | snd_eval h ih =>
    exact .snd_eval ih
  | snd_val ha hb =>
    exact .snd_val (value_erase ha) (value_erase hb)
  | adt_eval tag h ih =>
    exact .adt_eval tag ih
  | match_eval tag h ih =>
    exact .match_eval tag ih
  | match_hit tag hp =>
    exact .match_hit tag (value_erase hp)
  | match_miss tag1 tag2 hne hp =>
    exact .match_miss tag1 tag2 hne (value_erase hp)
  | match_bool_true =>
    exact .match_bool_true
  | match_bool_false =>
    exact .match_bool_false
  | let_eval id h ih =>
    exact .let_eval id ih
  | let_subst id hv =>
    dsimp [erase]
    rw [erase_subst]
    exact .let_subst id (value_erase hv)
  | app_fn h ih =>
    exact .app_fn ih
  | app_arg hfn h ih =>
    exact .app_arg (value_erase hfn) ih
  | app_beta p ty body eff hv =>
    dsimp [erase]
    rw [erase_subst]
    exact .app_beta p (erase body) (value_erase hv)
  | loop_step =>
    dsimp [erase]
    exact .loop_step

/-- Proof erasure independence: runtime execution is completely independent of
access certificates and type/effect annotations. -/
theorem proof_erasure_same_step (e1 e2 : CoreExpr)
    (heq : erase e1 = erase e2)
    {s s1' : State} {e1' : CoreExpr}
    (h1 : Step s e1 s1' e1') :
    ErasedStep s (erase e2) s1' (erase e1') := by
  rw [← heq]
  exact proof_erasure_simulation h1

end Aethel.CoreSoundness
