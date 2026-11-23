import Aethel.CoreAST
import Aethel.CoreSemantics
import Aethel.CoreSoundnessFull
import Aethel.Representation
import Aethel.ResourceLiveness

namespace Aethel.StatefulCore

open Functional Core Structured CoreAST Representation

/-- Unified types for the stateful core calculus connecting functional abstractions
with byte-heap handles and scoped views. -/
inductive SType where
  | unit : SType
  | bool : SType
  | byte : SType
  | prod (a b : SType) : SType
  | handle : SType
  | view (mode : AccessMode) : SType
  | arrow (dom cod : SType) : SType
  deriving DecidableEq, Repr

/-- Unified expressions integrating pure call-by-value lambda calculus with
live byte-machine allocations, handles, and scoped views. -/
inductive SExpr where
  | unit : SExpr
  | bool (b : Bool) : SExpr
  | byte (v : UInt8) : SExpr
  | pair (a b : SExpr) : SExpr
  | fst (p : SExpr) : SExpr
  | snd (p : SExpr) : SExpr
  | var (id : Nat) : SExpr
  | letBind (id : Nat) (v body : SExpr) : SExpr
  | lam (p : Nat) (ty : SType) (body : SExpr) : SExpr
  | app (fn arg : SExpr) : SExpr
  | handleVal (id : HandleId) : SExpr
  | viewVal (id : ViewId) : SExpr
  | alloc (owner : OwnerId) (hId : HandleId) (size : Nat) (init : UInt8) : SExpr
  | readHandle (h : HandleId) : SExpr
  | writeHandle (h : HandleId) (v : SExpr) : SExpr
  | withView (vId : ViewId) (h : HandleId) (mode : AccessMode) (body : SExpr) : SExpr
  | activeView (vId : ViewId) (body : SExpr) : SExpr
  | readView (vId : ViewId) : SExpr
  | writeView (vId : ViewId) (v : SExpr) : SExpr
  | destroy (owner : OwnerId) : SExpr
  deriving Repr, DecidableEq

inductive SValue : SExpr → Prop where
  | unit : SValue .unit
  | bool (b : Bool) : SValue (.bool b)
  | byte (v : UInt8) : SValue (.byte v)
  | handleVal (id : HandleId) : SValue (.handleVal id)
  | viewVal (id : ViewId) : SValue (.viewVal id)
  | lam (p : Nat) (ty : SType) (body : SExpr) : SValue (.lam p ty body)
  | pair {a b : SExpr} : SValue a → SValue b → SValue (.pair a b)

def ssubst (varId : Nat) (val : SExpr) : SExpr → SExpr
  | .unit => .unit
  | .bool b => .bool b
  | .byte v => .byte v
  | .pair a b => .pair (ssubst varId val a) (ssubst varId val b)
  | .fst p => .fst (ssubst varId val p)
  | .snd p => .snd (ssubst varId val p)
  | .var id => if id = varId then val else .var id
  | .letBind id v body =>
    let v' := ssubst varId val v
    let body' := if id = varId then body else ssubst varId val body
    .letBind id v' body'
  | .lam p ty body =>
    let body' := if p = varId then body else ssubst varId val body
    .lam p ty body'
  | .app fn arg => .app (ssubst varId val fn) (ssubst varId val arg)
  | .handleVal id => .handleVal id
  | .viewVal id => .viewVal id
  | .alloc owner hId sz init => .alloc owner hId sz init
  | .readHandle h => .readHandle h
  | .writeHandle h v => .writeHandle h (ssubst varId val v)
  | .withView vId h mode body => .withView vId h mode (ssubst varId val body)
  | .activeView vId body => .activeView vId (ssubst varId val body)
  | .readView vId => .readView vId
  | .writeView vId v => .writeView vId (ssubst varId val v)
  | .destroy owner => .destroy owner

abbrev SCtx := List (Nat × SType)

def SCtx.lookup (ctx : SCtx) (id : Nat) : Option SType :=
  match ctx.find? fun (k, _) => k == id with
  | some (_, ty) => some ty
  | none => none

inductive SWellTyped : SCtx → SExpr → SType → Prop where
  | unit (ctx : SCtx) : SWellTyped ctx .unit .unit
  | bool (ctx : SCtx) (b : Bool) : SWellTyped ctx (.bool b) .bool
  | byte (ctx : SCtx) (v : UInt8) : SWellTyped ctx (.byte v) .byte
  | handleVal (ctx : SCtx) (id : HandleId) : SWellTyped ctx (.handleVal id) .handle
  | viewVal (ctx : SCtx) (id : ViewId) (m : AccessMode) : SWellTyped ctx (.viewVal id) (.view m)
  | pair {ctx : SCtx} {a b : SExpr} {tyA tyB : SType} :
      SWellTyped ctx a tyA →
      SWellTyped ctx b tyB →
      SWellTyped ctx (.pair a b) (.prod tyA tyB)
  | fst {ctx : SCtx} {p : SExpr} {tyA tyB : SType} :
      SWellTyped ctx p (.prod tyA tyB) →
      SWellTyped ctx (.fst p) tyA
  | snd {ctx : SCtx} {p : SExpr} {tyA tyB : SType} :
      SWellTyped ctx p (.prod tyA tyB) →
      SWellTyped ctx (.snd p) tyB
  | var {ctx : SCtx} (id : Nat) {ty : SType} :
      ctx.lookup id = some ty →
      SWellTyped ctx (.var id) ty
  | letBind {ctx : SCtx} (id : Nat) {v body : SExpr} {tyV tyBody : SType} :
      SWellTyped ctx v tyV →
      SWellTyped ((id, tyV) :: ctx) body tyBody →
      SWellTyped ctx (.letBind id v body) tyBody
  | lam {ctx : SCtx} (p : Nat) (tyP : SType) {body : SExpr} {tyBody : SType} :
      SWellTyped ((p, tyP) :: ctx) body tyBody →
      SWellTyped ctx (.lam p tyP body) (.arrow tyP tyBody)
  | app {ctx : SCtx} {fn arg : SExpr} {dom cod : SType} :
      SWellTyped ctx fn (.arrow dom cod) →
      SWellTyped ctx arg dom →
      SWellTyped ctx (.app fn arg) cod
  | alloc (ctx : SCtx) (owner : OwnerId) (hId : HandleId) (size : Nat) (init : UInt8) :
      SWellTyped ctx (.alloc owner hId size init) .handle
  | readHandle (ctx : SCtx) (h : HandleId) :
      SWellTyped ctx (.readHandle h) .byte
  | writeHandle {ctx : SCtx} (h : HandleId) {v : SExpr} :
      SWellTyped ctx v .byte →
      SWellTyped ctx (.writeHandle h v) .unit
  | withView {ctx : SCtx} (vId : ViewId) (h : HandleId) (mode : AccessMode) {body : SExpr} {tyBody : SType} :
      SWellTyped ctx body tyBody →
      SWellTyped ctx (.withView vId h mode body) tyBody
  | activeView {ctx : SCtx} (vId : ViewId) {body : SExpr} {tyBody : SType} :
      SWellTyped ctx body tyBody →
      SWellTyped ctx (.activeView vId body) tyBody
  | readView (ctx : SCtx) (vId : ViewId) :
      SWellTyped ctx (.readView vId) .byte
  | writeView {ctx : SCtx} (vId : ViewId) {v : SExpr} :
      SWellTyped ctx v .byte →
      SWellTyped ctx (.writeView vId v) .unit
  | destroy (ctx : SCtx) (owner : OwnerId) :
      SWellTyped ctx (.destroy owner) .unit

def StateWellFormed (s : State) : Prop :=
  s.OwnersValid ∧ s.ReferencesLive ∧ s.ViewsCompatible

theorem stateWellFormed_empty : StateWellFormed {} :=
  ⟨State.empty_owners_valid, State.empty_references_live, State.empty_views_compatible⟩

/-- Unified stateful small-step operational semantics backed directly by `Core.Step`. -/
inductive StatefulStep : State → SExpr → State → SExpr → Prop where
  | pair_left {s s' : State} {a a' b : SExpr} :
      StatefulStep s a s' a' →
      StatefulStep s (.pair a b) s' (.pair a' b)
  | pair_right {s s' : State} {a b b' : SExpr} :
      SValue a → StatefulStep s b s' b' →
      StatefulStep s (.pair a b) s' (.pair a b')
  | fst_eval {s s' : State} {p p' : SExpr} :
      StatefulStep s p s' p' →
      StatefulStep s (.fst p) s' (.fst p')
  | fst_val {s : State} {a b : SExpr} :
      SValue a → SValue b →
      StatefulStep s (.fst (.pair a b)) s a
  | snd_eval {s s' : State} {p p' : SExpr} :
      StatefulStep s p s' p' →
      StatefulStep s (.snd p) s' (.snd p')
  | snd_val {s : State} {a b : SExpr} :
      SValue a → SValue b →
      StatefulStep s (.snd (.pair a b)) s b
  | let_eval {s s' : State} (id : Nat) {v v' body : SExpr} :
      StatefulStep s v s' v' →
      StatefulStep s (.letBind id v body) s' (.letBind id v' body)
  | let_subst {s : State} (id : Nat) {v body : SExpr} :
      SValue v →
      StatefulStep s (.letBind id v body) s (ssubst id v body)
  | app_fn {s s' : State} {fn fn' arg : SExpr} :
      StatefulStep s fn s' fn' →
      StatefulStep s (.app fn arg) s' (.app fn' arg)
  | app_arg {s s' : State} {fn arg arg' : SExpr} :
      SValue fn → StatefulStep s arg s' arg' →
      StatefulStep s (.app fn arg) s' (.app fn arg')
  | app_beta {s : State} (p : Nat) (ty : SType) (body : SExpr) {v : SExpr} :
      SValue v →
      StatefulStep s (.app (.lam p ty body) v) s (ssubst p v body)
  | alloc_exec {s s1 s2 : State} (owner : OwnerId) (hId : HandleId) (sz : Nat) (init : UInt8) :
      0 < sz →
      Core.Step s (.alloc owner (List.replicate sz init)) s1 →
      Core.Step s1 (.alias hId owner 0 .exclusive) s2 →
      StatefulStep s (.alloc owner hId sz init) s2 (.handleVal hId)
  | readHandle_exec {s s' : State} (h : HandleId) {hd : Handle} {val : UInt8} :
      s.handle h = some hd →
      s.byte hd.location = some val →
      Core.Step s (.read h) s' →
      StatefulStep s (.readHandle h) s' (.byte val)
  | writeHandle_eval {s s' : State} (h : HandleId) {v v' : SExpr} :
      StatefulStep s v s' v' →
      StatefulStep s (.writeHandle h v) s' (.writeHandle h v')
  | writeHandle_exec {s s' : State} (h : HandleId) (b : UInt8) :
      Core.Step s (.write h b) s' →
      StatefulStep s (.writeHandle h (.byte b)) s' .unit
  | withView_reserve {s s' : State} (vId : ViewId) (h : HandleId) (mode : AccessMode) (body : SExpr) :
      Core.Step s (.reserve vId h mode) s' →
      StatefulStep s (.withView vId h mode body) s' (.activeView vId body)
  | activeView_eval {s s' : State} (vId : ViewId) {body body' : SExpr} :
      StatefulStep s body s' body' →
      StatefulStep s (.activeView vId body) s' (.activeView vId body')
  | activeView_release {s s' : State} (vId : ViewId) {body : SExpr} :
      SValue body →
      Core.Step s (.release vId) s' →
      StatefulStep s (.activeView vId body) s' body
  | readView_exec {s s' : State} (vId : ViewId) {vw : View} {val : UInt8} :
      s.view vId = some vw →
      s.byte vw.location = some val →
      Core.Step s (.readView vId) s' →
      StatefulStep s (.readView vId) s' (.byte val)
  | writeView_eval {s s' : State} (vId : ViewId) {v v' : SExpr} :
      StatefulStep s v s' v' →
      StatefulStep s (.writeView vId v) s' (.writeView vId v')
  | writeView_exec {s s' : State} (vId : ViewId) (b : UInt8) :
      Core.Step s (.writeView vId b) s' →
      StatefulStep s (.writeView vId (.byte b)) s' .unit
  | destroy_exec {s s' : State} (owner : OwnerId) :
      Core.Step s (.destroy owner) s' →
      StatefulStep s (.destroy owner) s' .unit

inductive StatefulSteps : State → SExpr → State → SExpr → Prop where
  | refl (s : State) (e : SExpr) : StatefulSteps s e s e
  | step {s1 s2 s3 : State} {e1 e2 e3 : SExpr} :
      StatefulStep s1 e1 s2 e2 →
      StatefulSteps s2 e2 s3 e3 →
      StatefulSteps s1 e1 s3 e3

theorem sstep_val_impossible {s s' : State} {e e' : SExpr}
    (h : StatefulStep s e s' e') (hVal : SValue e) : False := by
  induction h with
  | pair_left _ _ => cases hVal; contradiction
  | pair_right _ _ _ => cases hVal; contradiction
  | fst_eval | fst_val | snd_eval | snd_val | let_eval | let_subst | app_fn | app_arg | app_beta =>
    cases hVal
  | alloc_exec | readHandle_exec | writeHandle_eval | writeHandle_exec | withView_reserve =>
    cases hVal
  | activeView_eval | activeView_release | readView_exec | writeView_eval | writeView_exec | destroy_exec =>
    cases hVal

theorem StatefulStep.deterministic {s s1 s2 : State} {e e1 e2 : SExpr}
    (h1 : StatefulStep s e s1 e1) (h2 : StatefulStep s e s2 e2) : s1 = s2 ∧ e1 = e2 := by
  induction h1 generalizing s2 e2 with
  | pair_left ha ih =>
    cases h2 with
    | pair_left ha2 => obtain ⟨hs, he⟩ := ih ha2; subst hs he; exact ⟨rfl, rfl⟩
    | pair_right hva _ => exact False.elim (sstep_val_impossible ha hva)
  | pair_right hva hb ih =>
    cases h2 with
    | pair_left ha2 => exact False.elim (sstep_val_impossible ha2 hva)
    | pair_right _ hb2 => obtain ⟨hs, he⟩ := ih hb2; subst hs he; exact ⟨rfl, rfl⟩
  | fst_eval hp ih =>
    cases h2 with
    | fst_eval hp2 => obtain ⟨hs, he⟩ := ih hp2; subst hs he; exact ⟨rfl, rfl⟩
    | fst_val hva hvb => exact False.elim (sstep_val_impossible hp (.pair hva hvb))
  | fst_val hva hvb =>
    cases h2 with
    | fst_eval hp2 => exact False.elim (sstep_val_impossible hp2 (.pair hva hvb))
    | fst_val => exact ⟨rfl, rfl⟩
  | snd_eval hp ih =>
    cases h2 with
    | snd_eval hp2 => obtain ⟨hs, he⟩ := ih hp2; subst hs he; exact ⟨rfl, rfl⟩
    | snd_val hva hvb => exact False.elim (sstep_val_impossible hp (.pair hva hvb))
  | snd_val hva hvb =>
    cases h2 with
    | snd_eval hp2 => exact False.elim (sstep_val_impossible hp2 (.pair hva hvb))
    | snd_val => exact ⟨rfl, rfl⟩
  | let_eval _ hv ih =>
    cases h2 with
    | let_eval _ hv2 => obtain ⟨hs, he⟩ := ih hv2; subst hs he; exact ⟨rfl, rfl⟩
    | let_subst _ hvv => exact False.elim (sstep_val_impossible hv hvv)
  | let_subst _ hvv =>
    cases h2 with
    | let_eval _ hv2 => exact False.elim (sstep_val_impossible hv2 hvv)
    | let_subst => exact ⟨rfl, rfl⟩
  | app_fn hfn ih =>
    cases h2 with
    | app_fn hfn2 => obtain ⟨hs, he⟩ := ih hfn2; subst hs he; exact ⟨rfl, rfl⟩
    | app_arg hvfn _ => exact False.elim (sstep_val_impossible hfn hvfn)
    | app_beta p ty body _ => exact False.elim (sstep_val_impossible hfn (.lam p ty body))
  | app_arg hvfn harg ih =>
    cases h2 with
    | app_fn hfn2 => exact False.elim (sstep_val_impossible hfn2 hvfn)
    | app_arg _ harg2 => obtain ⟨hs, he⟩ := ih harg2; subst hs he; exact ⟨rfl, rfl⟩
    | app_beta _ _ _ hv => exact False.elim (sstep_val_impossible harg hv)
  | app_beta p ty body hv =>
    cases h2 with
    | app_fn hfn2 => exact False.elim (sstep_val_impossible hfn2 (.lam p ty body))
    | app_arg _ harg2 => exact False.elim (sstep_val_impossible harg2 hv)
    | app_beta => exact ⟨rfl, rfl⟩
  | alloc_exec owner hId sz init _ cs1 cs2 =>
    cases h2 with
    | alloc_exec _ _ _ _ _ cs1' cs2' =>
      have hMid := Core.Step.deterministic cs1 cs1'
      subst hMid
      exact ⟨Core.Step.deterministic cs2 cs2', rfl⟩
  | readHandle_exec h fh lb cs1 =>
    cases h2 with
    | readHandle_exec _ fh2 lb2 cs2 =>
      have hHd := Option.some.inj (fh.symm.trans fh2)
      subst hHd
      have hVal := Option.some.inj (lb.symm.trans lb2)
      subst hVal
      exact ⟨Core.Step.deterministic cs1 cs2, rfl⟩
  | writeHandle_eval h hv ih =>
    cases h2 with
    | writeHandle_eval _ hv2 => obtain ⟨hs, he⟩ := ih hv2; subst hs he; exact ⟨rfl, rfl⟩
    | writeHandle_exec _ b _ => exact False.elim (sstep_val_impossible hv (.byte b))
  | writeHandle_exec h b cs1 =>
    cases h2 with
    | writeHandle_eval _ hv2 => exact False.elim (sstep_val_impossible hv2 (.byte b))
    | writeHandle_exec _ _ cs2 => exact ⟨Core.Step.deterministic cs1 cs2, rfl⟩
  | withView_reserve vId h mode body cs1 =>
    cases h2 with
    | withView_reserve _ _ _ _ cs2 => exact ⟨Core.Step.deterministic cs1 cs2, rfl⟩
  | activeView_eval vId hb ih =>
    cases h2 with
    | activeView_eval _ hb2 => obtain ⟨hs, he⟩ := ih hb2; subst hs he; exact ⟨rfl, rfl⟩
    | activeView_release _ hvb _ => exact False.elim (sstep_val_impossible hb hvb)
  | activeView_release vId hvb cs1 =>
    cases h2 with
    | activeView_eval _ hb2 => exact False.elim (sstep_val_impossible hb2 hvb)
    | activeView_release _ _ cs2 => exact ⟨Core.Step.deterministic cs1 cs2, rfl⟩
  | readView_exec vId fv lb cs1 =>
    cases h2 with
    | readView_exec _ fv2 lb2 cs2 =>
      have hVw := Option.some.inj (fv.symm.trans fv2)
      subst hVw
      have hVal := Option.some.inj (lb.symm.trans lb2)
      subst hVal
      exact ⟨Core.Step.deterministic cs1 cs2, rfl⟩
  | writeView_eval vId hv ih =>
    cases h2 with
    | writeView_eval _ hv2 => obtain ⟨hs, he⟩ := ih hv2; subst hs he; exact ⟨rfl, rfl⟩
    | writeView_exec _ b _ => exact False.elim (sstep_val_impossible hv (.byte b))
  | writeView_exec vId b cs1 =>
    cases h2 with
    | writeView_eval _ hv2 => exact False.elim (sstep_val_impossible hv2 (.byte b))
    | writeView_exec _ _ cs2 => exact ⟨Core.Step.deterministic cs1 cs2, rfl⟩
  | destroy_exec owner cs1 =>
    cases h2 with
    | destroy_exec _ cs2 => exact ⟨Core.Step.deterministic cs1 cs2, rfl⟩

private theorem coreStep_preserves_state_wf {s s' : State} {instr : Instruction}
    (hStep : Core.Step s instr s') (hWf : StateWellFormed s) : StateWellFormed s' :=
  ⟨hStep.owners_valid hWf.1, hStep.references_live hWf.1 hWf.2.1, hStep.views_compatible hWf.2.2⟩

theorem StatefulStep.preserves_state_wf {s s' : State} {e e' : SExpr}
    (hStep : StatefulStep s e s' e') (hWf : StateWellFormed s) : StateWellFormed s' := by
  induction hStep with
  | pair_left _ ih | pair_right _ _ ih | fst_eval _ ih | snd_eval _ ih
  | let_eval _ _ ih | app_fn _ ih | app_arg _ _ ih
  | writeHandle_eval _ _ ih | activeView_eval _ _ ih | writeView_eval _ _ ih => exact ih
  | fst_val | snd_val | let_subst | app_beta => exact hWf
  | alloc_exec _ _ _ _ _ cs1 cs2 =>
    exact coreStep_preserves_state_wf cs2 (coreStep_preserves_state_wf cs1 hWf)
  | readHandle_exec _ _ _ cs | writeHandle_exec _ _ cs | withView_reserve _ _ _ _ cs
  | activeView_release _ _ cs | readView_exec _ _ _ cs | writeView_exec _ _ cs
  | destroy_exec _ cs => exact coreStep_preserves_state_wf cs hWf

theorem StatefulSteps.preserves_state_wf {s s' : State} {e e' : SExpr}
    (hSteps : StatefulSteps s e s' e') (hWf : StateWellFormed s) : StateWellFormed s' := by
  induction hSteps with
  | refl => exact hWf
  | step h1 _ ih => exact ih (h1.preserves_state_wf hWf)

private theorem slookup_head (x : Nat) (tyX : SType) (ctx : SCtx) :
    SCtx.lookup ((x, tyX) :: ctx) x = some tyX := by
  simp [SCtx.lookup]

private theorem slookup_tail {x y : Nat} (hne : y ≠ x) (tyX : SType) (ctx : SCtx) :
    SCtx.lookup ((x, tyX) :: ctx) y = SCtx.lookup ctx y := by
  dsimp [SCtx.lookup]
  have h : (x == y) = false := by simp [beq_eq_false_iff_ne, Ne.symm hne]
  simp [h]

private theorem slookup_exchange {x y : Nat} (hne : x ≠ y) (tyX tyY : SType) (ctx : SCtx) (k : Nat) :
    SCtx.lookup ((x, tyX) :: (y, tyY) :: ctx) k = SCtx.lookup ((y, tyY) :: (x, tyX) :: ctx) k := by
  dsimp [SCtx.lookup]
  by_cases hx : x == k <;> by_cases hy : y == k
  · have hxEq : x = k := beq_iff_eq.mp hx
    have hyEq : y = k := beq_iff_eq.mp hy
    subst hxEq hyEq
    contradiction
  · simp [hx, hy]
  · simp [hx, hy]
  · simp [hx, hy]

private theorem slookup_shadow (x : Nat) (ty1 ty2 : SType) (ctx : SCtx) (k : Nat) :
    SCtx.lookup ((x, ty1) :: (x, ty2) :: ctx) k = SCtx.lookup ((x, ty1) :: ctx) k := by
  dsimp [SCtx.lookup]
  by_cases hx : x == k <;> simp [hx]

def SCtxSub (ctx1 ctx2 : SCtx) : Prop :=
  ∀ id ty, ctx1.lookup id = some ty → ctx2.lookup id = some ty

private theorem sctxSub_empty (ctx : SCtx) : SCtxSub [] ctx := by
  intro id ty h; contradiction

private theorem sctxSub_cons {ctx1 ctx2 : SCtx} (hsub : SCtxSub ctx1 ctx2) (x : Nat) (tyX : SType) :
    SCtxSub ((x, tyX) :: ctx1) ((x, tyX) :: ctx2) := by
  intro id ty h
  by_cases heq : id = x
  · subst heq; rw [slookup_head] at h ⊢; exact h
  · rw [slookup_tail heq] at h ⊢; exact hsub id ty h

theorem swellTyped_weaken {ctx1 ctx2 : SCtx} {e : SExpr} {ty : SType}
    (hTyped : SWellTyped ctx1 e ty) (hsub : SCtxSub ctx1 ctx2) :
    SWellTyped ctx2 e ty := by
  induction hTyped generalizing ctx2 with
  | unit => exact .unit ctx2
  | bool _ b => exact .bool ctx2 b
  | byte _ v => exact .byte ctx2 v
  | handleVal _ id => exact .handleVal ctx2 id
  | viewVal _ id m => exact .viewVal ctx2 id m
  | pair _ _ iha ihb => exact .pair (iha hsub) (ihb hsub)
  | fst _ ih => exact .fst (ih hsub)
  | snd _ ih => exact .snd (ih hsub)
  | var id h => exact .var id (hsub id _ h)
  | letBind id _ _ ihv ihb => exact .letBind id (ihv hsub) (ihb (sctxSub_cons hsub id _))
  | lam p tyP _ ihb => exact .lam p tyP (ihb (sctxSub_cons hsub p _))
  | app _ _ ihfn iharg => exact .app (ihfn hsub) (iharg hsub)
  | alloc _ o h sz i => exact .alloc ctx2 o h sz i
  | readHandle _ h => exact .readHandle ctx2 h
  | writeHandle h _ ih => exact .writeHandle h (ih hsub)
  | withView vId h mode _ ih => exact .withView vId h mode (ih hsub)
  | activeView vId _ ih => exact .activeView vId (ih hsub)
  | readView _ vId => exact .readView ctx2 vId
  | writeView vId _ ih => exact .writeView vId (ih hsub)
  | destroy _ o => exact .destroy ctx2 o

private theorem swellTyped_closed_weaken {e : SExpr} {ty : SType}
    (hTyped : SWellTyped [] e ty) (ctx : SCtx) :
    SWellTyped ctx e ty :=
  swellTyped_weaken hTyped (sctxSub_empty ctx)

private theorem swellTyped_exchange {x y : Nat} (hne : x ≠ y) {tyX tyY ty : SType}
    {e : SExpr} {ctx : SCtx}
    (h : SWellTyped ((x, tyX) :: (y, tyY) :: ctx) e ty) :
    SWellTyped ((y, tyY) :: (x, tyX) :: ctx) e ty :=
  swellTyped_weaken h (fun _ _ hL => by rw [slookup_exchange (Ne.symm hne)]; exact hL)

private theorem swellTyped_shadow {x : Nat} {ty1 ty2 ty : SType}
    {e : SExpr} {ctx : SCtx}
    (h : SWellTyped ((x, ty1) :: (x, ty2) :: ctx) e ty) :
    SWellTyped ((x, ty1) :: ctx) e ty :=
  swellTyped_weaken h (fun _ _ hL => by rw [slookup_shadow] at hL; exact hL)

theorem ssubstitution_value {val : SExpr} {tyV : SType}
    (hValTyped : SWellTyped [] val tyV) (body : SExpr) :
    ∀ {ctx : SCtx} {varId : Nat} {tyBody : SType},
      SWellTyped ((varId, tyV) :: ctx) body tyBody →
      SWellTyped ctx (ssubst varId val body) tyBody := by
  induction body with
  | unit => intro ctx _ _ hb; cases hb; exact .unit ctx
  | bool b => intro ctx _ _ hb; cases hb; exact .bool ctx b
  | byte v => intro ctx _ _ hb; cases hb; exact .byte ctx v
  | handleVal id => intro ctx _ _ hb; cases hb; exact .handleVal ctx id
  | viewVal id => intro ctx _ _ hb; cases hb; exact .viewVal ctx id _
  | pair a b iha ihb =>
    intro ctx _ _ hb
    cases hb with | pair ha hb => exact .pair (iha ha) (ihb hb)
  | fst p ih =>
    intro ctx _ _ hb
    cases hb with | fst hp => exact .fst (ih hp)
  | snd p ih =>
    intro ctx _ _ hb
    cases hb with | snd hp => exact .snd (ih hp)
  | var id =>
    intro ctx varId tyBody hb
    cases hb with
    | var _ h =>
      by_cases heq : id = varId
      · subst heq
        simp only [ssubst, ite_true]
        rw [slookup_head] at h
        have hty : tyV = tyBody := Option.some.inj h
        subst hty
        exact swellTyped_closed_weaken hValTyped ctx
      · have hne : (id = varId) = False := eq_false heq
        simp only [ssubst, hne, ↓reduceIte]
        rw [slookup_tail heq] at h
        exact .var id h
  | letBind id v b ihv ihb =>
    intro ctx varId tyBody hb
    cases hb with
    | letBind _ hv hb =>
      have hv' := ihv hv
      by_cases heq : id = varId
      · subst heq
        simp only [ssubst, ite_true]
        exact .letBind id hv' (swellTyped_shadow hb)
      · have hne : (id = varId) = False := eq_false heq
        simp only [ssubst, hne, ↓reduceIte]
        exact .letBind id hv' (ihb (swellTyped_exchange heq hb))
  | lam p tyP b ihb =>
    intro ctx varId tyBody hb
    cases hb with
    | lam _ _ hb =>
      by_cases heq : p = varId
      · subst heq
        simp only [ssubst, ite_true]
        exact .lam p tyP (swellTyped_shadow hb)
      · have hne : (p = varId) = False := eq_false heq
        simp only [ssubst, hne, ↓reduceIte]
        exact .lam p tyP (ihb (swellTyped_exchange heq hb))
  | app fn arg ihfn iharg =>
    intro ctx _ _ hb
    cases hb with | app hfn harg => exact .app (ihfn hfn) (iharg harg)
  | alloc owner hId sz init =>
    intro ctx _ _ hb; cases hb; exact .alloc ctx owner hId sz init
  | readHandle h =>
    intro ctx _ _ hb; cases hb; exact .readHandle ctx h
  | writeHandle h v ih =>
    intro ctx _ _ hb
    cases hb with | writeHandle _ hv => exact .writeHandle h (ih hv)
  | withView vId h mode b ih =>
    intro ctx _ _ hb
    cases hb with | withView _ _ _ hb' => exact .withView vId h mode (ih hb')
  | activeView vId b ih =>
    intro ctx _ _ hb
    cases hb with | activeView _ hb' => exact .activeView vId (ih hb')
  | readView vId =>
    intro ctx _ _ hb; cases hb; exact .readView ctx vId
  | writeView vId v ih =>
    intro ctx _ _ hb
    cases hb with | writeView _ hv => exact .writeView vId (ih hv)
  | destroy owner =>
    intro ctx _ _ hb; cases hb; exact .destroy ctx owner

theorem StatefulStep.preservation {s s' : State} {e e' : SExpr} {ty : SType}
    (hStep : StatefulStep s e s' e') (hTyped : SWellTyped [] e ty) :
    SWellTyped [] e' ty := by
  induction hStep generalizing ty with
  | pair_left _ ih =>
    cases hTyped with | pair ha hb => exact .pair (ih ha) hb
  | pair_right _ _ ih =>
    cases hTyped with | pair ha hb => exact .pair ha (ih hb)
  | fst_eval _ ih =>
    cases hTyped with | fst hp => exact .fst (ih hp)
  | fst_val _ _ =>
    cases hTyped with | fst hp => cases hp with | pair ha _ => exact ha
  | snd_eval _ ih =>
    cases hTyped with | snd hp => exact .snd (ih hp)
  | snd_val _ _ =>
    cases hTyped with | snd hp => cases hp with | pair _ hb => exact hb
  | let_eval id _ ih =>
    cases hTyped with | letBind _ hv hb => exact .letBind id (ih hv) hb
  | let_subst _ _ =>
    cases hTyped with | letBind _ hv hb => exact ssubstitution_value hv _ hb
  | app_fn _ ih =>
    cases hTyped with | app hfn harg => exact .app (ih hfn) harg
  | app_arg _ _ ih =>
    cases hTyped with | app hfn harg => exact .app hfn (ih harg)
  | app_beta _ _ _ _ =>
    cases hTyped with
    | app hfn harg =>
      cases hfn with | lam _ _ hb => exact ssubstitution_value harg _ hb
  | alloc_exec =>
    cases hTyped; exact .handleVal [] _
  | readHandle_exec =>
    cases hTyped; exact .byte [] _
  | writeHandle_eval h _ ih =>
    cases hTyped with | writeHandle _ hv => exact .writeHandle h (ih hv)
  | writeHandle_exec =>
    cases hTyped; exact .unit []
  | withView_reserve vId _ _ _ =>
    cases hTyped with | withView _ _ _ hb => exact .activeView vId hb
  | activeView_eval vId _ ih =>
    cases hTyped with | activeView _ hb => exact .activeView vId (ih hb)
  | activeView_release =>
    cases hTyped with | activeView _ hb => exact hb
  | readView_exec =>
    cases hTyped; exact .byte [] _
  | writeView_eval vId _ ih =>
    cases hTyped with | writeView _ hv => exact .writeView vId (ih hv)
  | writeView_exec =>
    cases hTyped; exact .unit []
  | destroy_exec =>
    cases hTyped; exact .unit []

private theorem scanonical_prod {v : SExpr} (hVal : SValue v) {tyA tyB : SType}
    (hTyped : SWellTyped [] v (.prod tyA tyB)) :
    ∃ a b, v = .pair a b ∧ SValue a ∧ SValue b := by
  cases hVal with
  | pair va vb => cases hTyped; exact ⟨_, _, rfl, va, vb⟩
  | unit | bool _ | byte _ | handleVal _ | viewVal _ | lam _ _ _ => cases hTyped

private theorem scanonical_arrow {v : SExpr} (hVal : SValue v) {dom cod : SType}
    (hTyped : SWellTyped [] v (.arrow dom cod)) :
    ∃ p ty body, v = .lam p ty body := by
  cases hVal with
  | lam p t b => cases hTyped; exact ⟨_, _, _, rfl⟩
  | unit | bool _ | byte _ | handleVal _ | viewVal _ | pair _ _ => cases hTyped

private theorem scanonical_byte {v : SExpr} (hVal : SValue v)
    (hTyped : SWellTyped [] v .byte) :
    ∃ b : UInt8, v = .byte b := by
  cases hVal with
  | byte b => exact ⟨b, rfl⟩
  | unit | bool _ | handleVal _ | viewVal _ | lam _ _ _ | pair _ _ => cases hTyped

/-- Inductive characterization of a redex blocked solely at an unsatisfied
runtime/checked resource precondition (missing handle, borrow conflict, etc.). -/
inductive ResourceBoundary : State → SExpr → Prop where
  | head {s : State} {e : SExpr} :
      (∃ o h sz i, e = .alloc o h sz i) ∨
      (∃ h, e = .readHandle h) ∨
      (∃ h b, e = .writeHandle h (.byte b)) ∨
      (∃ vId h m body, e = .withView vId h m body) ∨
      (∃ vId v, SValue v ∧ e = .activeView vId v) ∨
      (∃ vId, e = .readView vId) ∨
      (∃ vId b, e = .writeView vId (.byte b)) ∨
      (∃ o, e = .destroy o) →
      (¬ ∃ s' e', StatefulStep s e s' e') →
      ResourceBoundary s e
  | pair_left {s : State} {a b : SExpr} :
      ResourceBoundary s a → ResourceBoundary s (.pair a b)
  | pair_right {s : State} {a b : SExpr} :
      SValue a → ResourceBoundary s b → ResourceBoundary s (.pair a b)
  | fst {s : State} {p : SExpr} :
      ResourceBoundary s p → ResourceBoundary s (.fst p)
  | snd {s : State} {p : SExpr} :
      ResourceBoundary s p → ResourceBoundary s (.snd p)
  | letBind {s : State} (id : Nat) {v body : SExpr} :
      ResourceBoundary s v → ResourceBoundary s (.letBind id v body)
  | app_fn {s : State} {fn arg : SExpr} :
      ResourceBoundary s fn → ResourceBoundary s (.app fn arg)
  | app_arg {s : State} {fn arg : SExpr} :
      SValue fn → ResourceBoundary s arg → ResourceBoundary s (.app fn arg)
  | writeHandle {s : State} (h : HandleId) {v : SExpr} :
      ResourceBoundary s v → ResourceBoundary s (.writeHandle h v)
  | activeView {s : State} (vId : ViewId) {body : SExpr} :
      ResourceBoundary s body → ResourceBoundary s (.activeView vId body)
  | writeView {s : State} (vId : ViewId) {v : SExpr} :
      ResourceBoundary s v → ResourceBoundary s (.writeView vId v)

def ResourceReady (s : State) (e : SExpr) : Prop :=
  ¬ ResourceBoundary s e

private theorem stateful_progress_ctx {ctx : SCtx} {e : SExpr} {ty : SType}
    (hTyped : SWellTyped ctx e ty) (s : State) :
    ctx = [] → SValue e ∨ (∃ s' e', StatefulStep s e s' e') ∨ ResourceBoundary s e := by
  induction hTyped with
  | unit => intro _; exact Or.inl .unit
  | bool _ b => intro _; exact Or.inl (.bool b)
  | byte _ v => intro _; exact Or.inl (.byte v)
  | handleVal _ id => intro _; exact Or.inl (.handleVal id)
  | viewVal _ id _ => intro _; exact Or.inl (.viewVal id)
  | pair _ _ iha ihb =>
    intro hEmpty
    rcases iha hEmpty with hValA | ⟨s', a', hStepA⟩ | hBndA
    · rcases ihb hEmpty with hValB | ⟨s', b', hStepB⟩ | hBndB
      · exact Or.inl (.pair hValA hValB)
      · exact Or.inr (Or.inl ⟨s', .pair _ b', .pair_right hValA hStepB⟩)
      · exact Or.inr (Or.inr (.pair_right hValA hBndB))
    · exact Or.inr (Or.inl ⟨s', .pair a' _, .pair_left hStepA⟩)
    · exact Or.inr (Or.inr (.pair_left hBndA))
  | fst hP ih =>
    intro hEmpty
    rcases ih hEmpty with hValP | ⟨s', p', hStepP⟩ | hBndP
    · subst hEmpty
      obtain ⟨a, b, rfl, hValA, hValB⟩ := scanonical_prod hValP hP
      exact Or.inr (Or.inl ⟨s, a, .fst_val hValA hValB⟩)
    · exact Or.inr (Or.inl ⟨s', .fst p', .fst_eval hStepP⟩)
    · exact Or.inr (Or.inr (.fst hBndP))
  | snd hP ih =>
    intro hEmpty
    rcases ih hEmpty with hValP | ⟨s', p', hStepP⟩ | hBndP
    · subst hEmpty
      obtain ⟨a, b, rfl, hValA, hValB⟩ := scanonical_prod hValP hP
      exact Or.inr (Or.inl ⟨s, b, .snd_val hValA hValB⟩)
    · exact Or.inr (Or.inl ⟨s', .snd p', .snd_eval hStepP⟩)
    · exact Or.inr (Or.inr (.snd hBndP))
  | var id hLookup =>
    intro hEmpty
    subst hEmpty
    contradiction
  | letBind id _ _ ihv _ =>
    intro hEmpty
    rcases ihv hEmpty with hValV | ⟨s', v', hStepV⟩ | hBndV
    · exact Or.inr (Or.inl ⟨s, ssubst id _ _, .let_subst id hValV⟩)
    · exact Or.inr (Or.inl ⟨s', .letBind id v' _, .let_eval id hStepV⟩)
    · exact Or.inr (Or.inr (.letBind id hBndV))
  | lam p tyP _ _ =>
    intro _
    exact Or.inl (.lam p tyP _)
  | app hFn _ ihfn iharg =>
    intro hEmpty
    rcases ihfn hEmpty with hValFn | ⟨s', fn', hStepFn⟩ | hBndFn
    · subst hEmpty
      obtain ⟨p, ty, body, rfl⟩ := scanonical_arrow hValFn hFn
      rcases iharg rfl with hValArg | ⟨s', arg', hStepArg⟩ | hBndArg
      · exact Or.inr (Or.inl ⟨s, ssubst p _ body, .app_beta p ty body hValArg⟩)
      · exact Or.inr (Or.inl ⟨s', .app _ arg', .app_arg hValFn hStepArg⟩)
      · exact Or.inr (Or.inr (.app_arg hValFn hBndArg))
    · exact Or.inr (Or.inl ⟨s', .app fn' _, .app_fn hStepFn⟩)
    · exact Or.inr (Or.inr (.app_fn hBndFn))
  | alloc _ o h sz i =>
    intro _
    by_cases hStep : ∃ s' e', StatefulStep s (.alloc o h sz i) s' e'
    · exact Or.inr (Or.inl hStep)
    · exact Or.inr (Or.inr (.head (Or.inl ⟨o, h, sz, i, rfl⟩) hStep))
  | readHandle _ h =>
    intro _
    by_cases hStep : ∃ s' e', StatefulStep s (.readHandle h) s' e'
    · exact Or.inr (Or.inl hStep)
    · exact Or.inr (Or.inr (.head (Or.inr (Or.inl ⟨h, rfl⟩)) hStep))
  | writeHandle h hV ih =>
    intro hEmpty
    rcases ih hEmpty with hValV | ⟨s', v', hStepV⟩ | hBndV
    · subst hEmpty
      obtain ⟨b, rfl⟩ := scanonical_byte hValV hV
      by_cases hStep : ∃ s' e', StatefulStep s (.writeHandle h (.byte b)) s' e'
      · exact Or.inr (Or.inl hStep)
      · exact Or.inr (Or.inr (.head (Or.inr (Or.inr (Or.inl ⟨h, b, rfl⟩))) hStep))
    · exact Or.inr (Or.inl ⟨s', .writeHandle h v', .writeHandle_eval h hStepV⟩)
    · exact Or.inr (Or.inr (.writeHandle h hBndV))
  | withView vId h mode _hb _ih =>
    rename_i bodyE _tyB
    intro _
    by_cases hStep : ∃ s' e', StatefulStep s (.withView vId h mode bodyE) s' e'
    · exact Or.inr (Or.inl hStep)
    · exact Or.inr (Or.inr (.head (Or.inr (Or.inr (Or.inr (Or.inl ⟨vId, h, mode, bodyE, rfl⟩)))) hStep))
  | activeView vId _hB ih =>
    rename_i bodyE _tyB
    intro hEmpty
    rcases ih hEmpty with hValB | ⟨s', b', hStepB⟩ | hBndB
    · by_cases hStep : ∃ s' e', StatefulStep s (.activeView vId bodyE) s' e'
      · exact Or.inr (Or.inl hStep)
      · exact Or.inr (Or.inr (.head (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨vId, bodyE, hValB, rfl⟩))))) hStep))
    · exact Or.inr (Or.inl ⟨s', .activeView vId b', .activeView_eval vId hStepB⟩)
    · exact Or.inr (Or.inr (.activeView vId hBndB))
  | readView _ vId =>
    intro _
    by_cases hStep : ∃ s' e', StatefulStep s (.readView vId) s' e'
    · exact Or.inr (Or.inl hStep)
    · exact Or.inr (Or.inr (.head (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨vId, rfl⟩)))))) hStep))
  | writeView vId hV ih =>
    intro hEmpty
    rcases ih hEmpty with hValV | ⟨s', v', hStepV⟩ | hBndV
    · subst hEmpty
      obtain ⟨b, rfl⟩ := scanonical_byte hValV hV
      by_cases hStep : ∃ s' e', StatefulStep s (.writeView vId (.byte b)) s' e'
      · exact Or.inr (Or.inl hStep)
      · exact Or.inr (Or.inr (.head (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨vId, b, rfl⟩))))))) hStep))
    · exact Or.inr (Or.inl ⟨s', .writeView vId v', .writeView_eval vId hStepV⟩)
    · exact Or.inr (Or.inr (.writeView vId hBndV))
  | destroy _ o =>
    intro _
    by_cases hStep : ∃ s' e', StatefulStep s (.destroy o) s' e'
    · exact Or.inr (Or.inl hStep)
    · exact Or.inr (Or.inr (.head (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨o, rfl⟩))))))) hStep))

theorem stateful_progress {e : SExpr} {ty : SType}
    (hTyped : SWellTyped [] e ty) (s : State) :
    SValue e ∨ (∃ s' e', StatefulStep s e s' e') ∨ ResourceBoundary s e :=
  stateful_progress_ctx hTyped s rfl

theorem stateful_progress_ready {e : SExpr} {ty : SType}
    (hTyped : SWellTyped [] e ty) {s : State} (hReady : ResourceReady s e) :
    SValue e ∨ ∃ s' e', StatefulStep s e s' e' := by
  rcases stateful_progress hTyped s with hVal | hStep | hBnd
  · exact Or.inl hVal
  · exact Or.inr hStep
  · exact False.elim (hReady hBnd)

/-- Connecting stateful core execution directly to `Representation.HeapRepresents`:
writing a byte through handle `h` updates the logical byte at `hd.location` and
frames every unrelated allocation. -/
theorem stateful_writeHandle_heap_simulation {s s' : State} {h : HandleId}
    {hd : Handle} {b : UInt8} {oldExpr : CoreExpr}
    (hFound : s.handle h = some hd)
    (hStep : StatefulStep s (.writeHandle h (.byte b)) s' .unit)
    (hOld : HeapRepresents s hd.location.allocation hd.location.offset oldExpr CoreType.byte) :
    HeapRepresents s' hd.location.allocation hd.location.offset
      (.int false 8 (Int.ofNat b.toNat)) CoreType.byte ∧
    ∀ other off e ty, other ≠ hd.location.allocation →
      HeapRepresents s other off e ty → HeapRepresents s' other off e ty := by
  cases hStep with
  | writeHandle_exec _ _ cs =>
    cases cs with
    | write found2 _ _ _ =>
      have hEq := Option.some.inj (found2.symm.trans hFound)
      rw [hEq]
      refine ⟨rep_write_byte_simulation s hd.location.allocation hd.location.offset oldExpr b hOld, ?_⟩
      intro other off e ty hNe hOther
      exact rep_write_preserves_other s hd.location b other off e ty hNe hOther

-- Proof Erasure for the Unified Stateful Core

inductive ErasedSExpr where
  | unit : ErasedSExpr
  | bool (b : Bool) : ErasedSExpr
  | byte (v : UInt8) : ErasedSExpr
  | pair (a b : ErasedSExpr) : ErasedSExpr
  | fst (p : ErasedSExpr) : ErasedSExpr
  | snd (p : ErasedSExpr) : ErasedSExpr
  | var (id : Nat) : ErasedSExpr
  | letBind (id : Nat) (v body : ErasedSExpr) : ErasedSExpr
  | lam (p : Nat) (body : ErasedSExpr) : ErasedSExpr
  | app (fn arg : ErasedSExpr) : ErasedSExpr
  | handleVal (id : HandleId) : ErasedSExpr
  | viewVal (id : ViewId) : ErasedSExpr
  | alloc (owner : OwnerId) (hId : HandleId) (size : Nat) (init : UInt8) : ErasedSExpr
  | readHandle (h : HandleId) : ErasedSExpr
  | writeHandle (h : HandleId) (v : ErasedSExpr) : ErasedSExpr
  | withView (vId : ViewId) (h : HandleId) (body : ErasedSExpr) : ErasedSExpr
  | activeView (vId : ViewId) (body : ErasedSExpr) : ErasedSExpr
  | readView (vId : ViewId) : ErasedSExpr
  | writeView (vId : ViewId) (v : ErasedSExpr) : ErasedSExpr
  | destroy (owner : OwnerId) : ErasedSExpr
  deriving Repr, DecidableEq

def serase : SExpr → ErasedSExpr
  | .unit => .unit
  | .bool b => .bool b
  | .byte v => .byte v
  | .pair a b => .pair (serase a) (serase b)
  | .fst p => .fst (serase p)
  | .snd p => .snd (serase p)
  | .var id => .var id
  | .letBind id v body => .letBind id (serase v) (serase body)
  | .lam p _ body => .lam p (serase body)
  | .app fn arg => .app (serase fn) (serase arg)
  | .handleVal id => .handleVal id
  | .viewVal id => .viewVal id
  | .alloc owner hId sz init => .alloc owner hId sz init
  | .readHandle h => .readHandle h
  | .writeHandle h v => .writeHandle h (serase v)
  | .withView vId h _ body => .withView vId h (serase body)
  | .activeView vId body => .activeView vId (serase body)
  | .readView vId => .readView vId
  | .writeView vId v => .writeView vId (serase v)
  | .destroy owner => .destroy owner

def erasedSSubst (varId : Nat) (val : ErasedSExpr) : ErasedSExpr → ErasedSExpr
  | .unit => .unit
  | .bool b => .bool b
  | .byte v => .byte v
  | .pair a b => .pair (erasedSSubst varId val a) (erasedSSubst varId val b)
  | .fst p => .fst (erasedSSubst varId val p)
  | .snd p => .snd (erasedSSubst varId val p)
  | .var id => if id = varId then val else .var id
  | .letBind id v body =>
    let v' := erasedSSubst varId val v
    let body' := if id = varId then body else erasedSSubst varId val body
    .letBind id v' body'
  | .lam p body =>
    let body' := if p = varId then body else erasedSSubst varId val body
    .lam p body'
  | .app fn arg => .app (erasedSSubst varId val fn) (erasedSSubst varId val arg)
  | .handleVal id => .handleVal id
  | .viewVal id => .viewVal id
  | .alloc owner hId sz init => .alloc owner hId sz init
  | .readHandle h => .readHandle h
  | .writeHandle h v => .writeHandle h (erasedSSubst varId val v)
  | .withView vId h body => .withView vId h (erasedSSubst varId val body)
  | .activeView vId body => .activeView vId (erasedSSubst varId val body)
  | .readView vId => .readView vId
  | .writeView vId v => .writeView vId (erasedSSubst varId val v)
  | .destroy owner => .destroy owner

theorem serase_subst (varId : Nat) (val : SExpr) (body : SExpr) :
    serase (ssubst varId val body) = erasedSSubst varId (serase val) (serase body) := by
  induction body with
  | unit | bool _ | byte _ | handleVal _ | viewVal _ | alloc _ _ _ _ | readHandle _ | readView _ | destroy _ => rfl
  | pair a b iha ihb => simp only [ssubst, serase, iha, ihb, erasedSSubst]
  | fst p ih => simp only [ssubst, serase, ih, erasedSSubst]
  | snd p ih => simp only [ssubst, serase, ih, erasedSSubst]
  | var id => simp only [ssubst, serase]; dsimp [erasedSSubst]; split <;> rfl
  | letBind id v b ihv ihb => simp only [ssubst, serase, ihv, erasedSSubst]; split <;> simp [ihb]
  | lam p ty b ihb => simp only [ssubst, serase, erasedSSubst]; split <;> simp [ihb]
  | app fn arg ihfn iharg => simp only [ssubst, serase, ihfn, iharg, erasedSSubst]
  | writeHandle h v ih => simp only [ssubst, serase, ih, erasedSSubst]
  | withView vId h m b ih => simp only [ssubst, serase, ih, erasedSSubst]
  | activeView vId b ih => simp only [ssubst, serase, ih, erasedSSubst]
  | writeView vId v ih => simp only [ssubst, serase, ih, erasedSSubst]

inductive ErasedSValue : ErasedSExpr → Prop where
  | unit : ErasedSValue .unit
  | bool (b : Bool) : ErasedSValue (.bool b)
  | byte (v : UInt8) : ErasedSValue (.byte v)
  | handleVal (id : HandleId) : ErasedSValue (.handleVal id)
  | viewVal (id : ViewId) : ErasedSValue (.viewVal id)
  | lam (p : Nat) (body : ErasedSExpr) : ErasedSValue (.lam p body)
  | pair {a b : ErasedSExpr} : ErasedSValue a → ErasedSValue b → ErasedSValue (.pair a b)

theorem svalue_erase {e : SExpr} (h : SValue e) : ErasedSValue (serase e) := by
  induction h with
  | unit => exact .unit
  | bool b => exact .bool b
  | byte v => exact .byte v
  | handleVal id => exact .handleVal id
  | viewVal id => exact .viewVal id
  | lam p _ _ => exact .lam p _
  | pair _ _ iha ihb => exact .pair iha ihb

inductive ErasedStatefulStep : State → ErasedSExpr → State → ErasedSExpr → Prop where
  | pair_left {s s' : State} {a a' b : ErasedSExpr} :
      ErasedStatefulStep s a s' a' →
      ErasedStatefulStep s (.pair a b) s' (.pair a' b)
  | pair_right {s s' : State} {a b b' : ErasedSExpr} :
      ErasedSValue a → ErasedStatefulStep s b s' b' →
      ErasedStatefulStep s (.pair a b) s' (.pair a b')
  | fst_eval {s s' : State} {p p' : ErasedSExpr} :
      ErasedStatefulStep s p s' p' →
      ErasedStatefulStep s (.fst p) s' (.fst p')
  | fst_val {s : State} {a b : ErasedSExpr} :
      ErasedSValue a → ErasedSValue b →
      ErasedStatefulStep s (.fst (.pair a b)) s a
  | snd_eval {s s' : State} {p p' : ErasedSExpr} :
      ErasedStatefulStep s p s' p' →
      ErasedStatefulStep s (.snd p) s' (.snd p')
  | snd_val {s : State} {a b : ErasedSExpr} :
      ErasedSValue a → ErasedSValue b →
      ErasedStatefulStep s (.snd (.pair a b)) s b
  | let_eval {s s' : State} (id : Nat) {v v' body : ErasedSExpr} :
      ErasedStatefulStep s v s' v' →
      ErasedStatefulStep s (.letBind id v body) s' (.letBind id v' body)
  | let_subst {s : State} (id : Nat) {v body : ErasedSExpr} :
      ErasedSValue v →
      ErasedStatefulStep s (.letBind id v body) s (erasedSSubst id v body)
  | app_fn {s s' : State} {fn fn' arg : ErasedSExpr} :
      ErasedStatefulStep s fn s' fn' →
      ErasedStatefulStep s (.app fn arg) s' (.app fn' arg)
  | app_arg {s s' : State} {fn arg arg' : ErasedSExpr} :
      ErasedSValue fn → ErasedStatefulStep s arg s' arg' →
      ErasedStatefulStep s (.app fn arg) s' (.app fn arg')
  | app_beta {s : State} (p : Nat) (body : ErasedSExpr) {v : ErasedSExpr} :
      ErasedSValue v →
      ErasedStatefulStep s (.app (.lam p body) v) s (erasedSSubst p v body)
  | alloc_exec {s s1 s2 : State} (owner : OwnerId) (hId : HandleId) (sz : Nat) (init : UInt8) :
      0 < sz →
      Core.Step s (.alloc owner (List.replicate sz init)) s1 →
      Core.Step s1 (.alias hId owner 0 .exclusive) s2 →
      ErasedStatefulStep s (.alloc owner hId sz init) s2 (.handleVal hId)
  | readHandle_exec {s s' : State} (h : HandleId) {hd : Handle} {val : UInt8} :
      s.handle h = some hd →
      s.byte hd.location = some val →
      Core.Step s (.read h) s' →
      ErasedStatefulStep s (.readHandle h) s' (.byte val)
  | writeHandle_eval {s s' : State} (h : HandleId) {v v' : ErasedSExpr} :
      ErasedStatefulStep s v s' v' →
      ErasedStatefulStep s (.writeHandle h v) s' (.writeHandle h v')
  | writeHandle_exec {s s' : State} (h : HandleId) (b : UInt8) :
      Core.Step s (.write h b) s' →
      ErasedStatefulStep s (.writeHandle h (.byte b)) s' .unit
  | withView_reserve {s s' : State} (vId : ViewId) (h : HandleId) (mode : AccessMode) (body : ErasedSExpr) :
      Core.Step s (.reserve vId h mode) s' →
      ErasedStatefulStep s (.withView vId h body) s' (.activeView vId body)
  | activeView_eval {s s' : State} (vId : ViewId) {body body' : ErasedSExpr} :
      ErasedStatefulStep s body s' body' →
      ErasedStatefulStep s (.activeView vId body) s' (.activeView vId body')
  | activeView_release {s s' : State} (vId : ViewId) {body : ErasedSExpr} :
      ErasedSValue body →
      Core.Step s (.release vId) s' →
      ErasedStatefulStep s (.activeView vId body) s' body
  | readView_exec {s s' : State} (vId : ViewId) {vw : View} {val : UInt8} :
      s.view vId = some vw →
      s.byte vw.location = some val →
      Core.Step s (.readView vId) s' →
      ErasedStatefulStep s (.readView vId) s' (.byte val)
  | writeView_eval {s s' : State} (vId : ViewId) {v v' : ErasedSExpr} :
      ErasedStatefulStep s v s' v' →
      ErasedStatefulStep s (.writeView vId v) s' (.writeView vId v')
  | writeView_exec {s s' : State} (vId : ViewId) (b : UInt8) :
      Core.Step s (.writeView vId b) s' →
      ErasedStatefulStep s (.writeView vId (.byte b)) s' .unit
  | destroy_exec {s s' : State} (owner : OwnerId) :
      Core.Step s (.destroy owner) s' →
      ErasedStatefulStep s (.destroy owner) s' .unit

theorem stateful_erasure_simulation {s s' : State} {e e' : SExpr}
    (hStep : StatefulStep s e s' e') :
    ErasedStatefulStep s (serase e) s' (serase e') := by
  induction hStep with
  | pair_left _ ih => exact .pair_left ih
  | pair_right ha _ ih => exact .pair_right (svalue_erase ha) ih
  | fst_eval _ ih => exact .fst_eval ih
  | fst_val ha hb => exact .fst_val (svalue_erase ha) (svalue_erase hb)
  | snd_eval _ ih => exact .snd_eval ih
  | snd_val ha hb => exact .snd_val (svalue_erase ha) (svalue_erase hb)
  | let_eval id _ ih => exact .let_eval id ih
  | let_subst id hv =>
    dsimp [serase]
    rw [serase_subst]
    exact .let_subst id (svalue_erase hv)
  | app_fn _ ih => exact .app_fn ih
  | app_arg hfn _ ih => exact .app_arg (svalue_erase hfn) ih
  | app_beta p _ body hv =>
    dsimp [serase]
    rw [serase_subst]
    exact .app_beta p (serase body) (svalue_erase hv)
  | alloc_exec o h sz i hPos cs1 cs2 => exact .alloc_exec o h sz i hPos cs1 cs2
  | readHandle_exec h fh lb cs => exact .readHandle_exec h fh lb cs
  | writeHandle_eval h _ ih => exact .writeHandle_eval h ih
  | writeHandle_exec h b cs => exact .writeHandle_exec h b cs
  | withView_reserve vId h mode body cs => exact .withView_reserve vId h mode (serase body) cs
  | activeView_eval vId _ ih => exact .activeView_eval vId ih
  | activeView_release vId hvb cs => exact .activeView_release vId (svalue_erase hvb) cs
  | readView_exec vId fv lb cs => exact .readView_exec vId fv lb cs
  | writeView_eval vId _ ih => exact .writeView_eval vId ih
  | writeView_exec vId b cs => exact .writeView_exec vId b cs
  | destroy_exec o cs => exact .destroy_exec o cs

end Aethel.StatefulCore
