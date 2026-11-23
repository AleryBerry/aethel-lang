import Aethel.CoreAST
import Aethel.Machine

namespace Aethel.CoreSemantics

open Functional Core Structured CoreAST

/-- Operational reduction step of the unified sequential core. -/
inductive Step : State → CoreExpr → State → CoreExpr → Prop where
  -- Pairs
  | pair_left {s s' : State} {a a' b : CoreExpr} :
      Step s a s' a' →
      Step s (.pair a b) s' (.pair a' b)
  | pair_right {s s' : State} {a b b' : CoreExpr} :
      Value a → Step s b s' b' →
      Step s (.pair a b) s' (.pair a b')
  | fst_eval {s s' : State} {p p' : CoreExpr} :
      Step s p s' p' →
      Step s (.fst p) s' (.fst p')
  | fst_val {s : State} {a b : CoreExpr} :
      Value a → Value b →
      Step s (.fst (.pair a b)) s a
  | snd_eval {s s' : State} {p p' : CoreExpr} :
      Step s p s' p' →
      Step s (.snd p) s' (.snd p')
  | snd_val {s : State} {a b : CoreExpr} :
      Value a → Value b →
      Step s (.snd (.pair a b)) s b
  -- ADTs
  | adt_eval {s s' : State} (tag : Nat) {p p' : CoreExpr} :
      Step s p s' p' →
      Step s (.adt tag p) s' (.adt tag p')
  | match_eval {s s' : State} {sc sc' : CoreExpr} (tag : Nat) {onM onE : CoreExpr} :
      Step s sc s' sc' →
      Step s (.matchTag sc tag onM onE) s' (.matchTag sc' tag onM onE)
  | match_hit {s : State} (tag : Nat) {p : CoreExpr} {onM onE : CoreExpr} :
      Value p →
      Step s (.matchTag (.adt tag p) tag onM onE) s onM
  | match_miss {s : State} (tag1 tag2 : Nat) {p : CoreExpr} {onM onE : CoreExpr} :
      tag1 ≠ tag2 → Value p →
      Step s (.matchTag (.adt tag1 p) tag2 onM onE) s onE
  | match_bool_true {s : State} {onM onE : CoreExpr} :
      Step s (.matchTag (.bool true) 1 onM onE) s onM
  | match_bool_false {s : State} {onM onE : CoreExpr} :
      Step s (.matchTag (.bool false) 1 onM onE) s onE
  -- Let binding
  | let_eval {s s' : State} (id : Nat) {v v' body : CoreExpr} :
      Step s v s' v' →
      Step s (.letBind id v body) s' (.letBind id v' body)
  | let_subst {s : State} (id : Nat) {v body : CoreExpr} :
      Value v →
      Step s (.letBind id v body) s (subst id v body)
  -- Lambda and Application
  | app_fn {s s' : State} {fn fn' arg : CoreExpr} :
      Step s fn s' fn' →
      Step s (.app fn arg) s' (.app fn' arg)
  | app_arg {s s' : State} {fn arg arg' : CoreExpr} :
      Value fn → Step s arg s' arg' →
      Step s (.app fn arg) s' (.app fn arg')
  | app_beta {s : State} (p : Nat) (ty : CoreType) (body : CoreExpr) (eff : Effect) {v : CoreExpr} :
      Value v →
      Step s (.app (.lam p ty body eff) v) s (subst p v body)
  -- Loop unrolling
  | loop_step {s : State} {cond body : CoreExpr} :
      Step s (.loop cond body) s
        (.matchTag cond 1 (.letBind 0 body (.loop cond body)) .unit)

theorem step_val_impossible {s s' : State} {e e' : CoreExpr}
    (h : Step s e s' e') (hVal : Value e) : False := by
  induction h with
  | pair_left _ _ => cases hVal; rename_i ha _; contradiction
  | pair_right _ _ _ => cases hVal; rename_i _ hb; contradiction
  | fst_eval _ _ => cases hVal
  | fst_val _ _ => cases hVal
  | snd_eval _ _ => cases hVal
  | snd_val _ _ => cases hVal
  | adt_eval _ _ _ => cases hVal; rename_i hp; contradiction
  | match_eval _ _ => cases hVal
  | match_hit _ _ => cases hVal
  | match_miss _ _ _ _ => cases hVal
  | match_bool_true => cases hVal
  | match_bool_false => cases hVal
  | let_eval _ _ _ => cases hVal
  | let_subst _ _ => cases hVal
  | app_fn _ _ => cases hVal
  | app_arg _ _ _ => cases hVal
  | app_beta _ _ _ _ _ => cases hVal
  | loop_step => cases hVal

theorem canonical_bool {v : CoreExpr} (hVal : Value v) {eff : Effect}
    (hTyped : WellTyped [] v .bool eff) :
    ∃ b : Bool, v = .bool b := by
  cases hVal with
  | bool b => exact ⟨b, rfl⟩
  | unit => cases hTyped
  | nat _ => cases hTyped
  | int _ _ _ => cases hTyped
  | lam _ _ _ _ => cases hTyped
  | pair _ _ => cases hTyped
  | adt _ _ => cases hTyped

theorem canonical_nat {v : CoreExpr} (hVal : Value v) {eff : Effect}
    (hTyped : WellTyped [] v .nat eff) :
    ∃ n : Nat, v = .nat n := by
  cases hVal with
  | nat n => exact ⟨n, rfl⟩
  | unit => cases hTyped
  | bool _ => cases hTyped
  | int _ _ _ => cases hTyped
  | lam _ _ _ _ => cases hTyped
  | pair _ _ => cases hTyped
  | adt _ _ => cases hTyped

theorem canonical_int {v : CoreExpr} (hVal : Value v) {s : Bool} {bits : Nat} {eff : Effect}
    (hTyped : WellTyped [] v (.int s bits) eff) :
    ∃ n : Int, v = .int s bits n := by
  cases hVal with
  | int s' bits' val =>
    cases hTyped with
    | int => exact ⟨val, rfl⟩
  | unit => cases hTyped
  | bool _ => cases hTyped
  | nat _ => cases hTyped
  | lam _ _ _ _ => cases hTyped
  | pair _ _ => cases hTyped
  | adt _ _ => cases hTyped

theorem canonical_prod {v : CoreExpr} (hVal : Value v) {tyA tyB : CoreType} {eff : Effect}
    (hTyped : WellTyped [] v (.prod tyA tyB) eff) :
    ∃ a b, v = .pair a b ∧ Value a ∧ Value b := by
  cases hVal with
  | pair va vb =>
    cases hTyped with
    | pair _ _ => exact ⟨_, _, rfl, va, vb⟩
  | unit => cases hTyped
  | bool _ => cases hTyped
  | nat _ => cases hTyped
  | int _ _ _ => cases hTyped
  | lam _ _ _ _ => cases hTyped
  | adt _ _ => cases hTyped

theorem canonical_adt {v : CoreExpr} (hVal : Value v) {tag : Nat} {tyP : CoreType} {eff : Effect}
    (hTyped : WellTyped [] v (.adt tag tyP) eff) :
    ∃ p, v = .adt tag p ∧ Value p := by
  cases hVal with
  | adt tag' vp =>
    cases hTyped with
    | adt => exact ⟨_, rfl, vp⟩
  | unit => cases hTyped
  | bool _ => cases hTyped
  | nat _ => cases hTyped
  | int _ _ _ => cases hTyped
  | lam _ _ _ _ => cases hTyped
  | pair _ _ => cases hTyped

theorem canonical_arrow {v : CoreExpr} (hVal : Value v) {dom cod : CoreType} {effBody : Effect} {eff : Effect}
    (hTyped : WellTyped [] v (.arrow dom cod effBody) eff) :
    ∃ p ty body, v = .lam p ty body effBody := by
  cases hVal with
  | lam p t b eb =>
    cases hTyped with
    | lam => exact ⟨_, _, _, rfl⟩
  | unit => cases hTyped
  | bool _ => cases hTyped
  | nat _ => cases hTyped
  | int _ _ _ => cases hTyped
  | pair _ _ => cases hTyped
  | adt _ _ => cases hTyped

theorem Step.deterministic {s s1 s2 : State} {e e1 e2 : CoreExpr}
    (h1 : Step s e s1 e1) (h2 : Step s e s2 e2) : s1 = s2 ∧ e1 = e2 := by
  induction h1 generalizing s2 e2 with
  | pair_left hrec ih =>
    cases h2 with
    | pair_left hrec2 =>
      have ⟨hs, he⟩ := ih hrec2
      subst hs he
      exact ⟨rfl, rfl⟩
    | pair_right hva hrec2 =>
      have := step_val_impossible hrec hva
      contradiction
  | pair_right hva hrec ih =>
    cases h2 with
    | pair_left hrec2 =>
      have := step_val_impossible hrec2 hva
      contradiction
    | pair_right _ hrec2 =>
      have ⟨hs, he⟩ := ih hrec2
      subst hs he
      exact ⟨rfl, rfl⟩
  | fst_eval hrec ih =>
    cases h2 with
    | fst_eval hrec2 =>
      have ⟨hs, he⟩ := ih hrec2
      subst hs he
      exact ⟨rfl, rfl⟩
    | fst_val hva hvb =>
      have := step_val_impossible hrec (.pair hva hvb)
      contradiction
  | fst_val hva hvb =>
    cases h2 with
    | fst_eval hrec2 =>
      have := step_val_impossible hrec2 (.pair hva hvb)
      contradiction
    | fst_val _ _ =>
      exact ⟨rfl, rfl⟩
  | snd_eval hrec ih =>
    cases h2 with
    | snd_eval hrec2 =>
      have ⟨hs, he⟩ := ih hrec2
      subst hs he
      exact ⟨rfl, rfl⟩
    | snd_val hva hvb =>
      have := step_val_impossible hrec (.pair hva hvb)
      contradiction
  | snd_val hva hvb =>
    cases h2 with
    | snd_eval hrec2 =>
      have := step_val_impossible hrec2 (.pair hva hvb)
      contradiction
    | snd_val _ _ =>
      exact ⟨rfl, rfl⟩
  | adt_eval tag hrec ih =>
    cases h2 with
    | adt_eval _ hrec2 =>
      have ⟨hs, he⟩ := ih hrec2
      subst hs he
      exact ⟨rfl, rfl⟩
  | match_eval tag hrec ih =>
    cases h2 with
    | match_eval _ hrec2 =>
      have ⟨hs, he⟩ := ih hrec2
      subst hs he
      exact ⟨rfl, rfl⟩
    | match_hit _ hv =>
      have := step_val_impossible hrec (.adt tag hv)
      contradiction
    | match_miss _ _ hne hv =>
      have := step_val_impossible hrec (.adt _ hv)
      contradiction
    | match_bool_true =>
      have := step_val_impossible hrec (.bool true)
      contradiction
    | match_bool_false =>
      have := step_val_impossible hrec (.bool false)
      contradiction
  | match_hit tag hv =>
    cases h2 with
    | match_eval _ hrec2 =>
      have := step_val_impossible hrec2 (.adt tag hv)
      contradiction
    | match_hit => exact ⟨rfl, rfl⟩
    | match_miss _ _ hne _ => contradiction
  | match_miss tag1 tag2 hne hv =>
    cases h2 with
    | match_eval _ hrec2 =>
      have := step_val_impossible hrec2 (.adt tag1 hv)
      contradiction
    | match_hit => contradiction
    | match_miss => exact ⟨rfl, rfl⟩
  | match_bool_true =>
    cases h2 with
    | match_eval _ hrec2 =>
      have := step_val_impossible hrec2 (.bool true)
      contradiction
    | match_bool_true => exact ⟨rfl, rfl⟩
  | match_bool_false =>
    cases h2 with
    | match_eval _ hrec2 =>
      have := step_val_impossible hrec2 (.bool false)
      contradiction
    | match_bool_false => exact ⟨rfl, rfl⟩
  | let_eval id hrec ih =>
    cases h2 with
    | let_eval _ hrec2 =>
      have ⟨hs, he⟩ := ih hrec2
      subst hs he
      exact ⟨rfl, rfl⟩
    | let_subst _ hv =>
      have := step_val_impossible hrec hv
      contradiction
  | let_subst id hv =>
    cases h2 with
    | let_eval _ hrec2 =>
      have := step_val_impossible hrec2 hv
      contradiction
    | let_subst => exact ⟨rfl, rfl⟩
  | app_fn hrec ih =>
    cases h2 with
    | app_fn hrec2 =>
      have ⟨hs, he⟩ := ih hrec2
      subst hs he
      exact ⟨rfl, rfl⟩
    | app_arg hfn _ =>
      have := step_val_impossible hrec hfn
      contradiction
    | app_beta p ty body eff _ =>
      have := step_val_impossible hrec (.lam p ty body eff)
      contradiction
  | app_arg hfn hrec ih =>
    cases h2 with
    | app_fn hrec2 =>
      have := step_val_impossible hrec2 hfn
      contradiction
    | app_arg _ hrec2 =>
      have ⟨hs, he⟩ := ih hrec2
      subst hs he
      exact ⟨rfl, rfl⟩
    | app_beta _ _ _ _ hv =>
      have := step_val_impossible hrec hv
      contradiction
  | app_beta p ty body eff hv =>
    cases h2 with
    | app_fn hrec2 =>
      have := step_val_impossible hrec2 (.lam p ty body eff)
      contradiction
    | app_arg _ hrec2 =>
      have := step_val_impossible hrec2 hv
      contradiction
    | app_beta => exact ⟨rfl, rfl⟩
  | loop_step =>
    cases h2 with
    | loop_step => exact ⟨rfl, rfl⟩

end Aethel.CoreSemantics
