namespace Aethel

/-- Driver transition step boundary. A step may halt normally, continue to the next
state, or encounter a typed failure. -/
inductive DriverStep (S : Type) where
  | halt (finalState : S)
  | step (nextState : S)
  | fail (reason : String)
  deriving Repr, DecidableEq

/-- The outcome of running a bounded computation with fuel. -/
inductive DriverOutcome (S : Type) where
  | finished (finalState : S)
  | pending (remainingState : S)
  | error (reason : String)
  deriving Repr, DecidableEq

/-- Bounded execution driver running up to `fuel` steps. -/
def drive {S : Type} : Nat → (S → DriverStep S) → S → DriverOutcome S
  | 0, _, s => .pending s
  | fuel + 1, stepFn, s =>
    match stepFn s with
    | .halt s' => .finished s'
    | .step s' => drive fuel stepFn s'
    | .fail msg => .error msg

@[simp]
theorem drive_zero {S : Type} (stepFn : S → DriverStep S) (s : S) :
    drive 0 stepFn s = .pending s := rfl

theorem drive_halt {S : Type} (fuel : Nat) (stepFn : S → DriverStep S) (s s' : S)
    (h : stepFn s = .halt s') :
    drive (fuel + 1) stepFn s = .finished s' := by
  dsimp [drive]; rw [h]

theorem drive_fail {S : Type} (fuel : Nat) (stepFn : S → DriverStep S) (s : S) (msg : String)
    (h : stepFn s = .fail msg) :
    drive (fuel + 1) stepFn s = .error msg := by
  dsimp [drive]; rw [h]

theorem drive_step {S : Type} (fuel : Nat) (stepFn : S → DriverStep S) (s s' : S)
    (h : stepFn s = .step s') :
    drive (fuel + 1) stepFn s = drive fuel stepFn s' := by
  dsimp [drive]; rw [h]

/-- Step relation preserves invariant predicate `inv`. -/
def StepPreserves {S : Type} (inv : S → Prop) (stepFn : S → DriverStep S) : Prop :=
  ∀ s, inv s →
    match stepFn s with
    | .halt s' => inv s'
    | .step s' => inv s'
    | .fail _ => True

theorem drive_preserves_invariant {S : Type} (fuel : Nat) (stepFn : S → DriverStep S)
    (inv : S → Prop) (hstep : StepPreserves inv stepFn) (s : S) (hinv : inv s) :
    match drive fuel stepFn s with
    | .finished s' => inv s'
    | .pending s' => inv s'
    | .error _ => True := by
  induction fuel generalizing s with
  | zero =>
    simp only [drive_zero]
    exact hinv
  | succ n ih =>
    dsimp [drive]
    have hstep_s := hstep s hinv
    cases heq : stepFn s with
    | halt s' =>
      rw [heq] at hstep_s
      exact hstep_s
    | step s' =>
      rw [heq] at hstep_s
      exact ih s' hstep_s
    | fail msg =>
      trivial

theorem drive_pending_add {S : Type} (n : Nat) :
    ∀ (m : Nat) (stepFn : S → DriverStep S) (s sMid : S),
      drive n stepFn s = .pending sMid →
      drive (n + m) stepFn s = drive m stepFn sMid := by
  induction n with
  | zero =>
    intro m stepFn s sMid h
    simp only [drive_zero] at h
    cases h
    rw [Nat.zero_add]
  | succ n ih =>
    intro m stepFn s sMid h
    have h_nm : n + 1 + m = (n + m) + 1 := by omega
    rw [h_nm]
    dsimp [drive]
    cases heq : stepFn s with
    | halt s' =>
      dsimp [drive] at h; rw [heq] at h; cases h
    | step s' =>
      dsimp [drive] at h; rw [heq] at h
      exact ih m stepFn s' sMid h
    | fail msg =>
      dsimp [drive] at h; rw [heq] at h; cases h

/-- Relational specification of driver execution. -/
inductive ExecutesDriver {S : Type} : Nat → (S → DriverStep S) → S → DriverOutcome S → Prop where
  | zero (stepFn : S → DriverStep S) (s : S) :
      ExecutesDriver 0 stepFn s (.pending s)
  | halt (fuel : Nat) (stepFn : S → DriverStep S) (s s' : S) :
      stepFn s = .halt s' →
      ExecutesDriver (fuel + 1) stepFn s (.finished s')
  | fail (fuel : Nat) (stepFn : S → DriverStep S) (s : S) (msg : String) :
      stepFn s = .fail msg →
      ExecutesDriver (fuel + 1) stepFn s (.error msg)
  | step (fuel : Nat) (stepFn : S → DriverStep S) (s s' : S) (out : DriverOutcome S) :
      stepFn s = .step s' →
      ExecutesDriver fuel stepFn s' out →
      ExecutesDriver (fuel + 1) stepFn s out

theorem drive_agrees {S : Type} (fuel : Nat) (stepFn : S → DriverStep S) (s : S) :
    ExecutesDriver fuel stepFn s (drive fuel stepFn s) := by
  induction fuel generalizing s with
  | zero =>
    simp only [drive_zero]
    exact .zero stepFn s
  | succ n ih =>
    dsimp [drive]
    cases heq : stepFn s with
    | halt s' =>
      exact .halt n stepFn s s' heq
    | step s' =>
      exact .step n stepFn s s' (drive n stepFn s') heq (ih s')
    | fail msg =>
      exact .fail n stepFn s msg heq

theorem executes_deterministic {S : Type} {fuel : Nat} {stepFn : S → DriverStep S}
    {s : S} {out1 out2 : DriverOutcome S}
    (h1 : ExecutesDriver fuel stepFn s out1) (h2 : ExecutesDriver fuel stepFn s out2) :
    out1 = out2 := by
  induction h1 generalizing out2 with
  | zero =>
    cases h2
    rfl
  | halt fuel step s s' heq =>
    cases h2 with
    | halt _ _ _ _ heq2 =>
      rw [heq] at heq2
      injection heq2 with heq_s
      rw [heq_s]
    | fail _ _ _ _ heq2 =>
      rw [heq] at heq2; cases heq2
    | step _ _ _ _ _ heq2 _ =>
      rw [heq] at heq2; cases heq2
  | fail fuel step s msg heq =>
    cases h2 with
    | halt _ _ _ _ heq2 =>
      rw [heq] at heq2; cases heq2
    | fail _ _ _ _ heq2 =>
      rw [heq] at heq2
      injection heq2 with heq_m
      rw [heq_m]
    | step _ _ _ _ _ heq2 _ =>
      rw [heq] at heq2; cases heq2
  | step fuel step s s' out heq _hrec ih =>
    cases h2 with
    | halt _ _ _ _ heq2 =>
      rw [heq] at heq2; cases heq2
    | fail _ _ _ _ heq2 =>
      rw [heq] at heq2; cases heq2
    | step _ _ _ s'' _ heq2 hrec2 =>
      rw [heq] at heq2
      injection heq2 with heq_s'
      subst heq_s'
      exact ih hrec2

/-- Structured loop step generator from condition and body functions. -/
def loopStep {S : Type} (cond : S → Bool) (body : S → S) (s : S) : DriverStep S :=
  if cond s then .step (body s) else .halt s

theorem loopStep_halt {S : Type} (cond : S → Bool) (body : S → S) (s s' : S)
    (h : loopStep cond body s = .halt s') :
    s' = s ∧ cond s = false := by
  dsimp [loopStep] at h
  split at h
  · cases h
  · rename_i hcond
    simp only [Bool.not_eq_true] at hcond
    injection h with heq
    subst heq
    exact ⟨rfl, hcond⟩

theorem loopStep_preserves {S : Type} (cond : S → Bool) (body : S → S) (inv : S → Prop)
    (hBody : ∀ s, cond s = true → inv s → inv (body s)) :
    StepPreserves inv (loopStep cond body) := by
  intro s hinv
  dsimp [StepPreserves, loopStep]
  by_cases hc : cond s = true
  · simp [hc]
    exact hBody s hc hinv
  · have hf : cond s = false := by
      cases h : cond s <;> simp_all
    simp [hf, hinv]

theorem drive_loop_finished_exit {S : Type} (fuel : Nat) (cond : S → Bool) (body : S → S)
    (s s' : S) (h : drive fuel (loopStep cond body) s = .finished s') :
    cond s' = false := by
  induction fuel generalizing s with
  | zero => simp [drive_zero] at h
  | succ n ih =>
    dsimp [drive] at h
    cases heq : loopStep cond body s with
    | halt s0 =>
      have ⟨heq_s, hcond⟩ := loopStep_halt cond body s s0 heq
      rw [heq] at h
      injection h with h_fin
      subst h_fin heq_s
      exact hcond
    | step s0 =>
      rw [heq] at h
      exact ih s0 h
    | fail msg =>
      rw [heq] at h; cases h

theorem drive_loop_preserves_invariant {S : Type} (fuel : Nat) (cond : S → Bool)
    (body : S → S) (inv : S → Prop)
    (hBody : ∀ s, cond s = true → inv s → inv (body s)) (s : S) (hinv : inv s) :
    match drive fuel (loopStep cond body) s with
    | .finished s' => inv s' ∧ cond s' = false
    | .pending s' => inv s'
    | .error _ => True := by
  have hPres := drive_preserves_invariant fuel (loopStep cond body) inv (loopStep_preserves cond body inv hBody) s hinv
  cases hres : drive fuel (loopStep cond body) s with
  | finished s' =>
    rw [hres] at hPres
    have hexit := drive_loop_finished_exit fuel cond body s s' hres
    exact ⟨hPres, hexit⟩
  | pending s' =>
    rw [hres] at hPres
    exact hPres
  | error msg =>
    trivial

/-- Well-founded loop definition using a termination measure. -/
def loopWF {S : Type} (stepFn : S → S) (cond : S → Bool) (measure : S → Nat)
    (hProgress : ∀ s, cond s = true → measure (stepFn s) < measure s)
    (s : S) : S :=
  if h : cond s = true then
    have : measure (stepFn s) < measure s := hProgress s h
    loopWF stepFn cond measure hProgress (stepFn s)
  else
    s
termination_by measure s

theorem loopWF_stop {S : Type} (stepFn : S → S) (cond : S → Bool) (measure : S → Nat)
    (hProgress : ∀ s, cond s = true → measure (stepFn s) < measure s)
    (s : S) (h : cond s = false) :
    loopWF stepFn cond measure hProgress s = s := by
  rw [loopWF]
  have hne : ¬ (cond s = true) := by simp [h]
  simp [hne]

theorem loopWF_unroll {S : Type} (stepFn : S → S) (cond : S → Bool) (measure : S → Nat)
    (hProgress : ∀ s, cond s = true → measure (stepFn s) < measure s)
    (s : S) (h : cond s = true) :
    loopWF stepFn cond measure hProgress s = loopWF stepFn cond measure hProgress (stepFn s) := by
  conv =>
    lhs
    rw [loopWF]
  simp [h]

theorem loopWF_exit_cond {S : Type} (stepFn : S → S) (cond : S → Bool) (measure : S → Nat)
    (hProgress : ∀ s, cond s = true → measure (stepFn s) < measure s)
    (s : S) :
    cond (loopWF stepFn cond measure hProgress s) = false := by
  induction s using loopWF.induct stepFn cond measure hProgress with
  | case1 x hc _hlt ih =>
    rw [loopWF_unroll stepFn cond measure hProgress x hc]
    exact ih
  | case2 x _hnc =>
    have hf : cond x = false := by
      cases h : cond x <;> simp_all
    rw [loopWF_stop stepFn cond measure hProgress x hf]
    exact hf

theorem loopWF_preserves_invariant {S : Type} (stepFn : S → S) (cond : S → Bool)
    (measure : S → Nat) (hProgress : ∀ s, cond s = true → measure (stepFn s) < measure s)
    (inv : S → Prop) (hStep : ∀ s, cond s = true → inv s → inv (stepFn s))
    (s : S) (hinv : inv s) :
    inv (loopWF stepFn cond measure hProgress s) := by
  induction s using loopWF.induct stepFn cond measure hProgress with
  | case1 x hc _hlt ih =>
    rw [loopWF_unroll stepFn cond measure hProgress x hc]
    have hinv' := hStep x hc hinv
    exact ih hinv'
  | case2 x _hnc =>
    have hf : cond x = false := by
      cases h : cond x <;> simp_all
    rw [loopWF_stop stepFn cond measure hProgress x hf]
    exact hinv

theorem drive_loop_eq_loopWF {S : Type} (body : S → S) (cond : S → Bool)
    (measure : S → Nat) (hProgress : ∀ s, cond s = true → measure (body s) < measure s)
    (s : S) :
    ∀ (fuel : Nat), measure s < fuel →
      drive fuel (loopStep cond body) s = .finished (loopWF body cond measure hProgress s) := by
  induction s using loopWF.induct body cond measure hProgress with
  | case1 x hc _hlt ih =>
    intro fuel hfuel
    cases fuel with
    | zero => contradiction
    | succ k =>
      dsimp [drive]
      have hstep : loopStep cond body x = .step (body x) := by
        dsimp [loopStep]; simp [hc]
      rw [hstep]
      rw [loopWF_unroll body cond measure hProgress x hc]
      have hk : measure (body x) < k := by omega
      exact ih k hk
  | case2 x _hnc =>
    intro fuel _hfuel
    cases fuel with
    | zero => contradiction
    | succ k =>
      have hf : cond x = false := by
        cases h : cond x <;> simp_all
      dsimp [drive]
      have hstep : loopStep cond body x = .halt x := by
        dsimp [loopStep]; simp [hf]
      rw [hstep]
      rw [loopWF_stop body cond measure hProgress x hf]

end Aethel
