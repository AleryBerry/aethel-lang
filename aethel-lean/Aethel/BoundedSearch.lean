namespace Aethel.Search

/-- A single probe either finds an answer, exhausts the search space,
or supplies the next search state. -/
inductive Probe (State Answer : Type) where
  | found (answer : Answer)
  | finished
  | advance (next : State)
  deriving Repr, DecidableEq

inductive Outcome (State Answer : Type) where
  | found (answer : Answer)
  | finished
  | pending (next : State)
  deriving Repr, DecidableEq

/-- At most one probe is called per unit of budget. The probe itself is total
in this model. Integration with the language must enforce that requirement. -/
def run (probe : State → Probe State Answer) :
    Nat → State → Outcome State Answer
  | 0, state => .pending state
  | budget + 1, state =>
    match probe state with
    | .found answer => .found answer
    | .finished => .finished
    | .advance next => run probe budget next

/-- Declarative rules for budget consumption and explicit outcomes. -/
inductive Runs (probe : State → Probe State Answer) :
    Nat → State → Outcome State Answer → Prop where
  | pause : Runs probe 0 state (.pending state)
  | found : probe state = .found answer → Runs probe (budget + 1) state (.found answer)
  | finished : probe state = .finished → Runs probe (budget + 1) state .finished
  | advance : probe state = .advance next → Runs probe budget next outcome →
      Runs probe (budget + 1) state outcome

theorem run_sound (probe : State → Probe State Answer) (budget : Nat) (state : State) :
    Runs probe budget state (run probe budget state) := by
  induction budget generalizing state with
  | zero => exact .pause
  | succ budget ih =>
    cases h : probe state <;> simp only [run, h]
    · exact .found h
    · exact .finished h
    · exact .advance h (ih _)

theorem Runs.agrees {probe : State → Probe State Answer}
    (trace : Runs probe budget state outcome) : run probe budget state = outcome := by
  induction trace <;> simp_all [run]

theorem run_resume {probe : State → Probe State Answer} {budget : Nat} {initial next : State}
    (paused : run probe budget initial = .pending next) (additional : Nat) :
    run probe (additional + budget) initial = run probe additional next := by
  induction budget generalizing initial with
  | zero => simpa [run] using congrArg (fun o => match o with
      | .pending s => run probe additional s
      | other => other) paused
  | succ budget ih =>
    cases h : probe initial <;> simp only [run, h] at paused ⊢
    · cases paused
    · cases paused
    · exact ih paused

end Aethel.Search
