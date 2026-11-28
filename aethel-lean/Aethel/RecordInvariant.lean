import Aethel.SourceVerification

namespace Aethel.RecordInvariant

abbrev Record := List (String × UInt8)
abbrev Law := String × String × String

def Holds (row : Record) (law : Law) : Prop :=
  ∃ value, row.lookup law.2.1 = some value ∧ row.lookup law.2.2 = some value

private def equalFields (row : Record) (law : Law) : Bool :=
  match row.lookup law.2.1, row.lookup law.2.2 with
  | some x, some y => x == y
  | _, _ => false

theorem equalFields_sound (row : Record) (law : Law) (h : equalFields row law = true) :
    Holds row law := by
  unfold equalFields at h
  split at h
  next x y hx hy => exact ⟨x, hx, by simpa [beq_iff_eq.mp h] using hy⟩
  next => contradiction

inductive Expr where
  | literal (value : UInt8)
  | field (name : String)
  | localVar (name : String)
  | sub (left right : Expr)

def Expr.eval (row locals : Record) : Expr → Except String UInt8
  | .literal n => .ok n
  | .field name => (row.lookup name).elim (.error s!"unknown field {name}") .ok
  | .localVar name => (locals.lookup name).elim (.error s!"unknown local {name}") .ok
  | .sub a b => do return UInt8.ofNat ((← a.eval row locals).toNat - (← b.eval row locals).toNat)

inductive Op where
  | bind (name : String) (value : Expr)
  | write (field : String) (value : Expr)
  | replace (fields : List (String × Expr))

private def complete (names fields : List String) : Bool :=
  names.length == fields.length && names.all fields.contains && fields.all names.contains &&
    fields.eraseDups.length == fields.length

/-- Source evaluation emits a record observation at each completed mutation.
Replacement evaluates every initializer in the preceding environment. -/
def run (row locals : Record) : List Op → Except String (List Record)
  | [] => .ok []
  | .bind name e :: rest => do
    let value ← e.eval row locals
    run row ((name,value)::locals) rest
  | .write field e :: rest => do
    unless (row.lookup field).isSome do throw s!"unknown field {field}"
    let value ← e.eval row locals
    let next := row.map fun (k,v) => (k, if k == field then value else v)
    return next :: (← run next locals rest)
  | .replace fields :: rest => do
    unless complete (row.map Prod.fst) (fields.map Prod.fst) do throw "invalid replacement fields"
    let next ← fields.mapM fun (k,e) => do return (k, ← e.eval row locals)
    return next :: (← run next locals rest)

def checkTrace (laws : List Law) (trace : List Record) : Bool :=
  trace.all fun row => laws.all (equalFields row)

theorem accepted_observations (initial : Record) (ops : List Op) (laws : List Law)
    (observations : List Record) (_execution : run initial [] ops = .ok observations)
    (accepted : checkTrace laws (initial :: observations) = true) :
    ∀ row ∈ initial :: observations, ∀ law ∈ laws, Holds row law := by
  intro row hr law hl
  exact equalFields_sound _ _ (List.all_eq_true.mp (List.all_eq_true.mp accepted row hr) law hl)

private abbrev Tokens := List String

private def atom (root : String) : Tokens → Except String (Expr × Tokens)
  | name :: "." :: field :: rest =>
    if name == root then .ok (.field field, rest) else .error s!"unknown record {name}"
  | name :: rest =>
    let number := (name.dropSuffix "u8").toString.toNat?
    match number with
    | some n => if n < 256 then .ok (.literal n.toUInt8, rest) else .error "byte out of range"
    | none => .ok (.localVar name, rest)
  | [] => .error "expected byte expression"

private def expression (root : String) (ts : Tokens) : Except String (Expr × Tokens) := do
  let (a, rest) ← atom root ts
  if let "-|" :: tail := rest then
    let (b, remaining) ← atom root tail
    return (.sub a b, remaining)
  return (a, rest)

private def entries (root : String) : Nat → Tokens → Except String (List (String × Expr) × Tokens)
  | _, "}" :: rest => .ok ([], rest)
  | fuel+1, name :: ":" :: rest => do
    let (value, tail) ← expression root rest
    match tail with
    | "}" :: after => return ([(name,value)], after)
    | "," :: after =>
      let (fields, after) ← entries root fuel after
      return ((name,value)::fields, after)
    | _ => throw "expected comma or }"
  | _, _ => .error "invalid record initializer"

private def schema : Nat → Tokens → Except String (List String × Tokens)
  | _, "}" :: rest => .ok ([], rest)
  | fuel+1, name :: ":" :: "u8" :: "," :: rest => do
    let (fields, tail) ← schema fuel rest
    return (name::fields, tail)
  | _, name :: ":" :: "u8" :: "}" :: rest => .ok ([name], rest)
  | _, _ => .error "expected a direct u8 field"

private def operations (record root : String) : Nat → Tokens → Except String (List Op)
  | _, ["}"] => .ok []
  | _, [";", "}"] => .ok []
  | fuel+1, ";" :: rest => operations record root fuel rest
  | fuel+1, "let" :: name :: "=" :: rest => do
    if name == root then throw "record shadowing unsupported"
    let (e, tail) ← expression root rest
    return .bind name e :: (← operations record root fuel tail)
  | fuel+1, target :: "." :: field :: "=" :: rest => do
    unless target == root do throw "UNPROVED unknown mutation target"
    let (e, tail) ← expression root rest
    return .write field e :: (← operations record root fuel tail)
  | fuel+1, target :: "=" :: ty :: "{" :: rest => do
    unless target == root && ty == record do throw "UNPROVED unknown replacement"
    let (fields, tail) ← entries root rest.length rest
    return .replace fields :: (← operations record root fuel tail)
  | _, _ => .error "UNPROVED unsupported operation in invariant program"

def parseStraightLine (source record : String) (laws : List Law) : Except String (Record × List Op) := do
  let "type" :: ty :: "{" :: ts := SourceVerification.tokens source | throw "expected type"
  unless ty == record do throw s!"unknown record {record}"
  let (names, ts) ← schema ts.length ts
  unless names.eraseDups == names do throw "duplicate field"
  for law in laws do
    unless names.contains law.2.1 && names.contains law.2.2 do throw s!"unknown field in {law.1}"
  let "fn" :: "main" :: "(" :: ")" :: "{" :: "let" :: "mut" :: root :: "=" :: ctor :: "{" :: ts := ts
    | throw "UNPROVED expected sequential record main"
  unless ctor == record do throw "wrong constructor"
  let (fields, rest) ← entries root ts.length ts
  unless complete names (fields.map Prod.fst) do throw "invalid constructor fields"
  let initial ← fields.mapM fun (k,e) => do return (k, ← e.eval [] [])
  let ops ← operations record root rest.length rest
  return (initial, ops)

private def violation (laws : List Law) (trace : List Record) : String := Id.run do
  let mut previous : Option Record := none
  for row in trace do
    for law in laws do
      unless equalFields row law do
        return s!"FALSIFIED {law.1}: {repr previous} -> {repr row}"
    previous := some row
  return "invariant violated"

open Core Structured Functional SourceVerification

/-- Observe live fields after construction and at each step of a checked byte body.
The relational specification quantifies over prefixes of its machine execution. -/
def observe (names : List String) (state : State) : Option Record :=
  names.zipIdx.mapM fun (name,i) => do return (name, ← state.byte ⟨0,i⟩)

private def checkAt (names : List String) (laws : List Law) (state : State) : Except String Unit := do
  let some row := observe names state | throw "UNPROVED missing live record field"
  unless laws.all (equalFields row) do throw (violation laws [row])

def checkSteps (names : List String) (laws : List Law) (state : State) :
    Program → Except String Unit
  | [] => checkAt names laws state
  | i :: tail => do
    checkAt names laws state
    let some next := Core.execute state i | throw "UNPROVED invalid machine step"
    checkSteps names laws next tail

theorem checked_prefix (names : List String) (laws : List Law)
    {state after : State} {before : Program} (ran : Runs state before after) (rest : Program)
    (accepted : checkSteps names laws state (before ++ rest) = .ok ()) :
    checkAt names laws after = .ok () := by
  induction ran with
  | nil =>
    cases rest with
    | nil => exact accepted
    | cons i tail =>
      cases h : checkAt names laws _ <;> simp_all [checkSteps, Bind.bind, Except.bind]
  | @cons start _ _ _ _ step _ ih =>
    apply ih
    cases h : checkAt names laws start <;>
      simp_all [checkSteps, Bind.bind, Except.bind, execute_complete step]

private def checkBody (names : List String) (laws : List Law)
    (values : List UInt8) (ops : Operations) : Except String Unit := do
  let some state := Core.run {} (byteRegionEntry 0 values) | throw "UNPROVED initialization"
  let code := ops.toCode 0 (fun _ => .finish) []
  let some (steps, _) := runCode Env.empty state code | throw "UNPROVED resource conflict"
  checkSteps names laws state steps

/-- Independent meaning of a checked sequential byte body. Every relational
execution prefix after construction observes a complete, valid record. -/
def BodyPreserves (names : List String) (laws : List Law) (values : List UInt8) (ops : Operations) : Prop :=
  ∀ {entered before after rest final}, Core.run {} (byteRegionEntry 0 values) = some entered →
    Executes Env.empty entered (ops.toCode 0 (fun _ => .finish) []) (before ++ rest) final →
    Runs entered before after → ∃ row, observe names after = some row ∧ ∀ l ∈ laws, Holds row l

theorem checkBody_sound {names laws values ops} (h : checkBody names laws values ops = .ok ()) :
    BodyPreserves names laws values ops := by
  intro entered before after rest final entry exec ran
  have checked : checkSteps names laws entered (before ++ rest) = .ok () := by
    simpa [checkBody, entry, exec.agrees] using h
  have ok := checked_prefix names laws ran rest checked
  cases obs : observe names after with
  | none => simp [checkAt, obs] at ok
  | some row =>
    refine ⟨row, rfl, ?_⟩
    cases good : laws.all (equalFields row) with
    | false => simp [checkAt, obs, good] at ok
    | true => exact fun l hl => equalFields_sound _ _ (List.all_eq_true.mp good l hl)

private def checkEach (f : α → Except String Unit) : List α → Except String Unit
  | [] => .ok ()
  | a :: rest => do f a; checkEach f rest

private theorem checkEach_sound {f : α → Except String Unit} {xs : List α}
    (h : checkEach f xs = .ok ()) : ∀ x ∈ xs, f x = .ok () := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    cases hy : f y with
    | error e => simp [checkEach, hy, Bind.bind, Except.bind] at h
    | ok u =>
      have tail : checkEach f ys = .ok () := by simpa [checkEach, hy, Bind.bind, Except.bind] using h
      simpa [hy] using And.intro hy (ih tail)

/-- All byte inputs for an exported helper. Never promote a sample or a run
above the checker budget to an unconditional preservation claim. -/
private def checkInputs (k : List UInt8 → Except String Unit) : Nat → Except String Unit
  | 0 => k []
  | n+1 => checkEach (fun b => checkInputs (fun bs => k (b.toUInt8::bs)) n) (List.range 256)

private theorem checkInputs_sound (xs : List UInt8) (k : List UInt8 → Except String Unit)
    (h : checkInputs k xs.length = .ok ()) : k xs = .ok () := by
  induction xs generalizing k with
  | nil => exact h
  | cons x xs ih =>
    have one := checkEach_sound h x.toNat (List.mem_range.mpr x.toNat_lt)
    exact ih (fun bs => k (x::bs)) (by simpa using one)

private def checkHelper (names : List String) (laws : List Law) (helper : FunctionMIR) : Except String Unit :=
  if names.length ≤ 2 then
    checkInputs (fun bytes =>
      if laws.all (equalFields (names.zip bytes)) then checkBody names laws bytes helper.body else .ok ()) names.length
  else .error s!"UNPROVED {helper.name}: exhaustive input budget exceeded"

def HelperPreserves (names : List String) (laws : List Law) (helper : FunctionMIR) : Prop :=
  ∀ xs : List UInt8, xs.length = names.length →
    (∀ l ∈ laws, Holds (names.zip xs) l) → BodyPreserves names laws xs helper.body

private theorem checkHelper_sound {names laws helper} (h : checkHelper names laws helper = .ok ()) :
    HelperPreserves names laws helper := by
  intro xs len valid
  unfold checkHelper at h
  split at h
  next =>
    rw [← len] at h
    have input := checkInputs_sound xs _ h
    have holds : laws.all (equalFields (names.zip xs)) = true := by
      apply List.all_eq_true.mpr
      intro l hl
      obtain ⟨v, hx, hy⟩ := valid l hl
      simp [equalFields, hx, hy]
    have checked : checkBody names laws xs helper.body = .ok () := by simpa [holds] using input
    exact fun _ _ _ _ _ ready executed steps => checkBody_sound checked ready executed steps
  next => contradiction

private def preflight {source : String} (program : Verified source) (record : String)
    (laws : List Law) : Except String Unit := do
  let mir := program.mir
  unless mir.record == record do throw s!"unknown invariant type {record}"
  let names := mir.fields.map Prod.fst
  for law in laws do
    unless names.contains law.2.1 && names.contains law.2.2 do throw s!"unknown field in {law.1}"
  if (SourceVerification.tokens source).contains "fork" then
    throw "UNPROVED concurrent mutation under a record invariant"

def checkReference {source : String} (program : Verified source)
    (record : String) (laws : List Law) : Except String Unit := do
  let mir := program.mir
  let names := mir.fields.map Prod.fst
  preflight program record laws
  checkBody names laws (mir.fields.map Prod.snd) mir.body
  checkEach (checkHelper names laws) mir.functions

def checkProgram (source record : String) (laws : List Law) : Except String Unit :=
  match SourceVerification.verify source with
  | .ok program => checkReference program record laws
  | .error _ => do
    let (initial, ops) ← parseStraightLine source record laws
    let trace := initial :: (← run initial [] ops)
    if checkTrace laws trace then return () else throw (violation laws trace)

/-- The two restricted grammars expose their semantic evidence separately.
The byte reference path also certifies each helper for every valid input. -/
def ProgramPreserves (source record : String) (laws : List Law) : Prop :=
  match SourceVerification.verify source with
  | .ok program =>
    let mir := program.mir
    let names := mir.fields.map Prod.fst
    BodyPreserves names laws (mir.fields.map Prod.snd) mir.body ∧
      ∀ helper ∈ mir.functions, HelperPreserves names laws helper
  | .error _ => ∃ initial ops observations,
    parseStraightLine source record laws = .ok (initial, ops) ∧ run initial [] ops = .ok observations ∧
    ∀ row ∈ initial :: observations, ∀ l ∈ laws, Holds row l

theorem checkProgram_sound {source record laws} (accepted : checkProgram source record laws = .ok ()) :
    ProgramPreserves source record laws := by
  cases src : SourceVerification.verify source with
  | ok program =>
    simp only [checkProgram, src, checkReference, Bind.bind, Except.bind] at accepted
    simp only [ProgramPreserves, src]
    cases pf : preflight program record laws <;> simp [pf] at accepted
    cases body : checkBody (program.mir.fields.map Prod.fst) laws (program.mir.fields.map Prod.snd) program.mir.body <;> simp [body] at accepted
    exact ⟨checkBody_sound body, fun f hf => checkHelper_sound (checkEach_sound accepted f hf)⟩
  | error reason =>
    simp only [ProgramPreserves, src, checkProgram, Bind.bind, Except.bind] at *
    cases parse : parseStraightLine source record laws <;> simp [parse] at accepted
    rename_i pair
    obtain ⟨initial, ops⟩ := pair
    cases exec : run initial [] ops <;> simp [exec] at accepted
    rename_i observations
    cases good : checkTrace laws (initial::observations) <;> simp [good] at accepted
    exact ⟨initial, ops, observations, rfl, exec, accepted_observations _ _ _ _ exec good⟩

end Aethel.RecordInvariant
