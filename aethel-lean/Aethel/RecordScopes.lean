import Aethel.StructuredRecords

namespace Aethel.Structured.Records

open Core Functional AutomaticLayout

/-- An individual leaf access operation that can be clustered during scope coalescing. -/
inductive AccessOp where
  | load (path : List Nat)
  | store (path : List Nat) (value : Raw)
  deriving Repr

def AccessOp.path : AccessOp → List Nat
  | .load p | .store p _ => p

def AccessOp.mode : AccessOp → AccessMode
  | .load _ => .shared
  | .store _ _ => .exclusive

def wrapOp (op : AccessOp) (k : RawRecordCode) : RawRecordCode :=
  match op with
  | .load p => .load p k
  | .store p v => .store p v k

def buildBlock (ops : List AccessOp) (tail : RawRecordCode) : RawRecordCode :=
  ops.foldr wrapOp tail

def combineModes (ops : List AccessOp) : AccessMode :=
  if ops.any (fun op => decide (op.mode = .exclusive)) then .exclusive else .shared

/-- The longest common prefix of two logical record paths. -/
def commonPrefix : List Nat → List Nat → List Nat
  | x :: xs, y :: ys => if x = y then x :: commonPrefix xs ys else []
  | _, _ => []

theorem commonPrefix_isPrefix_left (p1 p2 : List Nat) :
    (commonPrefix p1 p2).isPrefixOf p1 = true := by
  induction p1 generalizing p2 with
  | nil => simp [commonPrefix]
  | cons x xs ih =>
    cases p2 with
    | nil => simp [commonPrefix]
    | cons y ys =>
      simp only [commonPrefix]
      split
      · rename_i hxy
        simp only [List.isPrefixOf]
        simp [hxy, ih]
      · simp [List.isPrefixOf]

theorem commonPrefix_isPrefix_right (p1 p2 : List Nat) :
    (commonPrefix p1 p2).isPrefixOf p2 = true := by
  induction p1 generalizing p2 with
  | nil => simp [commonPrefix]
  | cons x xs ih =>
    cases p2 with
    | nil => simp [commonPrefix]
    | cons y ys =>
      simp only [commonPrefix]
      split
      · rename_i hxy
        simp only [List.isPrefixOf]
        simp [hxy, ih]
      · simp [List.isPrefixOf]

/-- Collect the longest contiguous prefix of leaf access operations whose
target paths are within `root`. -/
def collectOps (root : List Nat) : RawRecordCode → List AccessOp × RawRecordCode
  | .load p body =>
    if root.isPrefixOf p then
      let (ops, rest) := collectOps root body
      (.load p :: ops, rest)
    else ([], .load p body)
  | .store p v next =>
    if root.isPrefixOf p then
      let (ops, rest) := collectOps root next
      (.store p v :: ops, rest)
    else ([], .store p v next)
  | other => ([], other)

theorem collectOps_sizeOf_le (root : List Nat) (code : RawRecordCode) :
    sizeOf (collectOps root code).2 ≤ sizeOf code := by
  induction code with
  | finish => simp [collectOps]
  | letValue v body ih => simp [collectOps]
  | branch c yes no ihy ihn => simp [collectOps]
  | withView p m body next ihb ihn => simp [collectOps]
  | load p body ih =>
    simp only [collectOps]
    split
    · dsimp only [Prod.snd]
      have : sizeOf body < sizeOf (RawRecordCode.load p body) := by
        dsimp [sizeOf, RawRecordCode._sizeOf_inst, RawRecordCode._sizeOf_1]; omega
      omega
    · simp
  | store p v next ih =>
    simp only [collectOps]
    split
    · dsimp only [Prod.snd]
      have : sizeOf next < sizeOf (RawRecordCode.store p v next) := by
        dsimp [sizeOf, RawRecordCode._sizeOf_inst, RawRecordCode._sizeOf_1]; omega
      omega
    · simp

theorem collectOps_sizeOf_lt {root : List Nat} {code : RawRecordCode} {op : AccessOp} {ops : List AccessOp}
    {rest : RawRecordCode} (h : collectOps root code = (op :: ops, rest)) :
    sizeOf rest < sizeOf code := by
  induction code with
  | finish => simp [collectOps] at h
  | letValue _ _ => simp [collectOps] at h
  | branch _ _ _ => simp [collectOps] at h
  | withView _ _ _ _ => simp [collectOps] at h
  | load p body ih =>
    simp only [collectOps] at h
    split at h
    · rename_i pfx
      have eq : rest = (collectOps root body).2 := by
        have := congrArg Prod.snd h
        dsimp at this
        exact this.symm
      have le := collectOps_sizeOf_le root body
      have : sizeOf body < sizeOf (RawRecordCode.load p body) := by
        dsimp [sizeOf, RawRecordCode._sizeOf_inst, RawRecordCode._sizeOf_1]; omega
      rw [eq]
      omega
    · simp at h
  | store p v next ih =>
    simp only [collectOps] at h
    split at h
    · rename_i pfx
      have eq : rest = (collectOps root next).2 := by
        have := congrArg Prod.snd h
        dsimp at this
        exact this.symm
      have le := collectOps_sizeOf_le root next
      have : sizeOf next < sizeOf (RawRecordCode.store p v next) := by
        dsimp [sizeOf, RawRecordCode._sizeOf_inst, RawRecordCode._sizeOf_1]; omega
      rw [eq]
      omega
    · simp at h

/-- Splice a continuation onto the straight-line completion of a record code fragment. -/
def splice : RawRecordCode → RawRecordCode → RawRecordCode
  | .finish, second => second
  | .letValue v body, second => .letValue v (splice body second)
  | .load p body, second => .load p (splice body second)
  | .store p v next, second => .store p v (splice next second)
  | .branch c yes no, second => .branch c (splice yes second) (splice no second)
  | .withView p m body next, second => .withView p m body (splice next second)

theorem splice_finish (code : RawRecordCode) : splice code .finish = code := by
  induction code with
  | finish => rfl
  | letValue _ body ih => simp [splice, ih]
  | load _ body ih => simp [splice, ih]
  | store _ _ next ih => simp [splice, ih]
  | branch _ yes no ihy ihn => simp [splice, ihy, ihn]
  | withView _ _ body next _ ihn => simp [splice, ihn]

theorem splice_assoc (a b c : RawRecordCode) :
    splice (splice a b) c = splice a (splice b c) := by
  induction a with
  | finish => rfl
  | letValue _ body ih => simp [splice, ih]
  | load _ body ih => simp [splice, ih]
  | store _ _ next ih => simp [splice, ih]
  | branch _ yes no ihy ihn => simp [splice, ihy, ihn]
  | withView _ _ body next _ ihn => simp [splice, ihn]

/-- Syntactic predicate checking whether any operation in `code` accesses
`root` or any subfield or ancestor of `root`. -/
def usesPath (root : List Nat) : RawRecordCode → Bool
  | .finish => false
  | .letValue _ body => usesPath root body
  | .load path body => root.isPrefixOf path || path.isPrefixOf root || usesPath root body
  | .store path _ next => root.isPrefixOf path || path.isPrefixOf root || usesPath root next
  | .branch _ yes no => usesPath root yes || usesPath root no
  | .withView path _ body next =>
    root.isPrefixOf path || path.isPrefixOf root || usesPath root body || usesPath root next

/-- Partition a code block into a prefix ending at the last use of `root`, and a
suffix containing instructions that execute strictly after `root` is dead. -/
def partitionLastUse (root : List Nat) : RawRecordCode → RawRecordCode × RawRecordCode
  | .finish => (.finish, .finish)
  | .letValue v body =>
    if usesPath root body then
      let (pre, suf) := partitionLastUse root body
      (.letValue v pre, suf)
    else (.finish, .letValue v body)
  | .load path body =>
    if ¬ (root.isPrefixOf path || path.isPrefixOf root || usesPath root body) then
      (.finish, .load path body)
    else if usesPath root body then
      let (pre, suf) := partitionLastUse root body
      (.load path pre, suf)
    else
      (.load path .finish, body)
  | .store path v next =>
    if ¬ (root.isPrefixOf path || path.isPrefixOf root || usesPath root next) then
      (.finish, .store path v next)
    else if usesPath root next then
      let (pre, suf) := partitionLastUse root next
      (.store path v pre, suf)
    else
      (.store path v .finish, next)
  | .branch c yes no =>
    if usesPath root yes || usesPath root no then
      (.branch c yes no, .finish)
    else
      (.finish, .branch c yes no)
  | .withView p m body next =>
    if ¬ (root.isPrefixOf p || p.isPrefixOf root || usesPath root body || usesPath root next) then
      (.finish, .withView p m body next)
    else if usesPath root next then
      let (pre, suf) := partitionLastUse root next
      (.withView p m body pre, suf)
    else
      (.withView p m body .finish, next)

theorem partitionLastUse_splice (root : List Nat) (code : RawRecordCode) :
    splice (partitionLastUse root code).1 (partitionLastUse root code).2 = code := by
  induction code with
  | finish => rfl
  | letValue v body ih =>
    simp only [partitionLastUse]
    split
    · dsimp only
      rw [splice, ih]
    · simp [splice]
  | load path body ih =>
    simp only [partitionLastUse]
    split
    · simp [splice]
    · split
      · dsimp only
        rw [splice, ih]
      · simp [splice]
  | store path v next ih =>
    simp only [partitionLastUse]
    split
    · simp [splice]
    · split
      · dsimp only
        rw [splice, ih]
      · simp [splice]
  | branch c yes no _ _ =>
    simp only [partitionLastUse]
    split
    · simp [splice_finish]
    · simp [splice]
  | withView p m body next _ ihn =>
    simp only [partitionLastUse]
    split
    · simp [splice]
    · split
      · dsimp only
        rw [splice, ihn]
      · simp [splice]

theorem partitionLastUse_suffix_dead (root : List Nat) (code : RawRecordCode) :
    usesPath root (partitionLastUse root code).2 = false := by
  induction code with
  | finish => rfl
  | letValue v body ih =>
    simp only [partitionLastUse]
    split
    · exact ih
    · simp only [usesPath]
      rename_i h
      simp only [Bool.not_eq_true] at h
      exact h
  | load path body ih =>
    simp only [partitionLastUse]
    split
    · rename_i h
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at h
      simp only [usesPath, h.1.1, h.1.2, h.2, Bool.false_or]
    · split
      · exact ih
      · rename_i _ h
        simp only [Bool.not_eq_true] at h
        exact h
  | store path v next ih =>
    simp only [partitionLastUse]
    split
    · rename_i h
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at h
      simp only [usesPath, h.1.1, h.1.2, h.2, Bool.false_or]
    · split
      · exact ih
      · rename_i _ h
        simp only [Bool.not_eq_true] at h
        exact h
  | branch c yes no _ _ =>
    simp only [partitionLastUse]
    split
    · rfl
    · rename_i h
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at h
      simp only [usesPath, h.1, h.2, Bool.or_self]
  | withView p m body next _ ihn =>
    simp only [partitionLastUse]
    split
    · rename_i h
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at h
      simp only [usesPath, h.1.1.1, h.1.1.2, h.1.2, h.2, Bool.false_or]
    · split
      · exact ihn
      · rename_i _ h
        simp only [Bool.not_eq_true] at h
        exact h

/-- Independent mathematical specification: `(prefixCode, suffixCode)` exactly
reconstitutes `body` via `splice`, and `root` is never referenced in `suffixCode`. -/
def IsPrefixSplit (root : List Nat) (body : RawRecordCode)
    (prefixCode suffixCode : RawRecordCode) : Prop :=
  splice prefixCode suffixCode = body ∧ usesPath root suffixCode = false

theorem partitionLastUse_sound (root : List Nat) (body : RawRecordCode) :
    IsPrefixSplit root body (partitionLastUse root body).1 (partitionLastUse root body).2 :=
  ⟨partitionLastUse_splice root body, partitionLastUse_suffix_dead root body⟩

/-- Shrink a view's syntactic scope to end at its last use within the body.
Operations following the last use run outside the view with parent authority. -/
def shrinkToLastUse (path : List Nat) (mode : AccessMode) (body next : RawRecordCode) : RawRecordCode :=
  let (prefixCode, suffixCode) := partitionLastUse path body
  match prefixCode with
  | .finish => splice suffixCode next
  | _ => .withView path mode prefixCode (splice suffixCode next)

private def nextPath : RawRecordCode → Option (List Nat)
  | .load p _ => some p
  | .store p _ _ => some p
  | _ => none

/-- Automatically infer enclosing views for contiguous sequences of subpath
operations and shrink existing and coalesced views to their last use. -/
def coalesceScopes (code : RawRecordCode) : RawRecordCode :=
  match code with
  | .finish => .finish
  | .letValue v body => .letValue v (coalesceScopes body)
  | .branch c yes no => .branch c (coalesceScopes yes) (coalesceScopes no)
  | .withView p m body next =>
    shrinkToLastUse p m (coalesceScopes body) (coalesceScopes next)
  | .load p body =>
    match nextPath body with
    | some p2 =>
      let root := commonPrefix p p2
      if root ≠ [] then
        match h : collectOps root (RawRecordCode.load p body) with
        | (op1 :: op2 :: restOps, rest) =>
          have _hlt : sizeOf rest < sizeOf (RawRecordCode.load p body) := collectOps_sizeOf_lt h
          .withView root (combineModes (op1 :: op2 :: restOps))
            (buildBlock (op1 :: op2 :: restOps) .finish) (coalesceScopes rest)
        | _ => .load p (coalesceScopes body)
      else .load p (coalesceScopes body)
    | none => .load p (coalesceScopes body)
  | .store p v next =>
    match nextPath next with
    | some p2 =>
      let root := commonPrefix p p2
      if root ≠ [] then
        match h : collectOps root (RawRecordCode.store p v next) with
        | (op1 :: op2 :: restOps, rest) =>
          have _hlt : sizeOf rest < sizeOf (RawRecordCode.store p v next) := collectOps_sizeOf_lt h
          .withView root (combineModes (op1 :: op2 :: restOps))
            (buildBlock (op1 :: op2 :: restOps) .finish) (coalesceScopes rest)
        | _ => .store p v (coalesceScopes next)
      else .store p v (coalesceScopes next)
    | none => .store p v (coalesceScopes next)
termination_by sizeOf code
decreasing_by
  all_goals
    dsimp [sizeOf, RawRecordCode._sizeOf_inst, RawRecordCode._sizeOf_1] at *
    omega

/-- Execute a record source program after inferring minimal coalesced scopes and
ending views at their last use. -/
def executeWithScopes {abi : TargetIntegerABI} {schema : Schema}
    (record : RecordRef abi schema) (state : State) (source : RawRecordCode) :
    Except RecordError (List IntegerBits × State) :=
  executeRecord record state (coalesceScopes source)

theorem executeWithScopes_restores_scopes {abi : TargetIntegerABI} {schema : Schema}
    {record : RecordRef abi schema} {state final : State}
    {source : RawRecordCode} {observations : List IntegerBits}
    (executed : executeWithScopes record state source = .ok (observations, final)) :
    final.handles = state.handles ∧ final.views = state.views :=
  executeRecord_restores_scopes executed

/-- Independent declarative relation specifying valid scope coalescing and last-use transformations. -/
inductive Coalesces : RawRecordCode → RawRecordCode → Prop where
  | finish : Coalesces .finish .finish
  | letValue (v : Raw) {body body' : RawRecordCode} :
      Coalesces body body' → Coalesces (.letValue v body) (.letValue v body')
  | branch (c : Raw) {yes yes' no no' : RawRecordCode} :
      Coalesces yes yes' → Coalesces no no' →
      Coalesces (.branch c yes no) (.branch c yes' no')
  | withView (p : List Nat) (m : AccessMode) {body body' next next' : RawRecordCode} :
      Coalesces body body' → Coalesces next next' →
      Coalesces (.withView p m body next) (shrinkToLastUse p m body' next')
  | load (p : List Nat) {body body' : RawRecordCode} :
      Coalesces body body' → Coalesces (.load p body) (.load p body')
  | store (p : List Nat) (v : Raw) {next next' : RawRecordCode} :
      Coalesces next next' → Coalesces (.store p v next) (.store p v next')
  | clusterLoad (p : List Nat) {body rest rest' : RawRecordCode} {ops : List AccessOp} (root : List Nat) :
      collectOps root (RawRecordCode.load p body) = (ops, rest) →
      Coalesces rest rest' →
      Coalesces (RawRecordCode.load p body)
        (.withView root (combineModes ops) (buildBlock ops .finish) rest')
  | clusterStore (p : List Nat) (v : Raw) {next rest rest' : RawRecordCode} {ops : List AccessOp} (root : List Nat) :
      collectOps root (RawRecordCode.store p v next) = (ops, rest) →
      Coalesces rest rest' →
      Coalesces (RawRecordCode.store p v next)
        (.withView root (combineModes ops) (buildBlock ops .finish) rest')

theorem coalesceScopes_sound (code : RawRecordCode) : Coalesces code (coalesceScopes code) := by
  have h (n : Nat) (c : RawRecordCode) (hn : sizeOf c ≤ n) : Coalesces c (coalesceScopes c) := by
    induction n generalizing c with
    | zero =>
      have : sizeOf c > 0 := by cases c <;> dsimp [sizeOf, RawRecordCode._sizeOf_inst, RawRecordCode._sizeOf_1] <;> omega
      omega
    | succ n ih =>
      cases c with
      | finish =>
        simp [coalesceScopes]
        exact .finish
      | letValue v body =>
        have lt : sizeOf body ≤ n := by
          have : sizeOf body < sizeOf (RawRecordCode.letValue v body) := by
            dsimp [sizeOf, RawRecordCode._sizeOf_inst, RawRecordCode._sizeOf_1]; omega
          omega
        have ihb := ih body lt
        rw [coalesceScopes]
        exact .letValue v ihb
      | branch c yes no =>
        have lty : sizeOf yes ≤ n := by
          have : sizeOf yes < sizeOf (RawRecordCode.branch c yes no) := by
            dsimp [sizeOf, RawRecordCode._sizeOf_inst, RawRecordCode._sizeOf_1]; omega
          omega
        have ltn : sizeOf no ≤ n := by
          have : sizeOf no < sizeOf (RawRecordCode.branch c yes no) := by
            dsimp [sizeOf, RawRecordCode._sizeOf_inst, RawRecordCode._sizeOf_1]; omega
          omega
        have ihy := ih yes lty
        have ihn := ih no ltn
        rw [coalesceScopes]
        exact .branch c ihy ihn
      | withView p m body next =>
        have ltb : sizeOf body ≤ n := by
          have : sizeOf body < sizeOf (RawRecordCode.withView p m body next) := by
            dsimp [sizeOf, RawRecordCode._sizeOf_inst, RawRecordCode._sizeOf_1]; omega
          omega
        have ltn : sizeOf next ≤ n := by
          have : sizeOf next < sizeOf (RawRecordCode.withView p m body next) := by
            dsimp [sizeOf, RawRecordCode._sizeOf_inst, RawRecordCode._sizeOf_1]; omega
          omega
        have ihb := ih body ltb
        have ihn := ih next ltn
        rw [coalesceScopes]
        exact .withView p m ihb ihn
      | load p body =>
        have ltb : sizeOf body ≤ n := by
          have : sizeOf body < sizeOf (RawRecordCode.load p body) := by
            dsimp [sizeOf, RawRecordCode._sizeOf_inst, RawRecordCode._sizeOf_1]; omega
          omega
        have ihb := ih body ltb
        rw [coalesceScopes]
        dsimp only
        split
        · split
          · rename_i p2 _ hroot
            split
            · rename_i ops rest hops
              have hlt : sizeOf rest < sizeOf (RawRecordCode.load p body) := collectOps_sizeOf_lt hops
              have ltr : sizeOf rest ≤ n := by omega
              exact .clusterLoad p (commonPrefix p p2) hops (ih rest ltr)
            · exact .load p ihb
          · exact .load p ihb
        · exact .load p ihb
      | store p v next =>
        have ltn : sizeOf next ≤ n := by
          have : sizeOf next < sizeOf (RawRecordCode.store p v next) := by
            dsimp [sizeOf, RawRecordCode._sizeOf_inst, RawRecordCode._sizeOf_1]; omega
          omega
        have ihn := ih next ltn
        rw [coalesceScopes]
        dsimp only
        split
        · split
          · rename_i p2 _ hroot
            split
            · rename_i ops rest hops
              have hlt : sizeOf rest < sizeOf (RawRecordCode.store p v next) := collectOps_sizeOf_lt hops
              have ltr : sizeOf rest ≤ n := by omega
              exact .clusterStore p v (commonPrefix p p2) hops (ih rest ltr)
            · exact .store p v ihn
          · exact .store p v ihn
        · exact .store p v ihn
  exact h (sizeOf code) code (Nat.le_refl _)

end Aethel.Structured.Records
