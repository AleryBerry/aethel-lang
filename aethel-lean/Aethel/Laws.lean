import Aethel.Functions

namespace Aethel.Functional

/-- A universally quantified equality between expressions in a shared context.
Both sides elaborate with the same checker used for ordinary expressions. -/
structure EqualityLaw where
  context : List Ty
  result : Ty
  left : Raw
  right : Raw

structure CheckedEquality (law : EqualityLaw) where
  left : Term law.context law.result
  right : Term law.context law.result
  leftSource : left.erase = law.left
  rightSource : right.erase = law.right

private theorem erase_cast {ctx : List Ty} {actual expected : Ty}
    (same : actual = expected) (term : Term ctx actual) :
    Term.erase (same ▸ term : Term ctx expected) = term.erase := by
  cases same
  rfl

def EqualityLaw.check (law : EqualityLaw) : Except TypeError (CheckedEquality law) := do
  let ⟨leftTy, left, leftSource⟩ ← elaborate law.context law.left
  let ⟨rightTy, right, rightSource⟩ ← elaborate law.context law.right
  if leftMatches : leftTy = law.result then
    if rightMatches : rightTy = law.result then
      return ⟨leftMatches ▸ left, rightMatches ▸ right,
        (erase_cast leftMatches left).trans leftSource,
        (erase_cast rightMatches right).trans rightSource⟩
    else .error (.expected law.result rightTy)
  else .error (.expected law.result leftTy)

def EqualityLaw.Holds (law : EqualityLaw) : Prop :=
  match law.check with
  | .error _ => False
  | .ok checked => ∀ env, checked.left.eval env = checked.right.eval env

theorem EqualityLaw.sound {law : EqualityLaw} {checked : CheckedEquality law}
    (elaborated : law.check = .ok checked) (proof : law.Holds)
    {env : Env law.context} {a b : law.result.Value}
    (left : Evaluates env checked.left a) (right : Evaluates env checked.right b) :
    a = b := by
  exact left.agrees.symm.trans ((show ∀ env, checked.left.eval env = checked.right.eval env by
    simpa [EqualityLaw.Holds, elaborated] using proof) env |>.trans right.agrees)

def statusRoundTrip (decode : Raw → Raw) : EqualityLaw :=
  ⟨[.status], .option .status, decode (.encodeStatus (.var 0)), .some (.var 0)⟩

theorem status_round_trip_law : (statusRoundTrip .decodeStatus).Holds := by
  change ∀ env : Env [.status], Status.decode (Status.encode (env.get .here)) = some (env.get .here)
  exact fun env => Status.decode_encode (env.get .here)

theorem status_round_trip_rejects_constant_decoder :
    ¬ (statusRoundTrip (fun _ => .some (.status .idle))).Holds := by
  intro proof
  exact (by decide : some Status.idle ≠ some Status.dead) (proof (Env.empty.extend Status.dead))

/-- The object-language map is assembled from option matching and application. -/
def optionMap (input output : Ty) : Term [] (.arrow (.arrow input output)
    (.arrow (.option input) (.option output))) :=
  .lam (.lam (.optionCase (.var .here) .none
    (.some (.app (.var (.there (.there .here))) (.var .here)))))

theorem option_map_identity (ty : Ty) (value : Option ty.Value) :
    (optionMap ty ty).eval Env.empty id value = value := by
  cases value <;> rfl

theorem option_map_composition (a b c : Ty) (f : a.Value → b.Value) (g : b.Value → c.Value)
    (value : Option a.Value) :
    (optionMap a c).eval Env.empty (g ∘ f) value =
      (optionMap b c).eval Env.empty g ((optionMap a b).eval Env.empty f value) := by
  cases value <;> rfl

/-- Composition in the object language, with the outer function passed first. -/
def compose (a b c : Ty) :
    Term [] (.arrow (.arrow b c) (.arrow (.arrow a b) (.arrow a c))) :=
  .lam (.lam (.lam
    (.app (.var (.there (.there .here))) (.app (.var (.there .here)) (.var .here)))))

theorem compose_identity (a b : Ty) (f : a.Value → b.Value) :
    (compose a b b).eval Env.empty id f = f ∧
    (compose a a b).eval Env.empty f id = f :=
  ⟨rfl, rfl⟩

theorem compose_associative (a b c d : Ty)
    (f : a.Value → b.Value) (g : b.Value → c.Value) (h : c.Value → d.Value) :
    (compose a c d).eval Env.empty h ((compose a b c).eval Env.empty g f) =
      (compose a b d).eval Env.empty ((compose b c d).eval Env.empty h g) f :=
  rfl

end Aethel.Functional
