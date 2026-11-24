import Aethel.CategoricalCombinators

namespace Aethel.CategoricalTraits

open Aethel.CategoricalCombinators

/-!
## Law-Verified Categorical Traits, Open-Universe Instances, & Structural Lifting

Formalizes Aethel's `trait` / `[default] instance` / `with` / `using` type system:
1. Categorical trait hierarchy (`SemigroupTrait`, `MonoidTrait`, `FunctorTrait`,
   `ApplicativeTrait`, `MonadTrait`, `CategoryTrait`) with forgetful-functor
   law preservation (`MonadTrait.toApplicativeTrait`, `MonadTrait.toFunctorTrait`).
2. Open-universe `InstanceRegistry` supporting multiple named instances on the same
   carrier type (`sum_u32` vs `max_u32`), unambiguous default resolution with
   independent `UniqueDefault` specification, `using` overrides, and `InstanceId`-branded
   container coherence (`BrandedContainer`).
3. Polynomial structural lifting (`PolyData`) demonstrating zero-allocation `using`
   overrides inside nested types like `Bar (List (Qux (Nat × Foo)))` without `newtype`.
-/

/-! ### Part A: Categorical Trait Hierarchy & Forgetful Functors -/

structure SemigroupTrait (α : Type) where
  combine : α → α → α
  assoc : ∀ x y z : α, combine (combine x y) z = combine x (combine y z)

structure MonoidTrait (α : Type) extends SemigroupTrait α where
  empty : α
  left_id : ∀ x : α, combine empty x = x
  right_id : ∀ x : α, combine x empty = x

theorem MonoidTrait.toSemigroup_assoc {α : Type} (m : MonoidTrait α) (x y z : α) :
    m.combine (m.combine x y) z = m.combine x (m.combine y z) :=
  m.assoc x y z

structure FunctorTrait (F : Type → Type) where
  map : {α β : Type} → (α → β) → F α → F β
  map_id : ∀ {α : Type} (x : F α), map id x = x
  map_comp : ∀ {α β γ : Type} (f : α → β) (g : β → γ) (x : F α),
    map (g ∘ f) x = map g (map f x)

structure ApplicativeTrait (F : Type → Type) extends FunctorTrait F where
  pure : {α : Type} → α → F α
  ap : {α β : Type} → F (α → β) → F α → F β
  ap_id : ∀ {α : Type} (v : F α), ap (pure id) v = v
  ap_homomorphism : ∀ {α β : Type} (f : α → β) (x : α),
    ap (pure f) (pure x) = pure (f x)
  ap_interchange : ∀ {α β : Type} (u : F (α → β)) (y : α),
    ap u (pure y) = ap (pure (fun f => f y)) u
  map_eq_ap_pure : ∀ {α β : Type} (f : α → β) (x : F α),
    map f x = ap (pure f) x

structure MonadTrait (F : Type → Type) where
  pure : {α : Type} → α → F α
  andThen : {α β : Type} → F α → (α → F β) → F β
  left_id : ∀ {α β : Type} (a : α) (k : α → F β), andThen (pure a) k = k a
  right_id : ∀ {α : Type} (m : F α), andThen m pure = m
  assoc : ∀ {α β γ : Type} (m : F α) (f : α → F β) (g : β → F γ),
    andThen (andThen m f) g = andThen m (fun x => andThen (f x) g)

def MonadTrait.derivedMap {F : Type → Type} (m : MonadTrait F)
    {α β : Type} (f : α → β) (x : F α) : F β :=
  m.andThen x (fun a => m.pure (f a))

def MonadTrait.derivedAp {F : Type → Type} (m : MonadTrait F)
    {α β : Type} (ff : F (α → β)) (fa : F α) : F β :=
  m.andThen ff (fun f => m.andThen fa (fun a => m.pure (f a)))

theorem MonadTrait.derivedMap_id {F : Type → Type} (m : MonadTrait F)
    {α : Type} (x : F α) :
    m.derivedMap id x = x := by
  dsimp [MonadTrait.derivedMap, id]
  exact m.right_id x

theorem MonadTrait.derivedMap_comp {F : Type → Type} (m : MonadTrait F)
    {α β γ : Type} (f : α → β) (g : β → γ) (x : F α) :
    m.derivedMap (g ∘ f) x = m.derivedMap g (m.derivedMap f x) := by
  dsimp [MonadTrait.derivedMap, Function.comp]
  rw [m.assoc]
  congr 1
  funext a
  rw [m.left_id]

theorem MonadTrait.derivedAp_id {F : Type → Type} (m : MonadTrait F)
    {α : Type} (v : F α) :
    m.derivedAp (m.pure id) v = v := by
  dsimp [MonadTrait.derivedAp]
  rw [m.left_id]
  simp only [id]
  exact m.right_id v

theorem MonadTrait.derivedAp_homomorphism {F : Type → Type} (m : MonadTrait F)
    {α β : Type} (f : α → β) (x : α) :
    m.derivedAp (m.pure f) (m.pure x) = m.pure (f x) := by
  dsimp [MonadTrait.derivedAp]
  rw [m.left_id, m.left_id]

theorem MonadTrait.derivedAp_interchange {F : Type → Type} (m : MonadTrait F)
    {α β : Type} (u : F (α → β)) (y : α) :
    m.derivedAp u (m.pure y) = m.derivedAp (m.pure (fun f => f y)) u := by
  dsimp [MonadTrait.derivedAp]
  rw [m.left_id]
  congr 1
  funext f
  rw [m.left_id]

theorem MonadTrait.derivedMap_eq_ap_pure {F : Type → Type} (m : MonadTrait F)
    {α β : Type} (f : α → β) (x : F α) :
    m.derivedMap f x = m.derivedAp (m.pure f) x := by
  dsimp [MonadTrait.derivedMap, MonadTrait.derivedAp]
  rw [m.left_id]

/-- Forgetful functor synthesizing a law-verified `FunctorTrait` from any lawful `MonadTrait`. -/
def MonadTrait.toFunctorTrait {F : Type → Type} (m : MonadTrait F) : FunctorTrait F where
  map := m.derivedMap
  map_id := m.derivedMap_id
  map_comp := m.derivedMap_comp

/-- Forgetful functor synthesizing a law-verified `ApplicativeTrait` from any lawful `MonadTrait`. -/
def MonadTrait.toApplicativeTrait {F : Type → Type} (m : MonadTrait F) : ApplicativeTrait F where
  map := m.derivedMap
  map_id := m.derivedMap_id
  map_comp := m.derivedMap_comp
  pure := m.pure
  ap := m.derivedAp
  ap_id := m.derivedAp_id
  ap_homomorphism := m.derivedAp_homomorphism
  ap_interchange := m.derivedAp_interchange
  map_eq_ap_pure := m.derivedMap_eq_ap_pure

structure CategoryTrait (Hom : Type → Type → Type) where
  idHom : {α : Type} → Hom α α
  compHom : {α β γ : Type} → Hom α β → Hom β γ → Hom α γ
  id_left : ∀ {α β : Type} (f : Hom α β), compHom idHom f = f
  id_right : ∀ {α β : Type} (f : Hom α β), compHom f idHom = f
  comp_assoc : ∀ {α β γ δ : Type} (f : Hom α β) (g : Hom β γ) (h : Hom γ δ),
    compHom (compHom f g) h = compHom f (compHom g h)

/-! ### Concrete Verified Categorical Instances -/

def natAddMonoid : MonoidTrait Nat where
  combine := (· + ·)
  assoc := Nat.add_assoc
  empty := 0
  left_id := Nat.zero_add
  right_id := Nat.add_zero

def natMaxMonoid : MonoidTrait Nat where
  combine := max
  assoc := Nat.max_assoc
  empty := 0
  left_id := Nat.zero_max
  right_id := Nat.max_zero

def satAddU32Bound : Nat := 2 ^ 32 - 1

def satAdd (bound x y : Nat) : Nat := min (x + y) bound

theorem satAdd_assoc (bound x y z : Nat) :
    satAdd bound (satAdd bound x y) z = satAdd bound x (satAdd bound y z) := by
  dsimp [satAdd]
  omega

def satAddU32Monoid : MonoidTrait { n : Nat // n ≤ satAddU32Bound } where
  combine a b := ⟨satAdd satAddU32Bound a.1 b.1, Nat.min_le_right _ _⟩
  assoc a b c := by
    apply Subtype.ext
    exact satAdd_assoc satAddU32Bound a.1 b.1 c.1
  empty := ⟨0, Nat.zero_le _⟩
  left_id a := by
    apply Subtype.ext
    dsimp [satAdd]
    have ha := a.2
    omega
  right_id a := by
    apply Subtype.ext
    dsimp [satAdd]
    have ha := a.2
    omega

def optionMonadTrait : MonadTrait Option where
  pure := Option.some
  andThen := optAndThen
  left_id := optAndThen_left_id
  right_id := optAndThen_right_id
  assoc := optAndThen_assoc

def resultMonadTrait (ε : Type) : MonadTrait (Except ε) where
  pure := Except.ok
  andThen := resAndThen
  left_id := resAndThen_left_id
  right_id := resAndThen_right_id
  assoc := resAndThen_assoc

def fnCategory : CategoryTrait (fun α β => α → β) where
  idHom := fun a => a
  compHom f g := fun a => g (f a)
  id_left _ := rfl
  id_right _ := rfl
  comp_assoc _ _ _ := rfl

def kleisliResultCategory (ε : Type) : CategoryTrait (fun α β => α → Except ε β) where
  idHom := Except.ok
  compHom := kleisliCompose
  id_left := kleisli_left_id
  id_right := kleisli_right_id
  comp_assoc := kleisli_assoc

/-! ### Part B: Open-Universe `InstanceRegistry`, `using`, and Branded Coherence -/

abbrev InstanceId := Nat
abbrev TraitId := Nat
abbrev TypeKey := Nat

structure InstanceEntry where
  instId : InstanceId
  traitId : TraitId
  typeKey : TypeKey
  moduleId : Nat
  isDefault : Bool
  deriving Repr, DecidableEq

abbrev InstanceRegistry := List InstanceEntry

/-- Independent relational specification of an unambiguous `default instance`
lookup for `(tr, ty)`. -/
def UniqueDefault (reg : InstanceRegistry) (tr : TraitId) (ty : TypeKey)
    (out : InstanceEntry) : Prop :=
  out ∈ reg ∧ out.traitId = tr ∧ out.typeKey = ty ∧ out.isDefault = true ∧
  ∀ other ∈ reg, other.traitId = tr → other.typeKey = ty → other.isDefault = true → other = out

def resolveDefault (reg : InstanceRegistry) (tr : TraitId) (ty : TypeKey) : Option InstanceEntry :=
  match reg.filter (fun e => decide (e.traitId = tr ∧ e.typeKey = ty ∧ e.isDefault = true)) with
  | [e] => some e
  | _ => none

theorem resolveDefault_sound {reg : InstanceRegistry} {tr : TraitId} {ty : TypeKey}
    {out : InstanceEntry} (hRes : resolveDefault reg tr ty = some out) :
    UniqueDefault reg tr ty out := by
  dsimp [resolveDefault, UniqueDefault] at *
  generalize hFilt : reg.filter (fun e => decide (e.traitId = tr ∧ e.typeKey = ty ∧ e.isDefault = true)) = xs at hRes
  cases xs with
  | nil => cases hRes
  | cons a rest =>
    cases rest with
    | nil =>
      cases hRes
      have hMemPred := List.mem_filter.mp (hFilt ▸ List.mem_cons_self)
      have hPred : out.traitId = tr ∧ out.typeKey = ty ∧ out.isDefault = true :=
        of_decide_eq_true hMemPred.2
      refine ⟨hMemPred.1, hPred.1, hPred.2.1, hPred.2.2, ?_⟩
      intro other ho hTr hTy hDef
      have hoFilt : other ∈ [out] := by
        rw [← hFilt]
        exact List.mem_filter.mpr ⟨ho, decide_eq_true ⟨hTr, hTy, hDef⟩⟩
      simpa using hoFilt
    | cons b _ => cases hRes

theorem resolveDefault_complete {reg : InstanceRegistry} (hNodup : reg.Nodup)
    {tr : TraitId} {ty : TypeKey} {out : InstanceEntry}
    (hUniq : UniqueDefault reg tr ty out) :
    resolveDefault reg tr ty = some out := by
  dsimp [resolveDefault]
  obtain ⟨hMem, hTr, hTy, hDef, hAll⟩ := hUniq
  have hFiltNodup :
      (reg.filter (fun e => decide (e.traitId = tr ∧ e.typeKey = ty ∧ e.isDefault = true))).Nodup :=
    hNodup.filter _
  generalize hFilt : reg.filter (fun e => decide (e.traitId = tr ∧ e.typeKey = ty ∧ e.isDefault = true)) = xs at hFiltNodup ⊢
  have hInXs : out ∈ xs := by
    rw [← hFilt]
    exact List.mem_filter.mpr ⟨hMem, decide_eq_true ⟨hTr, hTy, hDef⟩⟩
  have hEqOut : ∀ y ∈ xs, y = out := by
    intro y hy
    have hyFilt := List.mem_filter.mp (hFilt ▸ hy)
    have hyPred : y.traitId = tr ∧ y.typeKey = ty ∧ y.isDefault = true :=
      of_decide_eq_true hyFilt.2
    exact hAll y hyFilt.1 hyPred.1 hyPred.2.1 hyPred.2.2
  cases xs with
  | nil => cases hInXs
  | cons a rest =>
    cases rest with
    | nil =>
      have ha : a = out := hEqOut a List.mem_cons_self
      rw [ha]
    | cons b _ =>
      have ha : a = out := hEqOut a List.mem_cons_self
      have hb : b = out := hEqOut b (List.mem_cons_of_mem _ List.mem_cons_self)
      have hHead := (List.nodup_cons.mp hFiltNodup).1
      have hAB : a = b := ha.trans hb.symm
      exact False.elim (hHead (hAB ▸ List.mem_cons_self))

theorem resolveDefault_correct {reg : InstanceRegistry} (hNodup : reg.Nodup)
    (tr : TraitId) (ty : TypeKey) (out : InstanceEntry) :
    resolveDefault reg tr ty = some out ↔ UniqueDefault reg tr ty out :=
  ⟨resolveDefault_sound, resolveDefault_complete hNodup⟩

theorem resolveDefault_ambiguous_none {reg : InstanceRegistry}
    {tr : TraitId} {ty : TypeKey} {e1 e2 : InstanceEntry}
    (h1 : e1 ∈ reg) (h1Tr : e1.traitId = tr) (h1Ty : e1.typeKey = ty) (h1Def : e1.isDefault = true)
    (h2 : e2 ∈ reg) (h2Tr : e2.traitId = tr) (h2Ty : e2.typeKey = ty) (h2Def : e2.isDefault = true)
    (hNe : e1 ≠ e2) :
    resolveDefault reg tr ty = none := by
  cases hRes : resolveDefault reg tr ty with
  | none => rfl
  | some out =>
    have hUniq := resolveDefault_sound hRes
    have he1 : e1 = out := hUniq.2.2.2.2 e1 h1 h1Tr h1Ty h1Def
    have he2 : e2 = out := hUniq.2.2.2.2 e2 h2 h2Tr h2Ty h2Def
    exact False.elim (hNe (he1.trans he2.symm))

/-- Resolves either a lexical `using` override (`overrideId = some id`) or the
unique `default instance` in scope. -/
def resolveWithUsing (reg : InstanceRegistry) (overrideId : Option InstanceId)
    (tr : TraitId) (ty : TypeKey) : Option InstanceEntry :=
  match overrideId with
  | some iid =>
    reg.find? fun e => decide (e.instId = iid ∧ e.traitId = tr ∧ e.typeKey = ty)
  | none => resolveDefault reg tr ty

def ResolvesWithUsing (reg : InstanceRegistry) (overrideId : Option InstanceId)
    (tr : TraitId) (ty : TypeKey) (out : InstanceEntry) : Prop :=
  match overrideId with
  | some iid => out ∈ reg ∧ out.instId = iid ∧ out.traitId = tr ∧ out.typeKey = ty
  | none => UniqueDefault reg tr ty out

theorem resolveWithUsing_sound {reg : InstanceRegistry} {overrideId : Option InstanceId}
    {tr : TraitId} {ty : TypeKey} {out : InstanceEntry}
    (hRes : resolveWithUsing reg overrideId tr ty = some out) :
    ResolvesWithUsing reg overrideId tr ty out := by
  cases overrideId with
  | none => exact resolveDefault_sound hRes
  | some iid =>
    dsimp [resolveWithUsing, ResolvesWithUsing] at *
    have hMem := List.mem_of_find?_eq_some hRes
    have hPred := of_decide_eq_true
      (List.find?_some (p := fun (e : InstanceEntry) => decide (e.instId = iid ∧ e.traitId = tr ∧ e.typeKey = ty)) hRes)
    exact ⟨hMem, hPred.1, hPred.2.1, hPred.2.2⟩

theorem openUniverse_coexistence_witness :
    let reg : InstanceRegistry :=
      [ ⟨1, 10, 100, 0, true⟩   -- sum_u32 (default Monoid(u32) in module 0)
      , ⟨2, 10, 100, 1, false⟩ ] -- max_u32 (named instance in downstream module 1)
    resolveWithUsing reg none 10 100 = some ⟨1, 10, 100, 0, true⟩ ∧
    resolveWithUsing reg (some 2) 10 100 = some ⟨2, 10, 100, 1, false⟩ := by
  decide

/-- Container indexed at the type level by the `InstanceId` used to maintain its
internal representation invariant (e.g. `OrderedSet(k @ M)`). -/
structure BrandedContainer (instId : InstanceId) (α : Type) where
  elems : List α
  deriving Repr, DecidableEq

def BrandedContainer.SameInst (i1 i2 : InstanceId) : Prop := i1 = i2

def checkBrandedSameInst (i1 i2 : InstanceId) : Bool := i1 == i2

theorem checkBrandedSameInst_correct (i1 i2 : InstanceId) :
    checkBrandedSameInst i1 i2 = true ↔ BrandedContainer.SameInst i1 i2 := by
  simp [checkBrandedSameInst, BrandedContainer.SameInst]

def mergeBranded {instId : InstanceId} {α : Type}
    (a b : BrandedContainer instId α) : BrandedContainer instId α :=
  ⟨a.elems ++ b.elems⟩

theorem cross_instance_container_rejected :
    checkBrandedSameInst 1 2 = false := rfl

/-! ### Part C: Polynomial Structural Lifting (`using` Without `newtype`) -/

/-- Algebraic polynomial AST representing nested user containers such as
`Bar (List (Qux (Nat × Foo)))`. -/
inductive PolyData (Leaf : Type) where
  | constNat (n : Nat) : PolyData Leaf
  | leaf (x : Leaf) : PolyData Leaf
  | pair (a b : PolyData Leaf) : PolyData Leaf
  | inl (a : PolyData Leaf) : PolyData Leaf
  | inr (b : PolyData Leaf) : PolyData Leaf
  | list (xs : List (PolyData Leaf)) : PolyData Leaf
  deriving Repr

def PolyData.map {A B : Type} (f : A → B) : PolyData A → PolyData B
  | .constNat n => .constNat n
  | .leaf x => .leaf (f x)
  | .pair a b => .pair (a.map f) (b.map f)
  | .inl a => .inl (a.map f)
  | .inr b => .inr (b.map f)
  | .list xs => .list (xs.map (PolyData.map f))

mutual
  theorem PolyData.map_id {A : Type} (d : PolyData A) :
      d.map id = d := by
    cases d with
    | constNat _ => simp [PolyData.map]
    | leaf _ => simp [PolyData.map]
    | pair a b => simp [PolyData.map, PolyData.map_id a, PolyData.map_id b]
    | inl a => simp [PolyData.map, PolyData.map_id a]
    | inr b => simp [PolyData.map, PolyData.map_id b]
    | list xs => simp [PolyData.map, polyList_map_id xs]

  private theorem polyList_map_id {A : Type} (xs : List (PolyData A)) :
      xs.map (PolyData.map id) = xs := by
    cases xs with
    | nil => rfl
    | cons x rest => simp [PolyData.map_id x, polyList_map_id rest]
end

def polyEncode {Leaf : Type} (encodeLeaf : Leaf → List Nat) : PolyData Leaf → List Nat
  | .constNat n => [n]
  | .leaf x => encodeLeaf x
  | .pair a b => polyEncode encodeLeaf a ++ polyEncode encodeLeaf b
  | .inl a => 0 :: polyEncode encodeLeaf a
  | .inr b => 1 :: polyEncode encodeLeaf b
  | .list xs => xs.length :: (xs.flatMap (polyEncode encodeLeaf))

def polyFold {Leaf M : Type} (mon : MonoidTrait M) (proj : Leaf → M) : PolyData Leaf → M
  | .constNat _ => mon.empty
  | .leaf x => proj x
  | .pair a b => mon.combine (polyFold mon proj a) (polyFold mon proj b)
  | .inl a => polyFold mon proj a
  | .inr b => polyFold mon proj b
  | .list xs => xs.foldl (fun acc el => mon.combine acc (polyFold mon proj el)) mon.empty

structure WrappedLeaf (α : Type) where
  unwrap : α
  deriving Repr, DecidableEq

/-! Proves that evaluating a structural `using` override directly on `PolyData Leaf`
agrees identically with wrapping every leaf inside a nested container via `newtype`
(`Bar (List (Qux (Nat × Foo)))`), while avoiding wrapper traversal & reallocation. -/
mutual
  theorem polyEncode_using_no_repack {A B : Type} (iso : A → B) (enc : B → List Nat)
      (d : PolyData A) :
      polyEncode (fun a => enc (iso a)) d = polyEncode enc (d.map iso) := by
    cases d with
    | constNat _ => simp [polyEncode, PolyData.map]
    | leaf _ => simp [polyEncode, PolyData.map]
    | pair a b =>
      simp [polyEncode, PolyData.map, polyEncode_using_no_repack iso enc a,
        polyEncode_using_no_repack iso enc b]
    | inl a => simp [polyEncode, PolyData.map, polyEncode_using_no_repack iso enc a]
    | inr b => simp [polyEncode, PolyData.map, polyEncode_using_no_repack iso enc b]
    | list xs =>
      simp only [polyEncode, PolyData.map, List.length_map]
      congr 1
      exact polyListEncode_using_no_repack iso enc xs

  private theorem polyListEncode_using_no_repack {A B : Type} (iso : A → B) (enc : B → List Nat)
      (xs : List (PolyData A)) :
      xs.flatMap (polyEncode (fun a => enc (iso a))) =
        (xs.map (PolyData.map iso)).flatMap (polyEncode enc) := by
    cases xs with
    | nil => rfl
    | cons x rest =>
      simp [List.flatMap_cons, polyEncode_using_no_repack iso enc x,
        polyListEncode_using_no_repack iso enc rest]
end

theorem nested_bar_qux_foo_override_no_repack {Leaf : Type}
    (compactFoo : Leaf → List Nat) (bar : PolyData Leaf) :
    polyEncode compactFoo bar =
      polyEncode (fun w : WrappedLeaf Leaf => compactFoo w.unwrap) (bar.map WrappedLeaf.mk) :=
  (polyEncode_using_no_repack WrappedLeaf.mk (fun w => compactFoo w.unwrap) bar)

/-! ### Part D: Negative Unlawful & Ambiguous Counterexamples -/

theorem badSubSemigroup_not_assoc :
    ¬ (∀ x y z : Nat, (x - y) - z = x - (y - z)) := by
  intro h
  have hEx := h 5 3 2
  omega

theorem badAddEmptyOne_not_left_id :
    ¬ (∀ x : Nat, 1 + x = x) := by
  intro h
  have hEx := h 0
  omega

theorem ambiguous_default_rejected :
    let reg : InstanceRegistry :=
      [ ⟨1, 10, 100, 1, true⟩
      , ⟨2, 10, 100, 2, true⟩ ]
    resolveDefault reg 10 100 = none := by
  decide

end Aethel.CategoricalTraits
