import Aethel.CategoricalFusion

namespace Aethel.CategoricalCombinators

open Aethel Aethel.Core Aethel.CacheLayout Aethel.CategoricalFusion

/-!
## Categorical Combinators & Checked Fallible In-Place Pipelines

Formalizes `Result` (`Except`) and `Option` Kleisli categories, natural
transformations between them, and checked fallible in-place collection pipelines
whose Kleisli composition fuses without intermediate states.
-/

def resMap {ε α β : Type} (f : α → β) : Except ε α → Except ε β
  | .ok a => .ok (f a)
  | .error e => .error e

def resAndThen {ε α β : Type} (r : Except ε α) (k : α → Except ε β) : Except ε β :=
  match r with
  | .ok a => k a
  | .error e => .error e

def kleisliCompose {ε α β γ : Type}
    (f : α → Except ε β) (g : β → Except ε γ) : α → Except ε γ :=
  fun x => resAndThen (f x) g

def optAndThen {α β : Type} (o : Option α) (k : α → Option β) : Option β :=
  match o with
  | .some a => k a
  | .none => .none

def optKleisli {α β γ : Type} (f : α → Option β) (g : β → Option γ) : α → Option γ :=
  fun x => optAndThen (f x) g

def optionToResult {ε α : Type} (err : ε) : Option α → Except ε α
  | .some a => .ok a
  | .none => .error err

theorem resMap_id {ε α : Type} (r : Except ε α) : resMap id r = r := by
  cases r <;> rfl

theorem resMap_comp {ε α β γ : Type} (f : α → β) (g : β → γ) (r : Except ε α) :
    resMap (g ∘ f) r = resMap g (resMap f r) := by
  cases r <;> rfl

theorem resAndThen_left_id {ε α β : Type} (a : α) (k : α → Except ε β) :
    resAndThen (.ok a) k = k a := rfl

theorem resAndThen_right_id {ε α : Type} (r : Except ε α) :
    resAndThen r Except.ok = r := by
  cases r <;> rfl

theorem resAndThen_assoc {ε α β γ : Type} (r : Except ε α)
    (f : α → Except ε β) (g : β → Except ε γ) :
    resAndThen (resAndThen r f) g = resAndThen r (fun x => resAndThen (f x) g) := by
  cases r <;> rfl

theorem kleisli_left_id {ε α β : Type} (f : α → Except ε β) :
    kleisliCompose Except.ok f = f := rfl

theorem kleisli_right_id {ε α β : Type} (f : α → Except ε β) :
    kleisliCompose f Except.ok = f := by
  funext x
  exact resAndThen_right_id (f x)

theorem kleisli_assoc {ε α β γ δ : Type}
    (f : α → Except ε β) (g : β → Except ε γ) (h : γ → Except ε δ) :
    kleisliCompose (kleisliCompose f g) h = kleisliCompose f (kleisliCompose g h) := by
  funext x
  exact resAndThen_assoc (f x) g h

theorem optAndThen_left_id {α β : Type} (a : α) (k : α → Option β) :
    optAndThen (.some a) k = k a := rfl

theorem optAndThen_right_id {α : Type} (o : Option α) :
    optAndThen o Option.some = o := by
  cases o <;> rfl

theorem optAndThen_assoc {α β γ : Type} (o : Option α)
    (f : α → Option β) (g : β → Option γ) :
    optAndThen (optAndThen o f) g = optAndThen o (fun x => optAndThen (f x) g) := by
  cases o <;> rfl

theorem optionToResult_natural {ε α β : Type} (err : ε) (f : α → β) (o : Option α) :
    resMap f (optionToResult err o) = optionToResult err (Option.map f o) := by
  cases o <;> rfl

def tryMapFieldStep {ε : Type} (owner : OwnerId) (layout : CollectionLayout)
    (length fieldCount field : Nat) (f : UInt8 → Except ε UInt8)
    (s : Core.State) (i : Nat) : Except ε Core.State :=
  let loc : ByteLocation := ⟨owner, collectionSlot layout length fieldCount i field⟩
  match s.byte loc with
  | some b =>
    match f b with
    | .ok b' => .ok (s.store loc b')
    | .error e => .error e
  | none => .ok s

def tryMapFieldLoop {ε : Type} (owner : OwnerId) (layout : CollectionLayout)
    (length fieldCount field : Nat) (f : UInt8 → Except ε UInt8)
    (s : Core.State) : Nat → Except ε Core.State
  | 0 => .ok s
  | n + 1 =>
    resAndThen (tryMapFieldLoop owner layout length fieldCount field f s n)
      (fun mid => tryMapFieldStep owner layout length fieldCount field f mid n)

def tryMapFieldInPlace {ε : Type} (owner : OwnerId) (layout : CollectionLayout)
    (length fieldCount field : Nat) (f : UInt8 → Except ε UInt8)
    (s : Core.State) : Except ε Core.State :=
  tryMapFieldLoop owner layout length fieldCount field f s length

private theorem tryMapFieldLoop_ok_spec {ε : Type} {owner : OwnerId}
    {layout : CollectionLayout} (hValid : layout.Valid)
    {length fieldCount field n : Nat} (hN : n ≤ length) (hField : field < fieldCount)
    {s : Core.State} {table : Nat → Nat → UInt8}
    (hRep : ByteCollectionRep s owner layout length fieldCount table)
    (f : UInt8 → Except ε UInt8) (out : Nat → UInt8)
    (hOk : ∀ i, i < n → f (table i field) = .ok (out i)) :
    ∃ s', tryMapFieldLoop owner layout length fieldCount field f s n = .ok s' ∧
      (∀ i, i < n → s'.byte ⟨owner, collectionSlot layout length fieldCount i field⟩ = some (out i)) ∧
      (∀ loc, (¬ ∃ i, i < n ∧ loc = ⟨owner, collectionSlot layout length fieldCount i field⟩) →
        s'.byte loc = s.byte loc) := by
  induction n with
  | zero =>
    refine ⟨s, rfl, fun i hi => by omega, fun _ _ => rfl⟩
  | succ n ih =>
    have hNLe : n ≤ length := Nat.le_of_succ_le hN
    have hNLt : n < length := hN
    obtain ⟨mid, hRunMid, hUpdMid, hFrameMid⟩ :=
      ih hNLe (fun i hi => hOk i (Nat.lt_succ_of_lt hi))
    let locN : ByteLocation := ⟨owner, collectionSlot layout length fieldCount n field⟩
    have hNotIn : ¬ ∃ i, i < n ∧ locN = ⟨owner, collectionSlot layout length fieldCount i field⟩ := by
      rintro ⟨i, hi, hEq⟩
      have hSame := (collectionSlot_eq_iff hValid hNLt (Nat.lt_trans hi hNLt) hField hField).mp
        (congrArg ByteLocation.offset hEq)
      omega
    have hMidN : mid.byte locN = some (table n field) :=
      (hFrameMid locN hNotIn).trans (hRep n hNLt field hField)
    have hStepOk : f (table n field) = .ok (out n) := hOk n (Nat.lt_succ_self n)
    refine ⟨mid.store locN (out n), ?_, ?_, ?_⟩
    · dsimp [tryMapFieldLoop]
      rw [hRunMid, resAndThen]
      dsimp [tryMapFieldStep]
      change (match mid.byte locN with
        | some b => match f b with | Except.ok b' => Except.ok (mid.store locN b') | Except.error e => Except.error e
        | none => Except.ok mid) = _
      rw [hMidN]
      dsimp only
      rw [hStepOk]
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hLt | hEq
      · have hLocNe : locN ≠ ⟨owner, collectionSlot layout length fieldCount i field⟩ := by
          intro hEq
          have hSame := (collectionSlot_eq_iff hValid hNLt (Nat.lt_trans hLt hNLt) hField hField).mp
            (congrArg ByteLocation.offset hEq)
          omega
        rw [Core.State.store_byte_other mid locN _ (out n) hLocNe]
        exact hUpdMid i hLt
      · rw [hEq]
        exact Core.State.store_byte_written mid locN (table n field) (out n) hMidN
    · intro loc hNot
      have hLocNe : locN ≠ loc := by
        intro hEq
        exact hNot ⟨n, Nat.lt_succ_self n, hEq.symm⟩
      have hNotOld : ¬ ∃ i, i < n ∧ loc = ⟨owner, collectionSlot layout length fieldCount i field⟩ :=
        fun ⟨i, hi, hEq⟩ => hNot ⟨i, Nat.lt_succ_of_lt hi, hEq⟩
      rw [Core.State.store_byte_other mid locN loc (out n) hLocNe]
      exact hFrameMid loc hNotOld

theorem tryMapFieldInPlace_ok_rep {ε : Type} {owner : OwnerId}
    {layout : CollectionLayout} (hValid : layout.Valid)
    {length fieldCount field : Nat} (hField : field < fieldCount)
    {s : Core.State} {table : Nat → Nat → UInt8}
    (hRep : ByteCollectionRep s owner layout length fieldCount table)
    (f : UInt8 → Except ε UInt8) (out : Nat → UInt8)
    (hOk : ∀ i, i < length → f (table i field) = .ok (out i)) :
    ∃ s', tryMapFieldInPlace owner layout length fieldCount field f s = .ok s' ∧
      ByteCollectionRep s' owner layout length fieldCount
        (fun i g => if g = field then out i else table i g) ∧
      (∀ other off, other ≠ owner → s'.byte ⟨other, off⟩ = s.byte ⟨other, off⟩) := by
  obtain ⟨s', hRun, hUpd, hFrame⟩ :=
    tryMapFieldLoop_ok_spec hValid (Nat.le_refl _) hField hRep f out hOk
  refine ⟨s', hRun, ?_, ?_⟩
  · intro i hi g hg
    by_cases hGF : g = field
    · subst hGF
      dsimp only
      rw [ite_eq_left rfl]
      exact hUpd i hi
    · dsimp only
      rw [ite_eq_right hGF]
      have hNot : ¬ ∃ j, j < length ∧
          (⟨owner, collectionSlot layout length fieldCount i g⟩ : ByteLocation) =
            ⟨owner, collectionSlot layout length fieldCount j field⟩ := by
        rintro ⟨j, hj, hEq⟩
        have hSame := (collectionSlot_eq_iff hValid hi hj hg hField).mp
          (congrArg ByteLocation.offset hEq)
        exact hGF hSame.2
      exact (hFrame _ hNot).trans (hRep i hi g hg)
  · intro other off hNe
    have hNot : ¬ ∃ j, j < length ∧
        (⟨other, off⟩ : ByteLocation) = ⟨owner, collectionSlot layout length fieldCount j field⟩ := by
      rintro ⟨j, _, hEq⟩
      exact hNe (congrArg ByteLocation.allocation hEq)
    exact hFrame ⟨other, off⟩ hNot

theorem tryMapFieldInPlace_fusion {ε : Type} {owner : OwnerId}
    {layout : CollectionLayout} (hValid : layout.Valid)
    {length fieldCount field : Nat} (hField : field < fieldCount)
    {s : Core.State} {table : Nat → Nat → UInt8}
    (hRep : ByteCollectionRep s owner layout length fieldCount table)
    (f g : UInt8 → Except ε UInt8) (out1 out2 : Nat → UInt8)
    (hOk1 : ∀ i, i < length → f (table i field) = .ok (out1 i))
    (hOk2 : ∀ i, i < length → g (out1 i) = .ok (out2 i)) :
    ∃ s2 s12,
      resAndThen (tryMapFieldInPlace owner layout length fieldCount field f s)
        (tryMapFieldInPlace owner layout length fieldCount field g) = .ok s2 ∧
      tryMapFieldInPlace owner layout length fieldCount field (kleisliCompose f g) s = .ok s12 ∧
      ∀ loc, s2.byte loc = s12.byte loc := by
  obtain ⟨s1, hRun1, hUpd1, hFrame1⟩ :=
    tryMapFieldLoop_ok_spec hValid (Nat.le_refl _) hField hRep f out1 hOk1
  have hRep1 : ByteCollectionRep s1 owner layout length fieldCount
      (fun i g' => if g' = field then out1 i else table i g') := by
    intro i hi g' hg'
    by_cases hGF : g' = field
    · subst hGF
      dsimp only
      rw [ite_eq_left rfl]
      exact hUpd1 i hi
    · dsimp only
      rw [ite_eq_right hGF]
      have hNot : ¬ ∃ j, j < length ∧
          (⟨owner, collectionSlot layout length fieldCount i g'⟩ : ByteLocation) =
            ⟨owner, collectionSlot layout length fieldCount j field⟩ := by
        rintro ⟨j, hj, hEq⟩
        have hSame := (collectionSlot_eq_iff hValid hi hj hg' hField).mp
          (congrArg ByteLocation.offset hEq)
        exact hGF hSame.2
      exact (hFrame1 _ hNot).trans (hRep i hi g' hg')
  have hOk2' : ∀ i, i < length → g (if field = field then out1 i else table i field) = .ok (out2 i) := by
    intro i hi
    simp [hOk2 i hi]
  obtain ⟨s2, hRun2, hUpd2, hFrame2⟩ :=
    tryMapFieldLoop_ok_spec hValid (Nat.le_refl _) hField hRep1 g out2 hOk2'
  have hOkComp : ∀ i, i < length → (kleisliCompose f g) (table i field) = .ok (out2 i) := by
    intro i hi
    dsimp [kleisliCompose]
    rw [hOk1 i hi, resAndThen, hOk2 i hi]
  obtain ⟨s12, hRun12, hUpd12, hFrame12⟩ :=
    tryMapFieldLoop_ok_spec hValid (Nat.le_refl _) hField hRep (kleisliCompose f g) out2 hOkComp
  refine ⟨s2, s12, ?_, hRun12, ?_⟩
  · dsimp [tryMapFieldInPlace] at hRun1 hRun2 ⊢
    rw [hRun1, resAndThen]
    exact hRun2
  · intro loc
    by_cases hIn : ∃ i, i < length ∧ loc = ⟨owner, collectionSlot layout length fieldCount i field⟩
    · obtain ⟨i, hi, rfl⟩ := hIn
      rw [hUpd2 i hi, hUpd12 i hi]
    · rw [hFrame2 loc hIn, hFrame1 loc hIn, hFrame12 loc hIn]

def resUnwrapOr {ε α : Type} (r : Except ε α) (d : α) : α :=
  match r with
  | .ok a => a
  | .error _ => d

theorem optMap_id {α : Type} (o : Option α) : Option.map id o = o := by
  cases o <;> rfl

theorem optMap_comp {α β γ : Type} (f : α → β) (g : β → γ) (o : Option α) :
    Option.map g (Option.map f o) = Option.map (g ∘ f) o := by
  cases o <;> rfl

theorem optMap_unwrapOr {α β : Type} (f : α → β) (o : Option α) (d : β) :
    (Option.map f o).getD d = match o with | some a => f a | none => d := by
  cases o <;> rfl

theorem resMap_unwrapOr {ε α β : Type} (f : α → β) (r : Except ε α) (d : β) :
    resUnwrapOr (resMap f r) d = match r with | .ok a => f a | .error _ => d := by
  cases r <;> rfl

theorem optToResult_andThen_natural {ε α β : Type} (err : ε)
    (o : Option α) (k : α → Option β) :
    resAndThen (optionToResult err o) (fun x => optionToResult err (k x)) =
      optionToResult err (optAndThen o k) := by
  cases o <;> rfl

end Aethel.CategoricalCombinators
