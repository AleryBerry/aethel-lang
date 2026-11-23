import Aethel.PathRegex

namespace Aethel

/-- Candidate all-pairs path summaries. Their relationship to concrete loans
must still be established by transfer/closure and machine-invariant proofs. -/
structure BorrowSummary (α : Type) where
  nodeCount : Nat
  paths : Nat → Nat → Regex α

def BorrowSummary.OutboundSafe (g : BorrowSummary α) (source : Nat) : Prop :=
  ∀ target, target < g.nodeCount → ∀ xs, (g.paths source target).Matches xs → xs = []

def BorrowSummary.checkOutbound (g : BorrowSummary α) (source : Nat) : Bool :=
  (List.range g.nodeCount).all fun target => (g.paths source target).onlyEmpty

/-- Decides the outbound condition on supplied summaries, not whole-program safety. -/
theorem BorrowSummary.checkOutbound_correct (g : BorrowSummary α) (source : Nat) :
    g.checkOutbound source = true ↔ g.OutboundSafe source := by
  simp [checkOutbound, OutboundSafe, List.all_eq_true, Regex.onlyEmpty_correct]

structure Loan (α : Type) where
  source : Nat
  target : Nat
  path : List α
  deriving DecidableEq, Repr

def BorrowSummary.refl (nodeCount : Nat) : BorrowSummary α :=
  ⟨nodeCount, fun u v => if u = v then .epsilon else .empty⟩

theorem BorrowSummary.refl_self (nodeCount : Nat) (u : Nat) :
    (BorrowSummary.refl (α := α) nodeCount).paths u u = .epsilon := by
  dsimp [refl]; simp

theorem BorrowSummary.refl_matches_nil (nodeCount : Nat) (u : Nat) :
    ((BorrowSummary.refl (α := α) nodeCount).paths u u).Matches [] := by
  rw [BorrowSummary.refl_self]
  exact .epsilon

def BorrowSummary.CoversLoan (g : BorrowSummary α) (loan : Loan α) : Prop :=
  (g.paths loan.source loan.target).Matches loan.path

def BorrowSummary.Covers (g : BorrowSummary α) (loans : List (Loan α)) : Prop :=
  ∀ loan ∈ loans, g.CoversLoan loan

def BorrowSummary.checkCovers [DecidableEq α] (g : BorrowSummary α) (loans : List (Loan α)) : Bool :=
  loans.all fun loan => (g.paths loan.source loan.target).accepts loan.path

theorem BorrowSummary.checkCovers_correct [DecidableEq α] (g : BorrowSummary α) (loans : List (Loan α)) :
    g.checkCovers loans = true ↔ g.Covers loans := by
  simp only [checkCovers, Covers, CoversLoan, List.all_eq_true, Regex.accepts_correct]

def BorrowSummary.addEdge (g : BorrowSummary α) (src dst : Nat) (edge : Regex α) : BorrowSummary α :=
  ⟨g.nodeCount, fun u v => .alt (g.paths u v) (.seq (g.paths u src) (.seq edge (g.paths dst v)))⟩

theorem BorrowSummary.addEdge_covers_existing (g : BorrowSummary α) (src dst : Nat) (edge : Regex α)
    {u v : Nat} {p : List α} (h : (g.paths u v).Matches p) :
    ((g.addEdge src dst edge).paths u v).Matches p :=
  .left h

theorem BorrowSummary.addEdge_covers_transfer (g : BorrowSummary α) (src dst : Nat) (edge : Regex α)
    {u v : Nat} {p1 pEdge p2 : List α}
    (h1 : (g.paths u src).Matches p1) (he : edge.Matches pEdge) (h2 : (g.paths dst v).Matches p2) :
    ((g.addEdge src dst edge).paths u v).Matches (p1 ++ (pEdge ++ p2)) :=
  .right (.seq h1 (.seq he h2))

def BorrowSummary.releaseNode (g : BorrowSummary α) (k : Nat) : BorrowSummary α :=
  ⟨g.nodeCount, fun u v => if u = k || v = k then .empty else g.paths u v⟩

theorem BorrowSummary.releaseNode_outboundSafe (g : BorrowSummary α) (k : Nat) :
    (g.releaseNode k).OutboundSafe k := by
  intro target _ xs h
  dsimp [releaseNode] at h
  split at h
  · cases h
  · rename_i hne
    exfalso
    apply hne
    simp

theorem BorrowSummary.releaseNode_preserves_unrelated (g : BorrowSummary α) (k : Nat)
    {u v : Nat} (hu : u ≠ k) (hv : v ≠ k) :
    (g.releaseNode k).paths u v = g.paths u v := by
  dsimp [releaseNode]
  split
  · rename_i h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    cases h with
    | inl h => exact False.elim (hu h)
    | inr h => exact False.elim (hv h)
  · rfl

def BorrowSummary.WriteSafe (g : BorrowSummary α) (source : Nat) (writePath : List α) : Prop :=
  ∀ target, target < g.nodeCount → ∀ borrowPath, (g.paths source target).Matches borrowPath →
    ¬ (writePath <+: borrowPath ∨ borrowPath <+: writePath)

theorem whole_variable_borrow_conflicts (writePath : List α) :
    ([] : List α) <+: writePath :=
  List.nil_prefix

theorem prefix_head_eq {x y : α} {xs ys : List α} (h : (x :: xs) <+: (y :: ys)) : x = y := by
  rcases h with ⟨_, heq⟩
  exact List.cons.inj heq |>.1

theorem prefix_conflict_head_eq {x y : α} {xs ys : List α}
    (h : (x :: xs) <+: (y :: ys) ∨ (y :: ys) <+: (x :: xs)) : x = y := by
  cases h with
  | inl h => exact prefix_head_eq h
  | inr h => exact (prefix_head_eq h).symm

theorem paths_head_ne_writeSafe {x y : α} {xs ys : List α} (hne : x ≠ y) :
    ¬ ((x :: xs) <+: (y :: ys) ∨ (y :: ys) <+: (x :: xs)) := by
  intro h
  exact hne (prefix_conflict_head_eq h)

theorem BorrowSummary.outboundSafe_writeSafe (g : BorrowSummary α) (source : Nat)
    (hOut : g.OutboundSafe source) (writePath : List α)
    (hNoEps : ∀ target < g.nodeCount, ¬ (g.paths source target).Matches []) :
    g.WriteSafe source writePath := by
  intro target hTarget borrowPath hMatches
  have hEmpty := hOut target hTarget borrowPath hMatches
  subst hEmpty
  exact False.elim (hNoEps target hTarget hMatches)

end Aethel
