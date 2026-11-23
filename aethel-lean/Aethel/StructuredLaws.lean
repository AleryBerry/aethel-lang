import Aethel.Structured
import Aethel.ResourceFrame

namespace Aethel.Structured

open Core Functional

/-- A postcondition about the actual final state of a structured program.
The initial state, pure inputs, and resource effects all belong to the claim. -/
def Code.Ensures (code : Code ctx) (pre : Env ctx → State → Prop)
    (post : Env ctx → State → State → Prop) : Prop :=
  ∀ env initial steps final, pre env initial →
    Executes env initial code steps final → post env initial final

/-- Combine an all-paths resource check with a postcondition to obtain a
closed execution that establishes the promised observation. -/
theorem Code.executes_with_postcondition (code : Code ctx)
    {pre : Env ctx → State → Prop} {post : Env ctx → State → State → Prop}
    (law : code.Ensures pre post) (env : Env ctx) (initial : State)
    (allowed : pre env initial) (checked : check initial.resources code = true) :
    ∃ steps final, runCode env initial code = some (steps, final) ∧
      final.views = [] ∧ post env initial final := by
  obtain ⟨steps, final, executed, closed⟩ := check_executes code env initial checked
  exact ⟨steps, final, executed.agrees, closed, law env initial _ final allowed executed⟩

theorem computed_write_preserves_sibling (id : HandleId) (term : Term ctx .byte)
    (sibling : ByteLocation) :
    (Code.write (.handle id) term .finish).Ensures
      (fun _ initial => ∃ h, initial.handle id = some h ∧ h.location ≠ sibling)
      (fun _ initial final => final.byte sibling = initial.byte sibling) := by
  intro env initial steps final allowed executed
  obtain ⟨handle, lookup, different⟩ := allowed
  cases executed
  rename_i first evaluated remaining
  cases remaining
  exact first.write_frame lookup sibling different

theorem writeUInt16LE_preserves_sibling (lowId highId : HandleId) (term : Term ctx .uint16)
    (sibling : ByteLocation) :
    (Code.writeUInt16LE (.handle lowId) (.handle highId) term .finish).Ensures
      (fun _ initial => ∃ hLow hHigh, initial.handle lowId = some hLow ∧
        initial.handle highId = some hHigh ∧
        hLow.location ≠ sibling ∧ hHigh.location ≠ sibling)
      (fun _ initial final => final.byte sibling = initial.byte sibling) := by
  intro env initial steps final allowed executed
  obtain ⟨hLow, hHigh, lookupLow, lookupHigh, diffLow, diffHigh⟩ := allowed
  cases executed with
  | writeUInt16LE adj evalTerm step1 step2 remaining =>
    cases remaining
    have frame1 := step1.write_frame lookupLow sibling diffLow
    have frame2 : final.byte sibling = _ := step2.write_frame (by cases step1; exact lookupHigh) sibling diffHigh
    cases step1
    exact frame2.trans frame1

/-- A legal write can change the byte it targets, so a law claiming that
the target is preserved needs a stronger premise than resource legality. -/
theorem cannot_claim_written_byte_is_preserved :
    ¬ (Code.write (.handle 0) (.byte 9) .finish : Code []).Ensures
      (fun _ _ => True)
      (fun _ initial final => final.byte ⟨0, 0⟩ = initial.byte ⟨0, 0⟩) := by
  intro law
  let initial : State := (({} : State).addAllocation 0 [1]).addHandle 0 ⟨⟨0, 0⟩, .exclusive⟩
  let final := initial.store ⟨0, 0⟩ 9
  have executed : Executes Env.empty initial (Code.write (.handle 0) (.byte 9) .finish)
      [.write 0 9] final :=
    .write .byte (execute_sound (by rfl)) .finish
  exact (by decide : (some (9 : UInt8)) ≠ some 1) (law Env.empty initial _ final trivial executed)

end Aethel.Structured
