import Aethel.Laws
import Aethel.BoundedSearch

namespace Aethel.Functional.Tests

private def expectValue (name : String) (expr : Raw) (ty : Ty)
    [DecidableEq ty.Value] (expected : ty.Value) : IO Unit := do
  match elaborate [] expr with
  | .error error => throw (IO.userError s!"{name}: {repr error}")
  | .ok ⟨actual, term, _⟩ =>
    if same : actual = ty then
      let value := Term.eval Env.empty (same ▸ term)
      unless value = expected do
        throw (IO.userError s!"{name}: unexpected result")
    else
      throw (IO.userError s!"{name}: unexpected type {repr actual}")

private def expectError (name : String) (expr : Raw) (expected : TypeError) : IO Unit := do
  match elaborate [] expr with
  | .error error =>
    unless error = expected do
      throw (IO.userError s!"{name}: expected {repr expected}, got {repr error}")
  | .ok _ => throw (IO.userError s!"{name}: accepted invalid expression")

def run : IO Unit := do
  expectValue "strict application" (.app (.lam .nat (.var 0)) (.nat 7)) .nat 7
  expectValue "closure captures lexical value"
    (.app (.app (.lam .nat (.lam .bool (.var 1))) (.nat 9)) (.bool false)) .nat 9
  expectValue "conditional selects false branch" (.branch (.bool false) (.nat 5) (.nat 8)) .nat 8
  expectValue "option binder" (.optionCase (.some (.nat 17)) (.nat 0) (.var 0)) .nat 17
  expectValue "absent option" (.optionCase (.none .nat) (.nat 5) (.var 0)) .nat 5
  expectValue "encode and decode constructor"
    (.decodeStatus (.encodeStatus (.status .dead))) (.option .status) (some .dead)
  expectValue "invalid encoding returns no value" (.decodeStatus (.nat 64)) (.option .status) none
  expectError "unbound variable" (.var 0) (.unbound 0)
  expectError "nonfunction application" (.app (.nat 3) (.nat 5)) (.expectedFunction .nat)
  expectError "argument type mismatch" (.app (.lam .nat (.var 0)) (.bool true)) (.expected .nat .bool)
  expectError "branch types disagree" (.branch (.bool true) (.nat 3) (.bool false)) (.expected .nat .bool)
  expectError "nonoption match" (.optionCase (.bool true) (.nat 2) (.nat 3)) (.expectedOption .bool)
  let u1 : IntegerType := .unsigned .w1
  let u8 : IntegerType := .unsigned .w8
  let i32 : IntegerType := .signed .w32
  expectValue "u1 accepts 1" (.integer u1 1) (.integer u1) (BitVec.ofNat 1 1)
  expectValue "u8 literal works with existing byte equality"
    (.byteEq (.integer u8 255) (.byte 255)) .bool true
  expectValue "i32 accepts a negative literal as two's complement"
    (.integer i32 (-1)) (.integer i32) (BitVec.ofNat 32 4294967295)
  expectError "u1 rejects 2" (.integer u1 2) (.integerOutOfRange u1 2)
  expectError "u8 rejects negative values" (.integer u8 (-1)) (.integerOutOfRange u8 (-1))
  expectError "i32 rejects the first positive value outside its range"
    (.integer i32 2147483648) (.integerOutOfRange i32 2147483648)
  expectError "integer signedness and width remain part of the type"
    (.byteEq (.integer (.signed .w8) 1) (.byte 1)) (.expected .byte (.integer (.signed .w8)))
  IO.println "19 pure functional core regressions passed"

private def findOdd : List Nat → Search.Probe (List Nat) Nat
  | [] => .finished
  | head :: tail => if head % 2 = 1 then .found head else .advance tail

def runSearch : IO Unit := do
  unless Search.run findOdd 0 [3] == .pending [3] do
    throw (IO.userError "zero budget must leave the input untouched")
  unless Search.run findOdd 1 [2, 5] == .pending [5] do
    throw (IO.userError "one probe must suspend before the next")
  unless Search.run findOdd 2 [2, 5] == .found 5 do
    throw (IO.userError "second probe must find the odd entry")
  unless Search.run findOdd 2 [2] == .finished do
    throw (IO.userError "an exhausted input must finish")
  unless (Search.run (fun n : Nat => .advance (n + 1)) 100 0 :
      Search.Outcome Nat Nat) == .pending 100 do
    throw (IO.userError "an always-advancing probe must suspend")
  IO.println "5 bounded-search regressions passed"

end Aethel.Functional.Tests
