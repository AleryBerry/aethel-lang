import Aethel.Structured

namespace Aethel.Structured.Tests

private def twoBytes (body : RawCode) : RawCode :=
  .instruction (.alloc 0 [1, 2])
    (.instruction (.alias 0 0 0 .exclusive) (.instruction (.alias 1 0 1 .exclusive) body))

private def writeAndRead (handle : Core.HandleId) (value : Functional.Raw) : RawCode :=
  .write (.handle handle) value
    (.instruction (.read 0) (.instruction (.read 1) .finish))

private def conditional (takeFirst : Bool) : RawCode :=
  twoBytes (.letValue (.app (.lam .byte (.var 0)) (.byte 23))
    (.branch (.app (.lam .bool (.var 0)) (.bool takeFirst))
      (writeAndRead 0 (.var 0)) (writeAndRead 1 (.var 0))))

private def expectObservations (name : String) (program : RawCode) (expected : List UInt8) :
    IO Unit := do
  match executeClosed program with
  | .ok (some final) =>
    unless final.observations.reverse == expected do
      throw (IO.userError s!"{name}: incorrect observations")
  | .ok none => throw (IO.userError s!"{name}: verified code failed to execute")
  | .error error => throw (IO.userError s!"{name}: {repr error}")

private def expectReject (name : String) (program : RawCode) (expected : CheckError) : IO Unit := do
  match verify program with
  | .error error =>
    unless error == expected do
      throw (IO.userError s!"{name}: expected {repr expected}, got {repr error}")
  | .ok _ => throw (IO.userError s!"{name}: verifier accepted the program")

def run : IO Unit := do
  expectObservations "computed byte updates only the first field" (conditional true) [23, 2]
  expectObservations "computed byte updates only the second field" (conditional false) [1, 23]
  expectObservations "computed write through exclusive reservation"
    (twoBytes (.instruction (.reserve 0 0 .exclusive) (.write (.view 0) (.byte 9)
      (.instruction (.release 0) (.instruction (.read 0) .finish))))) [9]
  expectObservations "lexical binding shadows an outer byte"
    (twoBytes (.letValue (.byte 8) (.letValue (.byte 9) (writeAndRead 0 (.var 0))))) [9, 2]
  expectReject "write expects a byte"
    (twoBytes (writeAndRead 0 (.nat 7))) (.illTyped (.expected .byte .nat))
  expectReject "condition expects a Bool"
    (.branch (.byte 1) .finish .finish) (.illTyped (.expected .bool .byte))
  expectReject "reject invalid authority in an unselected arm"
    (twoBytes (.branch (.bool true) .finish (.write (.handle 9) (.byte 7) .finish))) .invalidResources
  expectReject "reject type errors in an unselected arm"
    (twoBytes (.branch (.bool true) .finish (.write (.handle 0) (.var 0) .finish)))
    (.illTyped (.unbound 0))
  expectReject "reject alias write during an exclusive view"
    (twoBytes (.instruction (.reserve 0 0 .exclusive) (.write (.handle 0) (.byte 7)
      (.instruction (.release 0) .finish)))) .invalidResources
  expectReject "reject a reservation leaked by either arm"
    (twoBytes (.branch (.bool true) .finish (.instruction (.reserve 0 0 .shared) .finish)))
    .invalidResources
  expectObservations "read a byte and copy it through a typed lambda"
    (twoBytes (.read (.handle 0) (writeAndRead 1 (.app (.lam .byte (.var 0)) (.var 0))))) [1, 1, 1]
  expectObservations "a read sees a preceding heap write"
    (twoBytes (.write (.handle 0) (.byte 53) (.read (.handle 0) (writeAndRead 1 (.var 0))))) [53, 53, 53]
  expectObservations "a local keeps the byte captured before a later write"
    (twoBytes (.read (.handle 0) (.write (.handle 0) (.byte 53) (writeAndRead 1 (.var 0))))) [1, 53, 1]
  expectObservations "read through an exclusive view"
    (twoBytes (.instruction (.reserve 0 0 .exclusive) (.write (.view 0) (.byte 17)
      (.read (.view 0) (.instruction (.release 0) (writeAndRead 1 (.var 0))))))) [17, 17, 17]
  expectObservations "shared reservation permits an overlapping read"
    (twoBytes (.instruction (.reserve 0 0 .shared)
      (.read (.handle 0) (.instruction (.release 0) .finish)))) [1]
  expectObservations "heap byte selects the true arm"
    (twoBytes (.read (.handle 0) (.branch (.byteEq (.var 0) (.byte 1))
      (writeAndRead 1 (.byte 8)) (writeAndRead 1 (.byte 9))))) [1, 1, 8]
  expectObservations "heap byte selects the false arm"
    (twoBytes (.write (.handle 0) (.byte 2) (.read (.handle 0) (.branch (.byteEq (.var 0) (.byte 1))
      (writeAndRead 1 (.byte 8)) (writeAndRead 1 (.byte 9)))))) [2, 2, 9]
  expectReject "borrow checking covers both arms of a heap-dependent branch"
    (twoBytes (.read (.handle 0) (.branch (.byteEq (.var 0) (.byte 1)) .finish
      (.read (.handle 9) .finish)))) .invalidResources
  expectReject "read through a missing handle" (.read (.handle 0) .finish) .invalidResources
  expectReject "read through a released view"
    (twoBytes (.instruction (.reserve 0 0 .shared)
      (.instruction (.release 0) (.read (.view 0) .finish)))) .invalidResources
  expectReject "read after destruction invalidates the handle"
    (twoBytes (.instruction (.destroy 0) (.read (.handle 0) .finish))) .invalidResources
  expectReject "exclusive reservation blocks an overlapping handle read"
    (twoBytes (.instruction (.alias 2 0 0 .shared) (.instruction (.reserve 0 0 .exclusive)
      (.read (.handle 2) (.instruction (.release 0) .finish))))) .invalidResources
  expectReject "loaded byte is not an implicit Boolean"
    (twoBytes (.read (.handle 0) (.branch (.var 0) .finish .finish)))
    (.illTyped (.expected .bool .byte))
  IO.println "23 structured program regressions passed"

private def observeWord (expected : UInt16) : RawCode :=
  .branch (.uint16Eq (.var 0) (.uint16 expected))
    (writeAndRead 1 (.byte 8)) (writeAndRead 1 (.byte 9))

def runWideAndFacts : IO Unit := do
  expectObservations "UInt16 load uses little-endian byte order"
    (twoBytes (.readUInt16LE (.handle 0) (.handle 1) (observeWord 513))) [1, 2, 1, 8]
  expectObservations "UInt16 load sees a changed high byte"
    (twoBytes (.write (.handle 1) (.byte 4)
      (.readUInt16LE (.handle 0) (.handle 1) (observeWord 1025)))) [1, 4, 1, 8]
  expectObservations "bytewise UInt16 load accepts an odd offset"
    (.instruction (.alloc 0 [0, 255, 255]) (.instruction (.alias 0 0 1 .shared)
      (.instruction (.alias 1 0 2 .exclusive)
        (.readUInt16LE (.handle 0) (.handle 1) (observeWord 65535))))) [255, 255, 255, 8]
  expectObservations "UInt16 load respects a view on its high byte"
    (twoBytes (.instruction (.reserve 7 1 .exclusive)
      (.readUInt16LE (.handle 0) (.view 7) (.instruction (.release 7) (observeWord 513)))))
    [1, 2, 1, 8]
  expectReject "UInt16 load rejects reversed byte order"
    (twoBytes (.readUInt16LE (.handle 1) (.handle 0) .finish)) .invalidResources
  expectReject "UInt16 load rejects a missing high byte"
    (twoBytes (.readUInt16LE (.handle 0) (.handle 9) .finish)) .invalidResources
  expectReject "UInt16 load cannot cross allocation boundaries"
    (twoBytes (.instruction (.alloc 1 [0, 3]) (.instruction (.alias 7 1 1 .shared)
      (.readUInt16LE (.handle 0) (.handle 7) .finish)))) .invalidResources
  expectReject "UInt16 load checks the high byte's permission"
    (twoBytes (.instruction (.reserve 7 1 .exclusive)
      (.readUInt16LE (.handle 0) (.handle 1) (.instruction (.release 7) .finish))))
    .invalidResources
  expectReject "UInt16 local cannot be stored through a byte write"
    (twoBytes (.readUInt16LE (.handle 0) (.handle 1) (.write (.handle 0) (.var 0) .finish)))
    (.illTyped (.expected .byte .uint16))

  let invalid : RawCode := .read (.handle 9) .finish
  let equals (index : Nat) (value : UInt8) : Functional.Raw := .byteEq (.var index) (.byte value)
  expectObservations "true-arm equality excludes a different constant after write and bind"
    (twoBytes (.read (.handle 0) (.branch (equals 0 1)
      (.write (.handle 0) (.byte 2) (.letValue (.nat 0)
        (.branch (.byteEq (.byte 2) (.var 1)) invalid (writeAndRead 1 (.var 1)))))
      .finish))) [1, 2, 1]
  expectObservations "false-arm disequality rules out a repeated comparison"
    (twoBytes (.read (.handle 1) (.branch (equals 0 1) .finish
      (.branch (equals 0 1) invalid (writeAndRead 1 (.byte 7)))))) [2, 1, 7]
  expectReject "an earlier guard does not predict a fresh load after a write"
    (twoBytes (.read (.handle 0) (.branch (equals 0 1)
      (.write (.handle 0) (.byte 2) (.read (.handle 0) (.branch (equals 0 1) .finish invalid)))
      .finish))) .invalidResources
  expectReject "a shadowing byte binding does not inherit the previous binding's fact"
    (twoBytes (.read (.handle 0) (.branch (equals 0 1)
      (.letValue (.byte 2) (.branch (equals 0 1) .finish invalid)) .finish))) .invalidResources
  expectReject "disequality with one constant says nothing about a different constant"
    (twoBytes (.read (.handle 1) (.branch (equals 0 1) .finish
      (.branch (equals 0 2) invalid .finish)))) .invalidResources
  expectObservations "UInt16 true-arm equality prunes a conflicting UInt16 comparison"
    (twoBytes (.readUInt16LE (.handle 0) (.handle 1)
      (.branch (.uint16Eq (.var 0) (.uint16 513))
        (.branch (.uint16Eq (.var 0) (.uint16 999)) invalid (writeAndRead 1 (.byte 42)))
        .finish))) [1, 2, 1, 42]
  expectObservations "variable equality fact is symmetric and prunes infeasible branch"
    (twoBytes (.read (.handle 0) (.read (.handle 0)
      (.branch (.byteEq (.var 1) (.var 0))
        (.branch (.byteEq (.var 0) (.var 1)) (writeAndRead 1 (.byte 77)) invalid)
        .finish)))) [1, 1, 1, 77]
  expectObservations "fact join retains knowledge on both branches"
    (twoBytes (.read (.handle 0)
      (.branch (.byteEq (.var 0) (.byte 1))
        (.letValue (.byte 5) (writeAndRead 1 (.var 0)))
        (.letValue (.byte 5) (writeAndRead 1 (.var 0)))))) [1, 1, 5]
  expectObservations "UInt16 store writes adjacent low and high bytes and allows wide read"
    (twoBytes (.writeUInt16LE (.handle 0) (.handle 1) (.uint16 1027)
      (.readUInt16LE (.handle 0) (.handle 1) (observeWord 1027)))) [3, 4, 3, 8]
  expectObservations "byte less-than fact prunes conflicting equality"
    (twoBytes (.read (.handle 0)
      (.branch (.byteLt (.var 0) (.byte 2))
        (.branch (.byteEq (.var 0) (.byte 5)) invalid (writeAndRead 1 (.byte 99)))
        .finish))) [1, 1, 99]
  expectObservations "UInt16 less-than false-branch prunes smaller comparison"
    (twoBytes (.readUInt16LE (.handle 0) (.handle 1)
      (.branch (.uint16Lt (.var 0) (.uint16 500))
        .finish
        (.branch (.uint16Lt (.var 0) (.uint16 300)) invalid (writeAndRead 1 (.byte 88)))))) [1, 2, 1, 88]
  IO.println "20 wide-load and branch-fact regressions passed"

end Aethel.Structured.Tests
