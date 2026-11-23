import Aethel.ResourceLiveness

namespace Aethel.Core.Tests

structure Positive where
  name : String
  program : Program
  observations : List UInt8
  heap : List (OwnerId × List UInt8)

private def twoAliases : Program :=
  [.alloc 0 [1, 2], .alias 0 0 0 .exclusive, .alias 1 0 0 .exclusive]

private def twoCells : Program :=
  [.alloc 0 [1, 2], .alias 0 0 0 .exclusive, .alias 1 0 1 .exclusive]

def positives : List Positive := [
  ⟨"empty program", [], [], []⟩,
  ⟨"empty owned allocation", [.alloc 0 []], [], [(0, [])]⟩,
  ⟨"alias handles alternate writes", twoAliases ++
    [.write 0 10, .read 1, .write 1 20, .read 0], [10, 20], [(0, [20, 2])]⟩,
  ⟨"read authority may coexist with writer handle", [.alloc 0 [1],
    .alias 0 0 0 .shared, .alias 1 0 0 .exclusive, .write 1 8, .read 0],
    [8], [(0, [8])]⟩,
  ⟨"exclusive view updates then releases", twoAliases ++
    [.reserve 0 0 .exclusive, .writeView 0 9, .readView 0, .release 0, .read 1],
    [9, 9], [(0, [9, 2])]⟩,
  ⟨"disjoint byte views coexist", twoCells ++
    [.reserve 0 0 .exclusive, .reserve 1 1 .exclusive, .writeView 0 8,
     .writeView 1 9, .readView 0, .readView 1, .release 0, .release 1],
    [8, 9], [(0, [8, 9])]⟩,
  ⟨"sibling handle remains usable", twoCells ++
    [.reserve 0 0 .exclusive, .write 1 7, .read 1, .writeView 0 6, .release 0],
    [7], [(0, [6, 7])]⟩,
  ⟨"shared views overlap", twoAliases ++
    [.reserve 0 0 .shared, .reserve 1 1 .shared, .readView 0, .readView 1,
     .read 0, .release 0, .release 1], [1, 1, 1], [(0, [1, 2])]⟩,
  ⟨"shared authority creates shared view", [.alloc 0 [3], .alias 0 0 0 .shared,
    .reserve 0 0 .shared, .readView 0, .release 0], [3], [(0, [3])]⟩,
  ⟨"reservation belongs to owner not handle variable", twoAliases ++
    [.reserve 0 0 .exclusive, .forget 0, .writeView 0 4, .release 0, .read 1],
    [4], [(0, [4, 2])]⟩,
  ⟨"released view ID can be rebound", twoCells ++
    [.reserve 0 0 .exclusive, .writeView 0 4, .release 0,
     .reserve 0 1 .exclusive, .writeView 0 5, .release 0], [], [(0, [4, 5])]⟩,
  ⟨"forgotten handle ID can be rebound", twoCells ++
    [.forget 0, .alias 0 0 1 .exclusive, .write 0 5, .read 1], [5], [(0, [1, 5])]⟩,
  ⟨"destruction invalidates dormant aliases", twoAliases ++ [.destroy 0], [], []⟩,
  ⟨"release before destruction", twoCells ++
    [.reserve 0 0 .exclusive, .writeView 0 4, .release 0, .destroy 0], [], []⟩,
  ⟨"destruction frames another allocation", [.alloc 0 [1], .alloc 1 [2],
    .alias 0 1 0 .exclusive, .destroy 0, .write 0 7, .read 0], [7], [(1, [7])]⟩,
  ⟨"unrelated owner may be destroyed during view", [.alloc 0 [1], .alloc 1 [2],
    .alias 0 1 0 .exclusive, .reserve 0 0 .exclusive, .destroy 0,
    .writeView 0 8, .release 0], [], [(1, [8])]⟩,
  ⟨"byte values include maximum", [.alloc 0 [255], .alias 0 0 0 .exclusive,
    .read 0, .write 0 0, .read 0], [255, 0], [(0, [0])]⟩,
  ⟨"fresh allocation after destruction", [.alloc 0 [1], .alias 0 0 0 .exclusive,
    .destroy 0, .alloc 1 [2], .alias 0 1 0 .exclusive, .read 0], [2], [(1, [2])]⟩
]

def negatives : List (String × Program) := [
  ("read unknown handle", [.read 0]),
  ("write unknown handle", [.write 0 2]),
  ("borrow missing owner", [.alias 0 0 0 .shared]),
  ("borrow empty allocation", [.alloc 0 [], .alias 0 0 0 .shared]),
  ("borrow past last byte", [.alloc 0 [1], .alias 0 0 1 .exclusive]),
  ("borrow far outside allocation", [.alloc 0 [1], .alias 0 0 100 .shared]),
  ("duplicate owner", [.alloc 0 [1], .alloc 0 [2]]),
  ("retired owner ID cannot resurrect", [.alloc 0 [1], .destroy 0, .alloc 0 [2]]),
  ("duplicate handle", twoAliases ++ [.alias 0 0 1 .exclusive]),
  ("read through forgotten handle", twoAliases ++ [.forget 0, .read 0]),
  ("read through invalidated handle", twoAliases ++ [.destroy 0, .read 0]),
  ("write through invalidated handle", twoAliases ++ [.destroy 0, .write 1 4]),
  ("alias cannot target destroyed owner", twoAliases ++ [.destroy 0, .alias 2 0 0 .shared]),
  ("shared handle cannot write", [.alloc 0 [1], .alias 0 0 0 .shared, .write 0 4]),
  ("shared handle cannot reserve exclusive view", [.alloc 0 [1],
    .alias 0 0 0 .shared, .reserve 0 0 .exclusive]),
  ("alias read blocked by exclusive view", twoAliases ++
    [.reserve 0 0 .exclusive, .read 1, .release 0]),
  ("origin handle read also blocked by exclusive view", twoAliases ++
    [.reserve 0 0 .exclusive, .read 0, .release 0]),
  ("alias write blocked by exclusive view", twoAliases ++
    [.reserve 0 0 .exclusive, .write 1 7, .release 0]),
  ("second exclusive reservation conflicts", twoAliases ++
    [.reserve 0 0 .exclusive, .reserve 1 1 .exclusive, .release 0, .release 1]),
  ("shared reservation conflicts with exclusive", twoAliases ++
    [.reserve 0 0 .exclusive, .reserve 1 1 .shared, .release 0, .release 1]),
  ("exclusive reservation conflicts with shared", twoAliases ++
    [.reserve 0 0 .shared, .reserve 1 1 .exclusive, .release 0, .release 1]),
  ("shared view cannot write", twoAliases ++
    [.reserve 0 0 .shared, .writeView 0 7, .release 0]),
  ("shared reservation blocks alias writes", twoAliases ++
    [.reserve 0 0 .shared, .write 1 7, .release 0]),
  ("duplicate view ID", twoCells ++
    [.reserve 0 0 .shared, .reserve 0 1 .shared, .release 0]),
  ("read after view release", twoCells ++
    [.reserve 0 0 .shared, .release 0, .readView 0]),
  ("write after view release", twoCells ++
    [.reserve 0 0 .exclusive, .release 0, .writeView 0 1]),
  ("unreleased view rejected at program end", twoCells ++ [.reserve 0 0 .shared]),
  ("destruction blocked by shared reservation", twoCells ++
    [.reserve 0 0 .shared, .destroy 0, .release 0]),
  ("destruction blocked by exclusive reservation", twoCells ++
    [.reserve 0 0 .exclusive, .destroy 0, .release 0]),
  ("reserve unknown handle", [.reserve 0 0 .shared]),
  ("read unknown view", [.readView 0]),
  ("write unknown view", [.writeView 0 1]),
  ("release unknown view", [.release 0]),
  ("forget unknown handle", [.forget 0]),
  ("destroy unknown owner", [.destroy 0]),
  ("double destruction", [.alloc 0 [], .destroy 0, .destroy 0])
]

def runTests : IO Unit := do
  for fixture in positives do
    unless verifyResources fixture.program do
      throw (IO.userError s!"static resource checker rejected: {fixture.name}")
    match checkClosed fixture.program with
    | none => throw (IO.userError s!"resource core rejected: {fixture.name}")
    | some final =>
      unless final.observations.reverse == fixture.observations do
        throw (IO.userError s!"wrong observations: {fixture.name}")
      unless final.allocations.length == fixture.heap.length &&
          fixture.heap.all (fun (owner, bytes) =>
            (final.allocation owner).map Allocation.bytes == some bytes) do
        throw (IO.userError s!"wrong final heap: {fixture.name}")
  for (name, program) in negatives do
    if verifyResources program then
      throw (IO.userError s!"static resource checker accepted: {name}")
    unless (checkClosed program).isNone do
      throw (IO.userError s!"resource core accepted invalid program: {name}")
  IO.println s!"{positives.length} positive and {negatives.length} negative resource-kernel programs passed"

end Aethel.Core.Tests
