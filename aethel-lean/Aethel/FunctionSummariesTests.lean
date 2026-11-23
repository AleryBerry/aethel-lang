import Aethel.FunctionSummaries

namespace Aethel.FunctionSummaries.Tests

open Functional

def runFunctionSummaries : IO Unit := do
  -- 1. Origin resolution
  let args : List Core.HandleId := [10, 20]
  unless (Origin.param 0).resolve args == some 10 do
    throw (IO.userError "Origin.param 0 resolution failed")
  unless (Origin.param 1).resolve args == some 20 do
    throw (IO.userError "Origin.param 1 resolution failed")
  unless (Origin.param 2).resolve args == none do
    throw (IO.userError "Origin.param 2 out-of-bounds failed")
  unless Origin.global.resolve args == none do
    throw (IO.userError "Origin.global resolution failed")
  unless Origin.fresh.resolve args == none do
    throw (IO.userError "Origin.fresh resolution failed")

  -- 2. Rank-one polymorphism
  let monoScheme : TypeScheme := ⟨0, .mono .nat⟩
  unless monoScheme.instantiate [] == some .nat do
    throw (IO.userError "TypeScheme mono instantiation failed")
  unless monoScheme.instantiate [.bool] == none do
    throw (IO.userError "TypeScheme arity mismatch rejection failed")

  let idScheme : TypeScheme := ⟨1, .arrow (.var 0) (.var 0)⟩
  unless idScheme.instantiate [.byte] == some (.arrow .byte .byte) do
    throw (IO.userError "TypeScheme id instantiation failed")

  let pairScheme : TypeScheme := ⟨2, .arrow (.var 0) (.var 1)⟩
  unless pairScheme.instantiate [.byte, .bool] == some (.arrow .byte .bool) do
    throw (IO.userError "TypeScheme binary instantiation failed")

  -- 3. General ADT definitions and exhaustiveness
  let resultADT : ADTDef := ⟨"Result", [⟨0, "Ok", [.uint16]⟩, ⟨1, "Err", [.byte]⟩]⟩
  unless (resultADT.findVariant 0).isSome do
    throw (IO.userError "ADT variant 0 lookup failed")
  unless (resultADT.findVariant 2).isNone do
    throw (IO.userError "ADT invalid variant lookup failed")
  unless resultADT.isExhaustive [0, 1] == true do
    throw (IO.userError "ADT exhaustive match check failed")
  unless resultADT.isExhaustive [0] == false do
    throw (IO.userError "ADT incomplete match rejection failed")
  unless boolExhaustive true true && !(boolExhaustive true false) do
    throw (IO.userError "Bool exhaustiveness check failed")
  unless optionExhaustive true true && !(optionExhaustive false true) do
    throw (IO.userError "Option exhaustiveness check failed")
  unless resultExhaustive true true && !(resultExhaustive true false) do
    throw (IO.userError "Result exhaustiveness check failed")
  unless intRangeExhaustive 0 100 [(0, 50), (51, 100)] do
    throw (IO.userError "IntRange exhaustive sweep check failed")
  unless !intRangeExhaustive 0 100 [(0, 49), (51, 100)] do
    throw (IO.userError "IntRange gap rejection check failed")

  -- 4. Effect footprints and conflict detection
  let eff1 : Effect := ⟨[[0, 1]], [[0, 2]], []⟩
  let eff2 : Effect := ⟨[[1, 0]], [[1, 1]], []⟩
  let effConflict : Effect := ⟨[[0, 2, 0]], [], []⟩
  unless eff1.reads == [[0, 1]] && eff2.writes == [[1, 1]] && effConflict.reads == [[0, 2, 0]] do
    throw (IO.userError "Effect structure check failed")
  unless Effect.empty.reads.isEmpty do
    throw (IO.userError "Effect.empty failed")
  unless pathConflicts [0, 2] [0, 2, 0] == true do
    throw (IO.userError "pathConflicts prefix detection failed")
  unless pathConflicts [0, 1] [1, 0] == false do
    throw (IO.userError "pathConflicts disjointness detection failed")

  -- 5. Closure ownership and captured resources
  let c : Closure := ⟨[.handle 0, .handle 1], 42⟩
  unless c.handles == [0, 1] do
    throw (IO.userError "Closure.handles projection failed")
  unless c.views.isEmpty do
    throw (IO.userError "Closure.views empty check failed")

  IO.println "12 function summary, origin, and polymorphism regressions passed"

end Aethel.FunctionSummaries.Tests
