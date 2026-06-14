import Leancremental
import Tests.Util

/-! Executable examples for QUERIES.md.

  Each function corresponds to a code snippet in that doc. Running `runAll`
  through the test executable verifies that every snippet compiles and produces
  the expected result.
-/

namespace Leancremental
namespace Tests
namespace QueriesExamples

def memoTableExample : IO (Nat × Nat × Nat) := do
  let state <- State.create
  let input <- Var.create state 1
  let computeCount <- IO.mkRef 0
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let first <- MemoTable.getOrCreate table "parse:file.lean" (fun _ => do
    computeCount.modify (fun count => count + 1)
    map (Var.watch input) (fun value => value + 1))
  let second <- MemoTable.getOrCreate table "parse:file.lean" (fun _ => do
    computeCount.modify (fun count => count + 1)
    const state 999)
  let observer <- observe second
  State.stabilize state
  pure (← Observer.value! observer, ← computeCount.get, first.id)

def memoScopeExample : IO (Nat × Nat) := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let _shared <- MemoTable.getOrCreate table "file:shared" (fun _ => const state 1)
  let scope <- MemoScope.create table
  let _hover <- MemoScope.getOrCreate scope "request:hover" (fun _ => const state 2)
  let _diagnostics <- MemoScope.getOrCreate scope "request:diagnostics" (fun _ => const state 3)
  let removed <- MemoScope.clear scope
  pure (removed, ← MemoTable.size table)

def staleValueExample : IO (Option Nat × Nat) := do
  let state <- State.create
  let input <- Var.create state 1
  let result <- map (Var.watch input) (fun value => value + 1)
  let observer <- observe result
  State.stabilize state
  Var.set input 10
  let stale <- Incr.staleValue? result
  State.stabilize state
  pure (stale, ← Observer.value! observer)

def stabilizeStatsExample : IO (Nat × Nat × Nat) := do
  let state <- State.create
  let input <- Var.create state 1
  let result <- map (Var.watch input) (fun value => value + 1)
  let _observer <- observe result
  let stats <- State.stabilizeWithStats state
  pure (stats.stabilization, stats.nodesStabilized, stats.activeObservers)

def budgetedStabilizationExample : IO Nat := do
  let state <- State.create
  let input <- Var.create state 1
  let plusOne <- map (Var.watch input) (fun value => value + 1)
  let doubled <- map plusOne (fun value => value * 2)
  let observer <- observe doubled
  let first <- State.stabilizeWithBudget state 1
  if first.completed then
    throw (IO.userError "budgeted stabilization completed too early")
  let _second <- State.stabilizeWithBudget state 1
  Observer.value! observer

def indexedAggregateExample : IO Nat := do
  let state <- State.create
  let first <- Var.create state 1
  let second <- Var.create state 2
  let aggregate <- IndexedAggregate.create (κ := String) state 0 (fun acc _key value => acc + value)
  IndexedAggregate.insertOrReplace aggregate "first" (Var.watch first)
  IndexedAggregate.insertOrReplace aggregate "second" (Var.watch second)
  let observer <- observe (IndexedAggregate.watch aggregate)
  State.stabilize state
  Var.set first 10
  State.stabilize state
  Observer.value! observer

def resultExample : IO (Except String Nat) := do
  let state <- State.create
  let parsed <- IncrResult.ok (ε := String) state 2
  let checked <- IncrResult.bind parsed (fun value => IncrResult.ok (ε := String) state (value + 3))
  let observer <- observe checked
  State.stabilize state
  Observer.value! observer

def documentVersionExample : IO (Except String Nat) := do
  let state <- State.create
  let doc <- Document.create state 10
  let snapshot <- Document.snapshot doc
  let stale <- const state { version := snapshot.version, value := snapshot.content + 1 }
  let currentOnly <- Document.requireCurrent doc stale
  let observer <- observe currentOnly
  let _nextVersion <- Document.edit doc (fun value => value + 10)
  State.stabilize state
  Observer.value! observer

def documentRequestTokenExample : IO Bool := do
  let state <- State.create
  let doc <- Document.create state 10
  let token <- Document.requestToken doc 7
  let _nextVersion <- Document.edit doc (fun value => value + 10)
  Document.requestIsCurrent doc token

/-- Run all checked query examples and validate their expected outputs. -/
def runAll : IO Unit := do
  let memoResult <- memoTableExample
  if memoResult.1 == 2 && memoResult.2.1 == 1 then pure () else throw (IO.userError "memo table example failed")
  assertEq "memo scope example" (← memoScopeExample) (2, 1)
  assertEq "stale value example" (← staleValueExample) (some 2, 11)
  assertEq "stabilize stats example" (← stabilizeStatsExample) (1, 1, 1)
  assertEq "budgeted stabilization example" (← budgetedStabilizationExample) 4
  assertEq "indexed aggregate example" (← indexedAggregateExample) 12
  assertOk "result example" (← resultExample) 5
  assertError "document version example" (← documentVersionExample)
    "stale result for document version 0, current version is 1"
  assertEq "document request token example" (← documentRequestTokenExample) false

end QueriesExamples
end Tests
end Leancremental
