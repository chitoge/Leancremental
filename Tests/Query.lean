import Leancremental
import Tests.Util

/-! Query/LSP-oriented regression tests. -/

namespace Leancremental
namespace Tests
namespace Query

def testQueryPrimitives : IO Unit := do
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
  assertEq "memo hit returns same node" first.id second.id
  assertEq "memo compute runs once" (← computeCount.get) 1
  assertEq "memo table size after hit" (← MemoTable.size table) 1
  let observer <- observe first
  let initialStats <- State.stabilizeWithStats state
  assertEq "memo value" (← Observer.value! observer) 2
  assertEq "stats stabilization number" initialStats.stabilization 1
  assertEq "stats active observers" initialStats.activeObservers 1
  assertEq "stats heap drained" initialStats.remainingRecomputeEntries 0
  Var.set input 10
  assertEq "stale cached value before restabilize" (← Incr.staleValue? first) (some 2)
  assertEq "input is stale before restabilize" (← Incr.isStale (Var.watch input)) true
  let updateStats <- State.stabilizeWithStats state
  assertEq "updated memo value" (← Observer.value! observer) 11
  assertEq "stats changed nodes" updateStats.nodesChanged 2
  let other <- MemoTable.getOrCreate table "parse:other.lean" (fun _ => const state 7)
  assertEq "memo miss allocates distinct node" (first.id == other.id) false
  assertEq "memo table size after miss" (← MemoTable.size table) 2

def testMemoLifecycle : IO Unit := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let computeCount <- IO.mkRef 0
  let first <- MemoTable.getOrCreate table "file:a" (fun _ => do
    computeCount.modify (fun count => count + 1)
    const state 1)
  assertEq "memo lifecycle initial size" (← MemoTable.size table) 1
  assertEq "memo invalidates missing key" (← MemoTable.invalidate table "missing") false
  assertEq "memo invalidates existing key" (← MemoTable.invalidate table "file:a") true
  let second <- MemoTable.getOrCreate table "file:a" (fun _ => do
    computeCount.modify (fun count => count + 1)
    const state 2)
  assertEq "memo invalidation allocates fresh node" (first.id == second.id) false
  assertEq "memo invalidation recomputes" (← computeCount.get) 2
  let _b <- MemoTable.getOrCreate table "file:b" (fun _ => const state 3)
  let _c <- MemoTable.getOrCreate table "file:c" (fun _ => const state 4)
  let removedMatching <- MemoTable.invalidateMatching table (fun key => key == "file:b")
  assertEq "memo predicate invalidation count" removedMatching 1
  assertEq "memo predicate invalidation size" (← MemoTable.size table) 2
  let scope <- MemoScope.create table
  let _hover <- MemoScope.getOrCreate scope "request:hover" (fun _ => const state 10)
  let _diagnostics <- MemoScope.getOrCreate scope "request:diagnostics" (fun _ => const state 20)
  let _hoverAgain <- MemoScope.getOrCreate scope "request:hover" (fun _ => const state 999)
  assertEq "memo scope records unique keys" (← MemoScope.ownedKeys scope).size 2
  assertEq "memo scope grows table" (← MemoTable.size table) 4
  assertEq "memo scope clear count" (← MemoScope.clear scope) 2
  assertEq "memo scope clear resets owned keys" (← MemoScope.ownedKeys scope).size 0
  assertEq "memo scope leaves unrelated keys" (← MemoTable.size table) 2
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun value => value + 1)
  let z <- map y (fun value => value * 2)
  let _observer <- observe z
  let partialSlice <- State.stabilizeWithBudget state 1
  assertEq "memo mutation guard starts partial" partialSlice.completed false
  let blocked <-
    try
      let _removed <- MemoTable.clear table
      pure false
    catch _ =>
      pure true
  assertEq "memo mutation blocked during partial stabilization" blocked true
  State.cancelStabilization state

def testBudgetedStabilization : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun value => value + 1)
  let z <- map y (fun value => value * 2)
  let observer <- observe z
  let firstSlice <- State.stabilizeWithBudget state 1
  assertEq "initial budget slice incomplete" firstSlice.completed false
  assertEq "initial budget leaves observer empty" (← Observer.value? observer) none
  let secondSlice <- State.stabilizeWithBudget state 1
  assertEq "initial budget completes" secondSlice.completed true
  assertEq "initial budgeted value" (← Observer.value! observer) 4
  Var.set x 10
  let updateVar <- State.stabilizeWithBudget state 1
  assertEq "update first slice incomplete" updateVar.completed false
  assertEq "observer not refreshed mid budget" (← Observer.value! observer) 4
  let updateMap <- State.stabilizeWithBudget state 1
  assertEq "update second slice incomplete" updateMap.completed false
  let updateDone <- State.stabilizeWithBudget state 1
  assertEq "update budget completes" updateDone.completed true
  assertEq "budgeted updated value" (← Observer.value! observer) 22
  Var.set x 20
  let canceled <- State.stabilizeWithBudget state 1
  assertEq "cancel test starts partial" canceled.completed false
  State.cancelStabilization state
  assertEq "cancel clears partial" (← State.hasPartialStabilization state) false
  Var.set x 30
  State.stabilize state
  assertEq "full stabilize after cancel" (← Observer.value! observer) 62

def testBudgetedBindKeepsEpoch : IO Unit := do
  let state <- State.create
  let useLeft <- Var.create state true
  let left <- Var.create state 1
  let right <- Var.create state 10
  let selected <- ifThenElse (Var.watch useLeft) (Var.watch left) (Var.watch right)
  let observer <- observe selected
  State.stabilize state
  assertEq "budgeted bind initial" (← Observer.value! observer) 1
  Var.set useLeft false
  let selectorSlice <- State.stabilizeWithBudget state 1
  assertEq "budgeted bind selector slice incomplete" selectorSlice.completed false
  let bindSlice <- State.stabilizeWithBudget state 1
  assertEq "budgeted bind reuses stabilization epoch" bindSlice.stats.stabilization selectorSlice.stats.stabilization
  let doneSlice <- State.stabilizeWithBudget state 1
  assertEq "budgeted bind completes" doneSlice.completed true
  assertEq "budgeted bind switched branch" (← Observer.value! observer) 10

def testIndexedAggregate : IO Unit := do
  let state <- State.create
  let a <- Var.create state 1
  let b <- Var.create state 2
  let c <- Var.create state 5
  let aggregate <- IndexedAggregate.create (κ := String) state 0 (fun acc _key value => acc + value)
  IndexedAggregate.insertOrReplace aggregate "a" (Var.watch a)
  IndexedAggregate.insertOrReplace aggregate "b" (Var.watch b)
  let observer <- observe (IndexedAggregate.watch aggregate)
  State.stabilize state
  assertEq "indexed aggregate initial" (← Observer.value! observer) 3
  Var.set a 10
  State.stabilize state
  assertEq "indexed aggregate input update" (← Observer.value! observer) 12
  IndexedAggregate.insertOrReplace aggregate "b" (Var.watch c)
  State.stabilize state
  assertEq "indexed aggregate replace" (← Observer.value! observer) 15
  assertEq "indexed aggregate remove missing" (← IndexedAggregate.remove aggregate "missing") false
  assertEq "indexed aggregate remove" (← IndexedAggregate.remove aggregate "a") true
  State.stabilize state
  assertEq "indexed aggregate after remove" (← Observer.value! observer) 5
  assertEq "indexed aggregate clear count" (← IndexedAggregate.clear aggregate) 1
  State.stabilize state
  assertEq "indexed aggregate after clear" (← Observer.value! observer) 0
  IndexedAggregate.insertOrReplace aggregate "a" (Var.watch a)
  State.stabilize state
  Var.set a 20
  let partialSlice <- State.stabilizeWithBudget state 1
  assertEq "indexed aggregate guard starts partial" partialSlice.completed false
  let blocked <-
    try
      IndexedAggregate.insertOrReplace aggregate "c" (Var.watch c)
      pure false
    catch _ =>
      pure true
  assertEq "indexed aggregate mutation blocked during partial stabilization" blocked true
  State.cancelStabilization state

def testIncrResult : IO Unit := do
  let state <- State.create
  let okNode <- IncrResult.ok (ε := String) state 2
  let mapped <- IncrResult.map okNode (fun value => value * 3)
  let bound <- IncrResult.bind okNode (fun value => IncrResult.ok (ε := String) state (value + 5))
  let errorNode <- IncrResult.error (α := Nat) state "parse failed"
  let mappedError <- IncrResult.map errorNode (fun value => value * 10)
  let recovered <- IncrResult.recover errorNode (fun _ => IncrResult.ok (ε := String) state 7)
  let combined <- IncrResult.map2 mapped recovered (fun left right => left + right)
  let valueProjection <- IncrResult.value? mapped
  let errorProjection <- IncrResult.error? mappedError
  Incr.setCutoff mapped IncrResult.cutoffOfEq
  let mappedObserver <- observe mapped
  let boundObserver <- observe bound
  let errorObserver <- observe mappedError
  let recoveredObserver <- observe recovered
  let combinedObserver <- observe combined
  let valueObserver <- observe valueProjection
  let errorTextObserver <- observe errorProjection
  State.stabilize state
  assertOk "result map ok" (← Observer.value! mappedObserver) 6
  assertOk "result bind ok" (← Observer.value! boundObserver) 7
  assertError "result map preserves error" (← Observer.value! errorObserver) "parse failed"
  assertOk "result recover" (← Observer.value! recoveredObserver) 7
  assertOk "result map2" (← Observer.value! combinedObserver) 13
  assertEq "result value projection" (← Observer.value! valueObserver) (some 6)
  assertEq "result error projection" (← Observer.value! errorTextObserver) (some "parse failed")

def testDocumentVersioning : IO Unit := do
  let state <- State.create
  let doc <- Document.create state 10
  let query <- map (Document.watchContent doc) (fun value => value + 1)
  let tagged <- Document.tag doc query
  let currentOnly <- Document.requireCurrent doc tagged
  let taggedObserver <- observe tagged
  let currentObserver <- observe currentOnly
  State.stabilize state
  assertEq "document tagged initial" (← Observer.value! taggedObserver) ({ version := 0, value := 11 } : Document.Versioned Nat)
  assertOk "document current initial" (← Observer.value! currentObserver) 11
  let token <- Document.requestToken doc 42
  let newVersion <- Document.edit doc (fun value => value + 10)
  assertEq "document edit version" newVersion 1
  assertEq "document stale tagged value" (← Incr.staleValue? tagged) (some ({ version := 0, value := 11 } : Document.Versioned Nat))
  assertEq "document token becomes stale" (← Document.requestIsCurrent doc token) false
  State.stabilize state
  assertEq "document tagged after edit" (← Observer.value! taggedObserver) ({ version := 1, value := 21 } : Document.Versioned Nat)
  assertOk "document current after edit" (← Observer.value! currentObserver) 21
  let snapshot <- Document.snapshot doc
  assertEq "document snapshot" snapshot ({ version := 1, content := 20 } : Document.Snapshot Nat)
  let staleResult <- const state ({ version := 0, value := 999 } : Document.Versioned Nat)
  let rejected <- Document.requireCurrent doc staleResult
  let rejectedObserver <- observe rejected
  State.stabilize state
  assertError "document rejects stale result" (← Observer.value! rejectedObserver) "stale result for document version 0, current version is 1"

def runAll : IO Unit := do
  testQueryPrimitives
  testMemoLifecycle
  testBudgetedStabilization
  testBudgetedBindKeepsEpoch
  testIndexedAggregate
  testIncrResult
  testDocumentVersioning

end Query
end Tests
end Leancremental
