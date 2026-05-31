import Leancremental
import Tests.Util

/-!
Checked copies of the executable snippets from `TUTORIAL.md`.

The test executable calls `Leancremental.Tests.TutorialExamples.runAll`, so edits
to tutorial code can be mirrored here and verified by `lake exe tests` without
adding examples to the public library namespace.
-/

namespace Leancremental
namespace Tests
namespace TutorialExamples

def prism : IO Float := do
  let state <- State.create

  let width <- Var.create state 3.0
  let depth <- Var.create state 5.0
  let height <- Var.create state 4.0

  let baseArea <- map2 (Var.watch width) (Var.watch depth) (fun w d => w * d)
  let volume <- map2 baseArea (Var.watch height) (fun area h => area * h)

  let volumeObserver <- observe volume
  State.stabilize state
  let first <- Observer.value! volumeObserver

  Var.set height 10.0
  let stillOld <- Observer.value! volumeObserver
  State.stabilize state
  let updated <- Observer.value! volumeObserver

  if first == 60.0 && stillOld == 60.0 then
    pure updated
  else
    throw (IO.userError "unexpected prism state")

def higherArityExample : IO Nat := do
  let state <- State.create
  let a <- Var.create state 1
  let b <- Var.create state 2
  let c <- Var.create state 3
  let d <- Var.create state 4
  let e <- Var.create state 5
  let total <- map5 (Var.watch a) (Var.watch b) (Var.watch c) (Var.watch d) (Var.watch e)
    (fun a b c d e => a + b + c + d + e)
  let observer <- observe total
  State.stabilize state
  Observer.value! observer

def necessaryExample : IO (Bool × Bool) := do
  let state <- State.create
  let x <- Var.create state 1
  let doubled <- map (Var.watch x) (fun n => n * 2)

  let before <- Incr.isNecessary doubled
  let _observer <- observe doubled
  State.stabilize state
  let after <- Incr.isNecessary doubled

  pure (before, after)

def observabilityExample : IO (Array Bool) := do
  let state <- State.create
  let x <- Var.create state 1
  let events <- IO.mkRef #[]

  Incr.onObservabilityChange (Var.watch x) (fun necessary =>
    events.modify (fun xs => xs.push necessary))

  let observer <- observe (Var.watch x)
  State.stabilize state
  Observer.disallowFutureUse observer
  State.stabilize state

  events.get

def cutoffExample : IO Nat := do
  let state <- State.create
  let x <- Var.create state 1
  let doubled <- map (Var.watch x) (fun n => n * 2)
  Incr.setCutoff doubled Cutoff.ofEq

  let observer <- observe doubled
  State.stabilize state
  Var.set x 1
  State.stabilize state
  Observer.value! observer

def branchExample : IO Nat := do
  let state <- State.create
  let useLeft <- Var.create state true
  let left <- Var.create state 10
  let right <- Var.create state 100

  let selected <- ifThenElse (Var.watch useLeft) (Var.watch left) (Var.watch right)
  let observer <- observe selected
  State.stabilize state

  Var.set right 101
  State.stabilize state
  let unchanged <- Observer.value! observer

  Var.set useLeft false
  State.stabilize state
  let switched <- Observer.value! observer

  if unchanged == 10 then pure switched else throw (IO.userError "bad branch")

def averagePrefix (state : State) (values : Array (Incr Nat)) (length : Incr Nat) : IO (Incr Nat) :=
  bind length (fun n => do
    let count := Nat.min n values.size
    let selected := values.extract 0 count
    let total <- sumNat state selected
    map total (fun sum => if count == 0 then 0 else sum / count))

def averagePrefixExample : IO Nat := do
  let state <- State.create
  let a <- Var.create state 4
  let b <- Var.create state 8
  let c <- Var.create state 12
  let length <- Var.create state 2
  let avg <- averagePrefix state #[Var.watch a, Var.watch b, Var.watch c] (Var.watch length)
  let observer <- observe avg
  State.stabilize state
  assertEq "initial average prefix" (← Observer.value! observer) 6
  Var.set length 3
  State.stabilize state
  Observer.value! observer

def foldExample : IO Nat := do
  let state <- State.create
  let a <- Var.create state 1
  let b <- Var.create state 2
  let c <- Var.create state 3
  let total <- sumNat state #[Var.watch a, Var.watch b, Var.watch c]
  let observer <- observe total
  State.stabilize state
  Observer.value! observer

def dependOnExample : IO (Nat × Bool) := do
  let state <- State.create
  let value <- Var.create state 10
  let dependency <- Var.create state 20
  let result <- dependOn (Var.watch value) (Var.watch dependency)
  let observer <- observe result
  State.stabilize state
  pure (← Observer.value! observer, ← Incr.isNecessary (Var.watch dependency))

def freezeExample : IO Nat := do
  let state <- State.create
  let x <- Var.create state 1
  let frozen <- freeze (Var.watch x)
  let observer <- observe frozen
  State.stabilize state
  Var.set x 2
  State.stabilize state
  Observer.value! observer

def dotExample : IO String := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- Var.create state 2
  let z <- map2 (Var.watch x) (Var.watch y) (fun x y => x + y)
  let _observer <- observe z
  State.stabilize state
  State.toDot state

def invariantExample : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun n => n + 1)
  let _observer <- observe y
  State.stabilize state
  State.checkStableInvariants state

def clockExample : IO BeforeOrAfter := do
  let state <- State.create
  let clock <- Clock.create state 100
  let boundary <- Clock.atTime clock 105
  let observer <- observe boundary

  State.stabilize state
  Clock.advanceBy clock 5
  State.stabilize state
  Observer.value! observer

def expertExample : IO Nat := do
  let state <- State.create
  let x <- Var.create state 3

  let dependency := Expert.Dependency.create (Var.watch x)
  let expert <- Expert.Node.create state (do
    let value <- Expert.Dependency.value dependency
    pure (value * 10))
  Expert.Node.addDependency expert dependency

  let observer <- observe (Expert.Node.watch expert)
  State.stabilize state
  Observer.value! observer

def pureExample : Nat :=
  let x : Pure.Var Nat := { value := 2 }
  let y : Pure.Var Nat := { value := 3 }
  let expr := Pure.map2 (Pure.Var.watch x) (Pure.Var.watch y) (fun x y => x + y)
  Pure.eval expr

def coreSnapshotExample : Nat :=
  (CoreSnapshot.stableValueSnapshot 5).value

def compiledPureExample : IO Nat := do
  let state <- State.create
  let expr := Pure.map2 (Pure.const 2) (Pure.const 3) (fun x y => x + y)
  let observer <- CoreSnapshot.observeExpr state expr
  State.stabilize state
  Observer.value! observer

def compiledPureFoldExample : IO Nat := do
  let state <- State.create
  let exprs := #[Pure.const 1, Pure.const 2, Pure.const 3]
  let observer <- CoreSnapshot.observeFoldArray state exprs 0 (fun acc value => acc + value)
  State.stabilize state
  Observer.value! observer

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
  let query <- map (Document.watchContent doc) (fun value => value + 1)
  let tagged <- Document.tag doc query
  let currentOnly <- Document.requireCurrent doc tagged
  let observer <- observe currentOnly
  State.stabilize state
  let _nextVersion <- Document.edit doc (fun value => value + 10)
  State.stabilize state
  Observer.value! observer

/-- Run all checked tutorial examples and validate their expected outputs. -/
def runAll : IO Unit := do
  assertEq "prism" (← prism) 150.0
  assertEq "higher arity example" (← higherArityExample) 15
  assertEq "necessary example" (← necessaryExample) (false, true)
  assertEq "observability example" (← observabilityExample) #[true, false]
  assertEq "cutoff example" (← cutoffExample) 2
  assertEq "branch example" (← branchExample) 101
  assertEq "average prefix example" (← averagePrefixExample) 8
  assertEq "fold example" (← foldExample) 6
  assertEq "dependOn example" (← dependOnExample) (10, true)
  assertEq "freeze example" (← freezeExample) 1
  let dot <- dotExample
  if dot.contains "n0 -> n2" && dot.contains "map2" then pure () else throw (IO.userError "dot example did not include expected graph")
  invariantExample
  assertEq "clock example" (← clockExample) BeforeOrAfter.after
  assertEq "expert example" (← expertExample) 30
  assertEq "pure example" pureExample 5
  assertEq "core snapshot example" coreSnapshotExample 5
  assertEq "compiled pure example" (← compiledPureExample) 5
  assertEq "compiled pure fold example" (← compiledPureFoldExample) 6
  let memoResult <- memoTableExample
  if memoResult.1 == 2 && memoResult.2.1 == 1 then pure () else throw (IO.userError "memo table example failed")
  assertEq "memo scope example" (← memoScopeExample) (2, 1)
  assertEq "stale value example" (← staleValueExample) (some 2, 11)
  assertEq "stabilize stats example" (← stabilizeStatsExample) (1, 2, 1)
  assertEq "budgeted stabilization example" (← budgetedStabilizationExample) 4
  assertEq "indexed aggregate example" (← indexedAggregateExample) 12
  assertOk "result example" (← resultExample) 5
  assertOk "document version example" (← documentVersionExample) 21

end TutorialExamples
end Tests
end Leancremental
