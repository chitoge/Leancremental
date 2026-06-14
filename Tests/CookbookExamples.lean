import Leancremental
import Tests.Util

/-!
Checked copies of the executable snippets from `COOKBOOK.md`.
-/

namespace Leancremental
namespace Tests
namespace CookbookExamples

def sumTwo : IO Nat := do
  let state <- State.create
  let x <- Var.create state 10
  let y <- Var.create state 20
  let sum <- map2 (Var.watch x) (Var.watch y) (fun a b => a + b)
  let observer <- observe sum

  State.stabilize state
  Var.set x 15
  State.stabilize state
  Observer.value! observer

def readAfterStabilize : IO (Nat × Nat) := do
  let state <- State.create
  let x <- Var.create state 1
  let doubled <- map (Var.watch x) (fun n => n * 2)
  let observer <- observe doubled

  State.stabilize state
  Var.set x 10
  let before <- Observer.value! observer
  State.stabilize state
  let after <- Observer.value! observer
  pure (before, after)

def switching : IO Nat := do
  let state <- State.create
  let chooseLeft <- Var.create state true
  let left <- Var.create state 7
  let right <- Var.create state 100

  let selected <- ifThenElse (Var.watch chooseLeft) (Var.watch left) (Var.watch right)
  let observer <- observe selected

  State.stabilize state
  Var.set chooseLeft false
  State.stabilize state
  Observer.value! observer

def memoizedQuery : IO (Nat × Bool) := do
  let state <- State.create
  let counter <- IO.mkRef 0
  let table <- MemoTable.create (κ := String) (α := Nat) state

  let first <- MemoTable.getOrCreate table "file:A" (fun _ => do
    counter.modify (fun n => n + 1)
    const state 42)

  let second <- MemoTable.getOrCreate table "file:A" (fun _ => do
    counter.modify (fun n => n + 1)
    const state 99)

  pure (← counter.get, first.id == second.id)

def staleDocumentResult : IO (Except String Nat) := do
  let state <- State.create
  let doc <- Document.create state 10
  let snapshot <- Document.snapshot doc
  let stale <- const state { version := snapshot.version, value := snapshot.content + 1 }
  let currentOnly <- Document.requireCurrent doc stale
  let observer <- observe currentOnly

  let _ <- Document.edit doc (fun n => n + 5)
  State.stabilize state
  Observer.value! observer

def staleRequestToken : IO Bool := do
  let state <- State.create
  let doc <- Document.create state 10
  let token <- Document.requestToken doc 7
  let _ <- Document.edit doc (fun n => n + 5)
  Document.requestIsCurrent doc token

def staleFallback : IO (Option Nat × Nat) := do
  let state <- State.create
  let x <- Var.create state 3
  let doubled <- map (Var.watch x) (fun n => n * 2)
  let observer <- observe doubled

  State.stabilize state
  Var.set x 10
  let oldValue <- Incr.staleValue? doubled
  State.stabilize state
  let newValue <- Observer.value! observer
  pure (oldValue, newValue)

def memoInvalidate : IO (Nat × Bool × Nat) := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let _ <- MemoTable.getOrCreate table "file:A" (fun _ => const state 42)
  let _ <- MemoTable.getOrCreate table "file:B" (fun _ => const state 99)
  let sizeBefore <- MemoTable.size table
  let wasPresent <- MemoTable.invalidate table "file:A"
  let sizeAfter <- MemoTable.size table
  pure (sizeBefore, wasPresent, sizeAfter)

def memoScopeClear : IO (Nat × Nat × Nat) := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := Nat) state
  let _ <- MemoTable.getOrCreate table "shared:base" (fun _ => const state 0)
  let scope <- MemoScope.create table
  let _ <- MemoScope.getOrCreate scope "request:hover" (fun _ => const state 1)
  let _ <- MemoScope.getOrCreate scope "request:diagnostics" (fun _ => const state 2)
  let before <- MemoTable.size table
  let removed <- MemoScope.clear scope
  let after <- MemoTable.size table
  pure (before, removed, after)

def memoCodecRoundtrip : IO (Option String) := do
  let state <- State.create
  let table <- MemoTable.create (κ := String) (α := String) state
  let node <- MemoTable.getOrCreate table "file:A" (fun _ => const state "hello")
  let obs <- observe node
  State.stabilize state
  let _ <- Observer.value! obs

  let snapStore <- MemoSnapshotStore.hashMap (κ := String) (σ := String)
  let _ <- MemoTable.persistStableValues table snapStore MemoValueCodec.ofJson

  let state2 <- State.create
  let table2 <- MemoTable.create (κ := String) (α := String) state2
  let _ <- MemoTable.preloadConstValues table2 snapStore MemoValueCodec.ofJson

  let node2 <- MemoTable.getOrCreate table2 "file:A" (fun _ => const state2 "fallback")
  let obs2 <- observe node2
  State.stabilize state2
  Observer.value? obs2

def cutoffStop : IO (Nat × Nat) := do
  let state <- State.create
  let x <- Var.create state 1
  let doubled <- map (Var.watch x) (fun n => n * 2) Cutoff.ofEq
  let obs <- observe doubled
  State.stabilize state
  let before <- Observer.value! obs
  Var.set x 1
  State.stabilize state
  let after <- Observer.value! obs
  pure (before, after)

def runAll : IO Unit := do
  assertEq "cookbook sumTwo" (← sumTwo) 35
  assertEq "cookbook readAfterStabilize" (← readAfterStabilize) (2, 20)
  assertEq "cookbook switching" (← switching) 100
  assertEq "cookbook memoizedQuery" (← memoizedQuery) (1, true)
  assertError "cookbook staleDocumentResult" (← staleDocumentResult)
    "stale result for document version 0, current version is 1"
  assertEq "cookbook staleRequestToken" (← staleRequestToken) false
  assertEq "cookbook staleFallback" (← staleFallback) (some 6, 20)
  assertEq "cookbook memoInvalidate" (← memoInvalidate) (2, true, 1)
  assertEq "cookbook memoScopeClear" (← memoScopeClear) (3, 2, 1)
  assertEq "cookbook memoCodecRoundtrip" (← memoCodecRoundtrip) (some "hello")
  assertEq "cookbook cutoffStop" (← cutoffStop) (2, 2)

end CookbookExamples
end Tests
end Leancremental
