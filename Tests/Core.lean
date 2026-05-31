import Leancremental
import Tests.Util

/-! Core runtime regression tests. -/

namespace Leancremental
namespace Tests
namespace Core

def testMap2 : IO Unit := do
  let state <- State.create
  let x <- Var.create state 13
  let y <- Var.create state 17
  let z <- map2 (Var.watch x) (Var.watch y) (fun x y => x + y)
  let observer <- observe z
  State.stabilize state
  assertEq "initial sum" (← Observer.value! observer) 30
  Var.set x 19
  State.stabilize state
  assertEq "updated sum" (← Observer.value! observer) 36

def testHigherArityMaps : IO Unit := do
  let state <- State.create
  let a <- Var.create state 1
  let b <- Var.create state 2
  let c <- Var.create state 3
  let d <- Var.create state 4
  let e <- Var.create state 5
  let three <- map3 (Var.watch a) (Var.watch b) (Var.watch c) (fun a b c => a + b + c)
  let four <- map4 (Var.watch a) (Var.watch b) (Var.watch c) (Var.watch d) (fun a b c d => a + b + c + d)
  let five <- map5 (Var.watch a) (Var.watch b) (Var.watch c) (Var.watch d) (Var.watch e) (fun a b c d e => a + b + c + d + e)
  let threeObserver <- observe three
  let fourObserver <- observe four
  let fiveObserver <- observe five
  State.stabilize state
  assertEq "map3 initial" (← Observer.value! threeObserver) 6
  assertEq "map4 initial" (← Observer.value! fourObserver) 10
  assertEq "map5 initial" (← Observer.value! fiveObserver) 15
  Var.set c 30
  State.stabilize state
  assertEq "map3 updated" (← Observer.value! threeObserver) 33
  assertEq "map4 updated" (← Observer.value! fourObserver) 37
  assertEq "map5 updated" (← Observer.value! fiveObserver) 42

def testCutoff : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let doubled <- map (Var.watch x) (fun n => n * 2)
  Incr.setCutoff doubled Cutoff.ofEq
  let observer <- observe doubled
  let updates <- IO.mkRef #[]
  Observer.onUpdate observer (fun update => do updates.modify (fun values => values.push update))
  State.stabilize state
  Var.set x 1
  State.stabilize state
  assertEq "cutoff suppresses unchanged updates" (← updates.get).size 1
  Var.set x 2
  State.stabilize state
  assertEq "cutoff allows changed updates" (← Observer.value! observer) 4
  assertEq "cutoff changed update count" (← updates.get).size 2

def testBindAndBranch : IO Unit := do
  let state <- State.create
  let useLeft <- Var.create state true
  let left <- Var.create state 10
  let right <- Var.create state 100
  let selected <- ifThenElse (Var.watch useLeft) (Var.watch left) (Var.watch right)
  let observer <- observe selected
  State.stabilize state
  assertEq "branch starts on left" (← Observer.value! observer) 10
  Var.set right 101
  State.stabilize state
  assertEq "inactive branch does not affect value" (← Observer.value! observer) 10
  Var.set useLeft false
  State.stabilize state
  assertEq "branch switches right" (← Observer.value! observer) 101
  Var.set right 102
  State.stabilize state
  assertEq "active branch updates" (← Observer.value! observer) 102

def testFold : IO Unit := do
  let state <- State.create
  let a <- Var.create state 1
  let b <- Var.create state 2
  let c <- Var.create state 3
  let total <- sumNat state #[Var.watch a, Var.watch b, Var.watch c]
  let observer <- observe total
  State.stabilize state
  assertEq "initial fold" (← Observer.value! observer) 6
  Var.replace b (fun value => value + 10)
  State.stabilize state
  assertEq "updated fold" (← Observer.value! observer) 16

def testDependOnAndSums : IO Unit := do
  let state <- State.create
  let x <- Var.create state 10
  let dependency <- Var.create state 20
  let dependencyEvents <- IO.mkRef #[]
  Incr.onObservabilityChange (Var.watch dependency) (fun isNecessary => do
    dependencyEvents.modify (fun events => events.push isNecessary))
  let valueWithDependency <- dependOn (Var.watch x) (Var.watch dependency)
  let dependencyObserver <- observe valueWithDependency
  State.stabilize state
  assertEq "dependOn initial value" (← Observer.value! dependencyObserver) 10
  assertEq "dependOn makes dependency necessary" (← dependencyEvents.get) #[true]
  Var.set dependency 99
  State.stabilize state
  assertEq "dependOn ignores dependency value" (← Observer.value! dependencyObserver) 10
  Observer.disallowFutureUse dependencyObserver
  State.stabilize state
  assertEq "dependOn releases dependency" (← dependencyEvents.get) #[true, false]
  let n1 <- Var.create state 1
  let n2 <- Var.create state 2
  let n3 <- Var.create state 3
  let genericTotal <- sum state #[Var.watch n1, Var.watch n2, Var.watch n3]
  let genericObserver <- observe genericTotal
  let f1 <- Var.create state 1.5
  let f2 <- Var.create state 2.25
  let floatTotal <- sumFloat state #[Var.watch f1, Var.watch f2]
  let floatObserver <- observe floatTotal
  State.stabilize state
  assertEq "generic sum" (← Observer.value! genericObserver) 6
  assertEq "float sum" (← Observer.value! floatObserver) 3.75

def testFreeze : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let doubled <- map (Var.watch x) (fun n => n * 2)
  let frozen <- freeze doubled
  let observer <- observe frozen
  State.stabilize state
  assertEq "freeze captures initial value" (← Observer.value! observer) 2
  Var.set x 5
  State.stabilize state
  assertEq "freeze ignores later source changes" (← Observer.value! observer) 2
  assertEq "freeze releases source" (← Incr.isNecessary doubled) false
  let y <- Var.create state 1
  let trigger <- Var.create state false
  let frozenWhen <- freezeWhen (Var.watch y) (Var.watch trigger)
  let whenObserver <- observe frozenWhen
  State.stabilize state
  assertEq "freezeWhen starts live" (← Observer.value! whenObserver) 1
  Var.set y 2
  State.stabilize state
  assertEq "freezeWhen follows before trigger" (← Observer.value! whenObserver) 2
  Var.set y 3
  Var.set trigger true
  State.stabilize state
  assertEq "freezeWhen captures trigger value" (← Observer.value! whenObserver) 3
  Var.set y 4
  Var.set trigger false
  State.stabilize state
  assertEq "freezeWhen remains frozen" (← Observer.value! whenObserver) 3

def testObservabilityTransitions : IO Unit := do
  let state <- State.create
  let useLeft <- Var.create state true
  let left <- Var.create state 10
  let right <- Var.create state 20
  let selected <- ifThenElse (Var.watch useLeft) (Var.watch left) (Var.watch right)
  let leftEvents <- IO.mkRef #[]
  let rightEvents <- IO.mkRef #[]
  Incr.onObservabilityChange (Var.watch left) (fun isNecessary => do
    leftEvents.modify (fun events => events.push isNecessary))
  Incr.onObservabilityChange (Var.watch right) (fun isNecessary => do
    rightEvents.modify (fun events => events.push isNecessary))
  let observer <- observe selected
  State.stabilize state
  assertEq "left becomes necessary" (← leftEvents.get) #[true]
  assertEq "right starts unnecessary" (← rightEvents.get) #[]
  Var.set useLeft false
  State.stabilize state
  assertEq "left becomes unnecessary after branch switch" (← leftEvents.get) #[true, false]
  assertEq "right becomes necessary after branch switch" (← rightEvents.get) #[true]
  Observer.disallowFutureUse observer
  State.stabilize state
  assertEq "right becomes unnecessary after observer is removed" (← rightEvents.get) #[true, false]

def testGraphDebugging : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- Var.create state 2
  let z <- map2 (Var.watch x) (Var.watch y) (fun x y => x + y)
  let _observer <- observe z
  State.stabilize state
  let dot <- State.toDot state
  let expected := "digraph Leancremental {\n  n0 [label=\"0 var h=0 necessary=true stale=false\"];\n  n1 [label=\"1 var h=0 necessary=true stale=false\"];\n  n2 [label=\"2 map2 h=1 necessary=true stale=false\"];\n  n0 -> n2;\n  n1 -> n2;\n}"
  assertEq "dot export" dot expected
  assertEq "acyclic graph has no cycle" (← State.detectCycle state) none

def testCoreInvariants : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- Var.create state 2
  let total <- map2 (Var.watch x) (Var.watch y) (fun x y => x + y)
  let observer <- observe total
  State.checkInvariants state
  let beforeStabilize <- State.stableInvariantViolations state
  if beforeStabilize.isEmpty then
    throw (IO.userError "stable invariants should detect stale necessary nodes before stabilization")
  State.stabilize state
  State.checkStableInvariants state
  assertEq "invariant observer value" (← Observer.value! observer) 3
  Var.set x 10
  State.checkInvariants state
  State.stabilize state
  State.checkStableInvariants state
  assertEq "updated invariant observer value" (← Observer.value! observer) 12

def testCycleDiagnostics : IO Unit := do
  let state <- State.create
  let a <- const state 1
  let b <- const state 2
  Internal.State.setChildren state a.id #[b.id]
  Internal.State.setChildren state b.id #[a.id]
  let cycle <- State.detectCycle state
  assertEq "detects cycle path" cycle (some [a.id, b.id, a.id])
  assertEq "formats cycle path" (State.formatCycle [a.id, b.id, a.id]) "cycle detected: n0 -> n1 -> n0"

def testClock : IO Unit := do
  let state <- State.create
  let clock <- Clock.create state 100
  let boundary <- Clock.atTime clock 105
  let phase <- Clock.stepFunction clock 0 [(100, 1), (110, 2)]
  let tick <- Clock.atIntervals clock 10
  let boundaryObserver <- observe boundary
  let phaseObserver <- observe phase
  let tickObserver <- observe tick
  State.stabilize state
  assertEq "clock starts before boundary" (← Observer.value! boundaryObserver) BeforeOrAfter.before
  assertEq "clock initial step" (← Observer.value! phaseObserver) 1
  assertEq "clock initial interval" (← Observer.value! tickObserver) 10
  Clock.advanceBy clock 5
  State.stabilize state
  assertEq "clock reaches boundary" (← Observer.value! boundaryObserver) BeforeOrAfter.after
  assertEq "clock interval advances" (← Observer.value! tickObserver) 10
  Clock.advanceTo clock 110
  State.stabilize state
  assertEq "clock step advances" (← Observer.value! phaseObserver) 2
  Clock.advanceTo clock 90
  State.stabilize state
  assertEq "clock ignores backwards advance" (← Observer.value! phaseObserver) 2

def testExpertNode : IO Unit := do
  let state <- State.create
  let x <- Var.create state 3
  let changes <- IO.mkRef #[]
  let dependency := Expert.Dependency.create (Var.watch x) (some (fun value => do
    changes.modify (fun values => values.push value)))
  let expert <- Expert.Node.create state (do
    let value <- Expert.Dependency.value dependency
    pure (value * 10))
  Expert.Node.addDependency expert dependency
  let observer <- observe (Expert.Node.watch expert)
  State.stabilize state
  assertEq "expert initial value" (← Observer.value! observer) 30
  assertEq "expert dependency callback is not initial" (← changes.get) #[]
  Var.set x 4
  State.stabilize state
  assertEq "expert updates from dependency" (← Observer.value! observer) 40
  assertEq "expert dependency callback fires" (← changes.get) #[4]

def runAll : IO Unit := do
  testMap2
  testHigherArityMaps
  testCutoff
  testBindAndBranch
  testFold
  testDependOnAndSums
  testFreeze
  testObservabilityTransitions
  testGraphDebugging
  testCoreInvariants
  testCycleDiagnostics
  testClock
  testExpertNode

end Core
end Tests
end Leancremental
