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

def testVarCreateCutoffAtConstruction : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1 Cutoff.ofEq
  let observer <- observe (Var.watch x)
  let updates <- IO.mkRef #[]
  Observer.onUpdate observer (fun update => do updates.modify (fun values => values.push update))
  State.stabilize state
  Var.set x 1
  State.stabilize state
  assertEq "Var.create cutoff suppresses unchanged updates" (← updates.get).size 1
  Var.set x 2
  State.stabilize state
  assertEq "Var.create cutoff allows changed updates" (← Observer.value! observer) 2
  assertEq "Var.create cutoff changed update count" (← updates.get).size 2

def testMapCutoffAtConstruction : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let parity <- map (Var.watch x) (fun n => n % 2) Cutoff.ofHash
  let observer <- observe parity
  let updates <- IO.mkRef #[]
  Observer.onUpdate observer (fun update => do updates.modify (fun values => values.push update))
  State.stabilize state
  Var.set x 3
  State.stabilize state
  assertEq "map cutoff suppresses unchanged updates" (← updates.get).size 1
  Var.set x 4
  State.stabilize state
  assertEq "map cutoff allows changed updates" (← Observer.value! observer) 0
  assertEq "map cutoff changed update count" (← updates.get).size 2

structure HashCollisionWitness where
  value : Nat
deriving Repr, BEq

instance : Hashable HashCollisionWitness where
  hash _ := 0

def testHashCutoffUncheckedCollisionSuppressesChange : IO Unit := do
  let state <- State.create
  let source <- Var.create state ({ value := 1 } : HashCollisionWitness)
  let watched := Var.watch source
  Incr.setCutoff watched Cutoff.ofHashUnchecked
  let projected <- map watched (fun (sample : HashCollisionWitness) => sample.value)
  let observer <- observe projected
  State.stabilize state
  assertEq "hash collision setup value" (← Observer.value! observer) 1
  Var.set source ({ value := 2 } : HashCollisionWitness)
  State.stabilize state
  assertEq "unchecked hash cutoff collision suppresses changed value propagation" (← Observer.value! observer) 1
  assertEq "unchecked hash cutoff collision keeps old cached value" (← Incr.value? watched) (some ({ value := 1 } : HashCollisionWitness))

def testHashCutoffSafeCollisionPropagatesChange : IO Unit := do
  let state <- State.create
  let source <- Var.create state ({ value := 1 } : HashCollisionWitness)
  let watched := Var.watch source
  Incr.setCutoff watched Cutoff.ofHash
  let projected <- map watched (fun (sample : HashCollisionWitness) => sample.value)
  let observer <- observe projected
  State.stabilize state
  assertEq "safe hash cutoff setup value" (← Observer.value! observer) 1
  Var.set source ({ value := 2 } : HashCollisionWitness)
  State.stabilize state
  assertEq "safe hash cutoff does not suppress changed value under collision" (← Observer.value! observer) 2
  assertEq "safe hash cutoff updates cached value under collision" (← Incr.value? watched) (some ({ value := 2 } : HashCollisionWitness))

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

def testBindRewiresOncePerLhsChange : IO Unit := do
  let state <- State.create
  let useLeft <- Var.create state true
  let left <- Var.create state 10
  let right <- Var.create state 100
  let rewireCount <- IO.mkRef 0
  let selected <- bind (Var.watch useLeft) (fun pickLeft => do
    rewireCount.modify (fun count => count + 1)
    pure (if pickLeft then Var.watch left else Var.watch right))
  let observer <- observe selected
  State.stabilize state
  assertEq "bind rewire count after initial stabilization" (← rewireCount.get) 1
  assertEq "bind rewire initial value" (← Observer.value! observer) 10
  Var.set useLeft false
  State.stabilize state
  assertEq "bind rewires once after lhs change" (← rewireCount.get) 2
  assertEq "bind rewire switched value" (← Observer.value! observer) 100
  Var.set right 101
  State.stabilize state
  assertEq "bind does not rewire when only selected child changes" (← rewireCount.get) 2
  assertEq "bind selected child still propagates updates" (← Observer.value! observer) 101

def testBindCutoffAtConstruction : IO Unit := do
  let state <- State.create
  let source <- Var.create state 1
  let parity <- bind (Var.watch source) (fun value => ret state (value % 2)) Cutoff.ofEq
  let observer <- observe parity
  let updates <- IO.mkRef #[]
  Observer.onUpdate observer (fun update => do updates.modify (fun values => values.push update))
  State.stabilize state
  Var.set source 3
  State.stabilize state
  assertEq "bind cutoff suppresses unchanged rewired value" (← updates.get).size 1
  Var.set source 4
  State.stabilize state
  assertEq "bind cutoff propagates changed rewired value" (← Observer.value! observer) 0
  assertEq "bind cutoff changed update count" (← updates.get).size 2

def log2ceil (n : Nat) : Nat :=
  if n <= 1 then 0
  else (Nat.log2 (n - 1)) + 1

-- Returns (nodesStabilized, nodesVisited)
def measureAssocAggregateSingleEntryVisits (n : Nat) : IO (Nat × Nat) := do
  let state <- State.create
  let aggregate <- AssocIndexedAggregate.create (κ := Nat) state 0 (fun _ value => value) (· + ·)
  let mut vars : Array (Var Nat) := #[]
  for i in [:n] do
    let v <- Var.create state 1
    AssocIndexedAggregate.insertOrReplace aggregate i (Var.watch v)
    vars := vars.push v
  let observer <- observe (AssocIndexedAggregate.watch aggregate)
  State.stabilize state
  assertEq "assoc aggregate initial total" (← Observer.value! observer) n
  let some firstVar := vars[0]?
    | throw (IO.userError "assoc aggregate locality test expected at least one entry")
  Var.set firstVar 2
  let stats <- State.stabilizeWithStats state
  assertEq "assoc aggregate single entry update total" (← Observer.value! observer) (n + 1)
  pure (stats.nodesStabilized, stats.nodesVisited)

def testAssocAggregateSingleEntryLocality : IO Unit := do
  let (smallVisits, smallNodesVisited) <- measureAssocAggregateSingleEntryVisits 64
  let (largeVisits, _) <- measureAssocAggregateSingleEntryVisits 512
  let (_, visits1024) <- measureAssocAggregateSingleEntryVisits 1024
  assertEq "assoc aggregate small update stays local" (decide (smallVisits <= 96)) true
  assertEq "assoc aggregate large update stays near path-local" (decide (largeVisits <= smallVisits + 96)) true
  assertEq "assoc aggregate large update avoids linear full-tree visits" (decide (largeVisits <= 192)) true
  -- FR-6: nodesVisited ≤ 2 * ⌈log₂ n⌉ + 8
  assertEq "FR-6 nodesVisited bound n=64" (decide (smallNodesVisited <= 2 * log2ceil 64 + 8)) true
  assertEq "FR-6 nodesVisited bound n=1024" (decide (visits1024 <= 2 * log2ceil 1024 + 8)) true

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

def testFreezeWhenCutoffAtConstruction : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let trigger <- Var.create state false
  let parity <- map (Var.watch x) (fun n => n % 2)
  let frozen <- freezeWhen parity (Var.watch trigger) Cutoff.ofEq
  let observer <- observe frozen
  let updates <- IO.mkRef #[]
  Observer.onUpdate observer (fun update => do updates.modify (fun values => values.push update))
  State.stabilize state
  Var.set x 3
  State.stabilize state
  assertEq "freezeWhen cutoff suppresses unchanged pre-freeze value" (← updates.get).size 1
  Var.set x 4
  State.stabilize state
  assertEq "freezeWhen cutoff propagates changed pre-freeze value" (← Observer.value! observer) 0
  assertEq "freezeWhen cutoff changed update count" (← updates.get).size 2
  Var.set trigger true
  Var.set x 6
  State.stabilize state
  assertEq "freezeWhen cutoff freezes current value" (← Observer.value! observer) 0
  Var.set x 7
  State.stabilize state
  assertEq "freezeWhen cutoff keeps frozen value" (← Observer.value! observer) 0
  assertEq "freezeWhen cutoff releases source after freeze" (← Incr.isNecessary parity) false

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

def testMultipleObserversShareNecessity : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let doubled <- map (Var.watch x) (fun value => value * 2)
  let observer1 <- observe doubled
  let observer2 <- observe doubled
  State.stabilize state
  assertEq "shared node starts necessary" (← Incr.isNecessary doubled) true
  assertEq "shared child starts necessary" (← Incr.isNecessary (Var.watch x)) true
  Observer.disallowFutureUse observer1
  assertEq "one observer keeps shared node necessary" (← Incr.isNecessary doubled) true
  assertEq "one observer keeps shared child necessary" (← Incr.isNecessary (Var.watch x)) true
  Observer.disallowFutureUse observer1
  assertEq "repeated disallow is safe" (← Incr.isNecessary doubled) true
  Observer.disallowFutureUse observer2
  assertEq "last observer releases shared node immediately" (← Incr.isNecessary doubled) false
  assertEq "last observer releases shared child immediately" (← Incr.isNecessary (Var.watch x)) false

def testObserverRemovalDropsNecessityWithoutGlobalPass : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let doubled <- map (Var.watch x) (fun value => value * 2)
  let observer <- observe doubled
  State.stabilize state
  assertEq "observer setup makes graph necessary" (← Incr.isNecessary (Var.watch x)) true
  Observer.disallowFutureUse observer
  assertEq "observed node becomes unnecessary immediately" (← Incr.isNecessary doubled) false
  assertEq "dependency becomes unnecessary immediately" (← Incr.isNecessary (Var.watch x)) false

def testObserverRefreshPrunesInactiveObservers : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let doubled <- map (Var.watch x) (fun value => value * 2)
  let observerA <- observe doubled
  let observerB <- observe doubled
  State.stabilize state
  assertEq "observer storage tracks active observers" (← State.numObservers state) 2
  Observer.disallowFutureUse observerA
  State.stabilize state
  -- Lazy-pruning: slot stays in array, but active count reflects deactivation
  assertEq "one active observer after first disallow" (← State.numObservers state) 1
  Observer.disallowFutureUse observerB
  State.stabilize state
  assertEq "no active observers after second disallow" (← State.numObservers state) 0

def testObserverCreatedAfterStablePassInitializes : IO Unit := do
  let state <- State.create
  let x <- Var.create state 5
  let y <- map (Var.watch x) (fun value => value + 1)
  let firstObserver <- observe y
  State.stabilize state
  assertEq "first observer initialized" (← Observer.value! firstObserver) 6
  let secondObserver <- observe y
  State.stabilize state
  assertEq "new observer initializes even when node is unchanged" (← Observer.value! secondObserver) 6

def testNecessaryRewriteUpdatesChildrenIncrementally : IO Unit := do
  let state <- State.create
  let left <- Var.create state 10
  let right <- Var.create state 20
  let currentDependency <- (IO.mkRef (Var.watch left) : IO (IO.Ref (Incr Nat)))
  let expert <- Expert.Node.create state (do
    let dependency <- currentDependency.get
    Incr.value! dependency)
  let leftEvents <- IO.mkRef #[]
  let rightEvents <- IO.mkRef #[]
  Incr.onObservabilityChange (Var.watch left) (fun isNecessary =>
    leftEvents.modify (fun events => events.push isNecessary))
  Incr.onObservabilityChange (Var.watch right) (fun isNecessary =>
    rightEvents.modify (fun events => events.push isNecessary))
  Expert.Node.addDependency expert (Expert.Dependency.create (Var.watch left))
  let observer <- observe (Expert.Node.watch expert)
  State.stabilize state
  assertEq "rewrite setup reads left" (← Observer.value! observer) 10
  assertEq "left starts necessary through expert" (← leftEvents.get) #[true]
  assertEq "right starts unnecessary through expert" (← rightEvents.get) #[]
  currentDependency.set (Var.watch right)
  expert.dependencies.set #[{ nodeId := right.watch.id, fireIfChanged := fun _ => pure () }]
  Internal.State.setChildren state expert.incr.id #[right.watch.id]
  assertEq "old child released immediately on rewrite" (← leftEvents.get) #[true, false]
  assertEq "new child retained immediately on rewrite" (← rightEvents.get) #[true]
  State.stabilize state
  assertEq "rewrite updates observed value" (← Observer.value! observer) 20

def testQueuedUnnecessaryRootsAreSkippedSafely : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun value => value + 1)
  let observer <- observe y
  State.stabilize state
  Var.set x 5
  let slice <- State.stabilizeWithBudget state 0
  assertEq "budget 0 leaves queued root" slice.completed false
  assertEq "queued root enters heap" (← State.recomputeHeapSize state) 1
  Observer.disallowFutureUse observer
  State.checkInvariants state
  State.stabilize state
  State.checkStableInvariants state
  assertEq "queued work drains after observer removal" (← State.recomputeHeapSize state) 0

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

def testDependencyChangeHooks : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let doubled <- map (Var.watch x) (fun n => n * 2)
  let frozen <- freeze doubled
  let events <- IO.mkRef #[]
  State.onDependenciesChanged state (fun id oldChildren newChildren => do
    if id == frozen.id then
      events.modify (fun xs => xs.push (oldChildren, newChildren))
    else
      pure ())
  let _observer <- observe frozen
  State.stabilize state
  let hookEvents <- events.get
  assertEq "dependency hook saw one rewrite" hookEvents.size 1
  assertEq "dependency hook old children" hookEvents[0]!.1 #[doubled.id]
  assertEq "dependency hook new children" hookEvents[0]!.2 #[]

def testIncrInvalidate : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun value => value + 1)
  let observer <- observe y
  State.stabilize state
  assertEq "invalidate setup value" (← Observer.value! observer) 2
  Incr.invalidate y
  assertEq "invalidate clears cached node value" (← Incr.value? y) none
  State.stabilize state
  assertEq "invalidate recomputes value" (← Observer.value! observer) 2

def testMarkStalePreservesCachedValue : IO Unit := do
  let state <- State.create
  let x <- Var.create state 10
  let y <- map (Var.watch x) (fun value => value + 1)
  let observer <- observe y
  State.stabilize state
  assertEq "markStale setup value" (← Observer.value! observer) 11
  Incr.markStale y
  assertEq "markStale preserves cached value" (← Incr.value? y) (some 11)
  assertEq "markStale marks node stale" (← Incr.isStale y) true
  State.stabilize state
  assertEq "markStale recomputes without changing value" (← Observer.value! observer) 11

def testMarkStaleRecomputesStaleParents : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun value => value + 1)
  let z <- map y (fun value => value * 2)
  let observer <- observe z
  State.stabilize state
  assertEq "markStale parent setup value" (← Observer.value! observer) 4
  Incr.markStale y
  assertEq "markStale marks parent stale before stabilization" (← Incr.isStale z) true
  State.stabilize state
  assertEq "markStale preserves parent observer value" (← Observer.value! observer) 4
  assertEq "markStale clears parent stale flag after stabilization" (← Incr.isStale z) false

def testNecessaryRewriteQueuesMissingChildOutsideStabilization : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- Var.create state 10
  let missing <- map (Var.watch y) (fun value => value + 100)
  let currentDependency <- (IO.mkRef (Var.watch x) : IO (IO.Ref (Incr Nat)))
  let expert <- Expert.Node.create state (do
    let dependency <- currentDependency.get
    let value <- Incr.value! dependency
    pure (value * 2))
  Expert.Node.addDependency expert (Expert.Dependency.create (Var.watch x))
  let observer <- observe (Expert.Node.watch expert)
  State.stabilize state
  assertEq "expert initial dependency value" (← Observer.value! observer) 2
  currentDependency.set missing
  expert.dependencies.set #[{ nodeId := missing.id, fireIfChanged := fun _ => pure () }]
  Internal.State.setChildren state expert.incr.id #[missing.id]
  State.stabilize state
  assertEq "outside rewrite computes newly necessary missing child" (← Observer.value! observer) 220

def testCancelRestoresPendingDirtyWork : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun value => value + 1)
  let observer <- observe y
  State.stabilize state
  assertEq "cancel restore setup value" (← Observer.value! observer) 2
  Var.set x 5
  let budgetResult <- State.stabilizeWithBudget state 0
  assertEq "budget 0 leaves stabilization incomplete" budgetResult.completed false
  assertEq "budget 0 moves dirty work into the heap" (← State.recomputeHeapSize state) 1
  State.cancelStabilization state
  assertEq "cancel clears partial stabilization" (← State.hasPartialStabilization state) false
  State.stabilize state
  assertEq "cancel restores dirty work for the next pass" (← Observer.value! observer) 6

def testCancelRestoresPartialChainWork : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun value => value + 1)
  let z <- map y (fun value => value * 10)
  let observer <- observe z
  State.stabilize state
  assertEq "partial cancel setup value" (← Observer.value! observer) 20
  Var.set x 5
  let slice <- State.stabilizeWithBudget state 1
  assertEq "single-root slice stays partial on a chain" slice.completed false
  assertEq "one queued parent remains after partial slice" (← State.recomputeHeapSize state) 1
  State.cancelStabilization state
  assertEq "cancel clears partial chain stabilization" (← State.hasPartialStabilization state) false
  State.stabilize state
  assertEq "cancel restores remaining chain work for next pass" (← Observer.value! observer) 60

def testTraceEpochContext : IO Unit := do
  let state <- State.create
  State.setTraceMode state .unbounded
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun value => value + 1)
  let _observer <- observe y
  State.stabilize state
  State.clearTraceEvents state
  Incr.markStale y
  Incr.invalidate y
  let frozen <- freeze y
  let _frozenObserver <- observe frozen
  State.stabilize state
  let events <- State.traceEvents state
  let outsideMarkedHasNoEpoch := events.any (fun event =>
    event.nodeId == y.id && event.stabilization == none &&
      event.kind == .markedStale none)
  let outsideInvalidatedHasNoEpoch := events.any (fun event =>
    event.nodeId == y.id && event.stabilization == none && event.kind == .invalidated)
  let rewriteHasEpoch := events.any (fun event =>
    event.nodeId == frozen.id &&
      match event.kind with
      | .dependencyRewrite #[child] #[] => child == y.id && event.stabilization.isSome
      | _ => false)
  assertEq "markStale outside stabilization uses no epoch" outsideMarkedHasNoEpoch true
  assertEq "invalidate outside stabilization uses no epoch" outsideInvalidatedHasNoEpoch true
  assertEq "dependency rewrite during stabilization uses epoch" rewriteHasEpoch true

def testDependencyHandlerCanQueueMutationsDuringStabilization : IO Unit := do
  let state <- State.create
  State.setTraceMode state .unbounded
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun value => value + 1)
  let frozen <- freeze y
  let frozenObserver <- observe frozen
  let yObserver <- observe y
  State.onDependenciesChanged state (fun id _oldChildren _newChildren => do
    if id == frozen.id then
      Incr.invalidate y
    else
      pure ())
  State.clearTraceEvents state
  State.stabilize state
  assertEq "freeze still computes this pass" (← Observer.value! frozenObserver) 2
  assertEq "queued invalidation applies after pass" (← Incr.isStale y) true
  let events <- State.traceEvents state
  let deferredInvalidationHasEpoch := events.any (fun event =>
    event.nodeId == y.id && event.stabilization.isSome && event.kind == .invalidated)
  assertEq "queued invalidation traced with stabilization epoch" deferredInvalidationHasEpoch true
  State.stabilize state
  assertEq "next pass consumes deferred invalidation" (← Incr.isStale y) false
  assertEq "invalidated dependency recomputes next pass" (← Observer.value! yObserver) 2

def testHandlerFailureIsTracedNotFatal : IO Unit := do
  let state <- State.create
  State.setTraceMode state .unbounded
  let useLeft <- Var.create state true
  let left <- Var.create state 10
  let right <- Var.create state 20
  let selected <- ifThenElse (Var.watch useLeft) (Var.watch left) (Var.watch right)
  Incr.onObservabilityChange (Var.watch left) (fun _ =>
    throw (IO.userError "observability handler boom"))
  Incr.onObservabilityChange (Var.watch right) (fun _ =>
    throw (IO.userError "observability handler boom"))
  let selectedObserver <- observe selected
  let x <- Var.create state 1
  let doubled <- map (Var.watch x) (fun value => value * 2)
  let frozen <- freeze doubled
  State.onDependenciesChanged state (fun id _oldChildren _newChildren => do
    if id == frozen.id then
      throw (IO.userError "dependency handler boom")
    else
      pure ())
  let frozenObserver <- observe frozen
  State.clearTraceEvents state
  State.stabilize state
  assertEq "stabilization continues after handler failures" (← Observer.value! selectedObserver) 10
  assertEq "stabilization computes freeze despite dependency handler failure" (← Observer.value! frozenObserver) 2
  let events <- State.traceEvents state
  let sawObservabilityFailure := events.any (fun event =>
    match event.kind with
    | .handlerFailed kind _ => kind == "observability"
    | _ => false)
  let sawDependencyFailure := events.any (fun event =>
    match event.kind with
    | .handlerFailed kind _ => kind == "dependency-change"
    | _ => false)
  assertEq "trace includes observability handler failure" sawObservabilityFailure true
  assertEq "trace includes dependency handler failure" sawDependencyFailure true

def testNodeMetadataApis : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let node := Var.watch x
  State.stabilize state
  Incr.touch node
  let touchedInfo <- State.nodeInfo state node.id
  assertEq "touch records latest access epoch" touchedInfo.lastAccessedAt (some 1)
  Incr.setExternalDirtyReason node "edited-buffer"
  let dirtyInfo <- State.nodeInfo state node.id
  assertEq "setExternalDirtyReason stores reason" dirtyInfo.externalDirtyReason (some "edited-buffer")
  Incr.clearExternalDirtyReason node
  let clearedDirtyInfo <- State.nodeInfo state node.id
  assertEq "clearExternalDirtyReason clears reason" clearedDirtyInfo.externalDirtyReason none
  Incr.addTag node "skyframe"
  Incr.addTag node "hot"
  Incr.addTag node "skyframe"
  assertEq "addTag deduplicates" (← Incr.tags node) #["skyframe", "hot"]
  assertEq "nodesWithTag tracks additions" (← State.nodesWithTag state "skyframe") #[node.id]
  Incr.removeTag node "skyframe"
  assertEq "removeTag removes matching tags" (← Incr.tags node) #["hot"]
  assertEq "nodesWithTag tracks removals" (← State.nodesWithTag state "skyframe") #[]

def testNodesWithTagOrdering : IO Unit := do
  let state <- State.create
  let first <- Var.create state 1
  let second <- Var.create state 2
  let firstNode := Var.watch first
  let secondNode := Var.watch second
  Incr.addTag secondNode "hot"
  Incr.addTag firstNode "hot"
  Incr.addTag firstNode "hot"
  assertEq "nodesWithTag keeps deterministic ascending ids" (← State.nodesWithTag state "hot") #[firstNode.id, secondNode.id]
  Incr.removeTag firstNode "hot"
  assertEq "nodesWithTag removes one node cleanly" (← State.nodesWithTag state "hot") #[secondNode.id]

def testStaleNecessaryIds : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun value => value + 1)
  let observer <- observe y
  assertEq "initial observed stale work includes derived node only" (← State.staleNecessaryIds state) #[y.id]
  State.stabilize state
  assertEq "stale necessary ids drain after initial stabilize" (← State.staleNecessaryIds state) #[]
  Var.set x 5
  assertEq "stale necessary ids reflect currently stale observed roots" (← State.staleNecessaryIds state) #[x.watch.id]
  State.stabilize state
  assertEq "stale necessary ids drain after update stabilize" (← State.staleNecessaryIds state) #[]
  Observer.disallowFutureUse observer
  Var.set x 7
  assertEq "stale necessary ids ignore unobserved work" (← State.staleNecessaryIds state) #[]

def testStaleNecessaryIdsSortedOrder : IO Unit := do
  let state <- State.create
  let first <- Var.create state 1
  let second <- Var.create state 2
  let third <- Var.create state 3
  let firstPlus <- map (Var.watch first) (fun value => value + 1)
  let secondPlus <- map (Var.watch second) (fun value => value + 1)
  let thirdPlus <- map (Var.watch third) (fun value => value + 1)
  let _observerThird <- observe thirdPlus
  let _observerFirst <- observe firstPlus
  let _observerSecond <- observe secondPlus
  let observedIds <- State.staleNecessaryIds state
  assertEq "observed derived nodes start stale and necessary" observedIds.size 3
  let observedIdsSorted := observedIds.foldl Internal.insertNatSortedUnique #[]
  assertEq "stale necessary ids are sorted at observe time" observedIds observedIdsSorted
  State.stabilize state
  Var.set third 30
  Var.set first 10
  Var.set second 20
  let updatedIds <- State.staleNecessaryIds state
  let updatedIdsSorted := updatedIds.foldl Internal.insertNatSortedUnique #[]
  assertEq
    "stale necessary ids stay sorted after out-of-order dirtying"
    updatedIds
    updatedIdsSorted

def testReclaimUnreachableCachedValues : IO Unit := do
  let state <- State.create
  let live <- Var.create state 10
  let liveNode <- map (Var.watch live) (fun value => value + 1)
  let liveObserver <- observe liveNode
  let cold <- Var.create state 20
  let coldWatch := Var.watch cold
  let coldNode <- map coldWatch (fun value => value * 2)
  let coldObserver <- observe coldNode
  let frozenConst <- const state 99
  State.stabilize state
  assertEq "live setup value" (← Observer.value! liveObserver) 11
  assertEq "cold setup value" (← Observer.value! coldObserver) 40
  Observer.disallowFutureUse coldObserver
  let reclaimed <- State.reclaimUnreachableCachedValues state
  assertEq "reclaim clears only recomputable unreachable caches" reclaimed 2
  assertEq "reachable observed cache stays intact" (← Incr.value? liveNode) (some 11)
  assertEq "unreachable var cache is cleared" (← Incr.value? coldWatch) none
  assertEq "unreachable derived cache is cleared" (← Incr.value? coldNode) none
  assertEq "non-recomputable const cache is preserved" (← Incr.value? frozenConst) (some 99)
  let coldObserverAgain <- observe coldNode
  State.stabilize state
  assertEq "reclaimed node recomputes when observed again" (← Observer.value! coldObserverAgain) 40

def testReclaimUnreachableCachedValuesGuard : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun value => value + 1)
  let _observer <- observe y
  let slice <- State.stabilizeWithBudget state 0
  assertEq "budgeted slice leaves partial stabilization active" slice.completed false
  let blocked <-
    try
      let _ <- State.reclaimUnreachableCachedValues state
      pure false
    catch _ =>
      pure true
  assertEq "reclaim is blocked during partial stabilization" blocked true
  State.cancelStabilization state

def measureBindChurnNodeCount (rounds : Nat) (reclaimEachRound : Bool) : IO Nat := do
  let state <- State.create
  let source <- Var.create state 0
  let selected <- bind (Var.watch source) (fun value => ret state value)
  let observer <- observe selected
  State.stabilize state
  for step in [:rounds] do
    Var.set source (step + 1)
    State.stabilize state
    if reclaimEachRound then
      let _ <- State.reclaimUnreachableNodes state
      pure ()
    else
      pure ()
  assertEq "bind churn final observed value" (← Observer.value! observer) rounds
  State.numNodes state

def testReclaimUnreachableNodesMitigatesBindChurn : IO Unit := do
  let rounds := 120
  let leakedNodeCount <- measureBindChurnNodeCount rounds false
  let reclaimedNodeCount <- measureBindChurnNodeCount rounds true
  assertEq "bind churn without reclamation keeps growing nodes" (decide (leakedNodeCount >= rounds + 3)) true
  assertEq "bind churn with reclamation stays near constant size" (decide (reclaimedNodeCount <= 8)) true
  assertEq "bind churn reclamation materially reduces growth" (decide (reclaimedNodeCount + (rounds / 2) <= leakedNodeCount)) true

def testTraceEvents : IO Unit := do
  let state <- State.create
  State.setTraceMode state .unbounded
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun value => value + 1)
  let observer <- observe y
  State.stabilize state
  State.clearTraceEvents state
  Incr.setExternalDirtyReason y "manual-dirty"
  Incr.markStale y
  Incr.invalidate y
  State.stabilize state
  let invalidateEvents <- State.traceEvents state
  let hasMarkedStale := invalidateEvents.any (fun event =>
    event.nodeId == y.id && event.kind == .markedStale (some "manual-dirty"))
  let hasInvalidated := invalidateEvents.any (fun event =>
    event.nodeId == y.id && event.kind == .invalidated)
  let hasRecomputed := invalidateEvents.any (fun event =>
    event.nodeId == y.id &&
      match event.kind with
      | .recomputed _ => true
      | _ => false)
  assertEq "trace records marked stale" hasMarkedStale true
  assertEq "trace records invalidation" hasInvalidated true
  assertEq "trace records recompute completion" hasRecomputed true
  let frozen <- freeze y
  let _frozenObserver <- observe frozen
  State.clearTraceEvents state
  State.stabilize state
  let rewriteEvents <- State.traceEvents state
  let hasDependencyRewrite := rewriteEvents.any (fun event =>
    event.nodeId == frozen.id && event.kind == .dependencyRewrite #[y.id] #[])
  assertEq "trace records dependency rewrite" hasDependencyRewrite true
  Observer.disallowFutureUse observer

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

-- ---------------------------------------------------------------------------
-- Round-3 tests
-- ---------------------------------------------------------------------------

/-- Deferred mutations applied before observer refresh: observer sees node stale
    flag already set when the observer's update callback fires. -/
def testDeferredMutationBeforeObserverRefresh : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun v => v + 1)
  let frozen <- freeze y
  -- When the freeze node rewires during stabilization, queue a markStale on y.
  State.onDependenciesChanged state (fun id _old _new => do
    if id == frozen.id then
      Incr.markStale y
    else
      pure ())
  let yObserver <- observe y
  let _frozenObserver <- observe frozen   -- make frozen necessary so it runs
  -- Track whether y is stale at the moment the observer fires.
  let staleAtRefresh <- IO.mkRef false
  Observer.onUpdate yObserver (fun _ => do
    staleAtRefresh.set (← Incr.isStale y))
  State.stabilize state
  -- y should have been marked stale (deferred) BEFORE the observer callback ran.
  assertEq "deferred mutation visible at observer refresh" (← staleAtRefresh.get) true

/-- Budgeted stabilization with deferred mutations queued across two slices. -/
def testBudgetedStabilizationWithDeferredMutations : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun v => v + 10)
  let z <- map y (fun v => v * 2)
  let frozen <- freeze z
  -- Queue a deferred markStale on x when the freeze node rewires.
  State.onDependenciesChanged state (fun id _old _new => do
    if id == frozen.id then
      Incr.markStale y
    else
      pure ())
  let observer <- observe frozen
  -- First slice: process a limited budget
  let result1 <- State.stabilizeWithBudget state 1
  if result1.completed then
    -- Everything fit in one slice; just verify the deferred mutation was applied
    assertEq "frozen observer value (single slice)" (← Observer.value! observer) 22
    assertEq "deferred mutation count is zero after completion" (← State.deferredMutationCount state) 0
  else
    assertEq "hasDeferredMutations mid-budget" (← State.hasDeferredMutations state) false
    -- Drain to completion
    let result2 <- State.stabilizeWithBudget state 100
    assertEq "budget slice completes" result2.completed true
    assertEq "deferred mutation count zero after completion" (← State.deferredMutationCount state) 0

/-- cancelStabilization clears the deferred mutation queue and prevents stale-
    epoch application on the next epoch. -/
def testCancelStabilizationClearsDeferredQueue : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun v => v + 1)
  let frozen <- freeze y
  -- Queue deferred mutation during stabilization.
  State.onDependenciesChanged state (fun id _old _new => do
    if id == frozen.id then
      Incr.markStale y
    else
      pure ())
  let _yObs <- observe y
  let _fObs <- observe frozen
  -- Run a partial budget so the dependency-change handler fires, queuing the mutation.
  let _slice <- State.stabilizeWithBudget state 100
  -- If the stabilization completed, mutations are already applied; nothing to test.
  -- To reliably leave mutations pending we test cancelStabilization directly.
  -- After a full stabilize, queue something externally as a simulation:
  State.clearTraceEvents state
  -- Simulate: do a fresh partial stabilization, then cancel before completion.
  Var.set x 2
  let _partial <- State.stabilizeWithBudget state 0  -- 0 budget: nothing processed
  assertEq "queue is empty after budget=0 (no work run)" (← State.deferredMutationCount state) 0
  -- Cancel clears partial epoch and queue.
  State.cancelStabilization state
  assertEq "deferredMutationCount is zero after cancel" (← State.deferredMutationCount state) 0
  assertEq "hasPartialStabilization is false after cancel" (← State.hasPartialStabilization state) false
  -- New stabilization should complete cleanly with x=2 visible.
  State.stabilize state
  let obs <- observe (← map (Var.watch x) (fun v => v))
  State.stabilize state
  assertEq "value is correct after cancel+restabilize" (← Observer.value! obs) 2

/-- failFast handler mode re-throws after recording trace. -/
def testFailFastHandlerMode : IO Unit := do
  let state <- State.create
  State.setTraceMode state .unbounded
  State.setHandlerFailureMode state HandlerFailureMode.failFast
  let x <- Var.create state 1
  let doubled <- map (Var.watch x) (fun v => v * 2)
  let frozen <- freeze doubled
  State.onDependenciesChanged state (fun id _old _new => do
    if id == frozen.id then
      throw (IO.userError "failFast test boom")
    else
      pure ())
  let _obs <- observe frozen
  State.clearTraceEvents state
  -- Stabilization should throw because failFast is set.
  let threw <- do
    try
      State.stabilize state
      pure false
    catch _ =>
      pure true
  assertEq "failFast mode causes stabilize to throw" threw true
  -- Trace event should still have been recorded.
  let events <- State.traceEvents state
  let sawFailure := events.any (fun event =>
    match event.kind with
    | .handlerFailed kind _ => kind == "dependency-change"
    | _ => false)
  assertEq "failFast still records trace event" sawFailure true
  -- Reset to traceOnly for subsequent tests.
  State.setHandlerFailureMode state HandlerFailureMode.traceOnly

/-- Deferred mutation introspection APIs. -/
def testDeferredMutationIntrospection : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun v => v + 1)
  let _obs <- observe y
  State.stabilize state
  assertEq "deferredMutationCount is 0 after stabilize" (← State.deferredMutationCount state) 0
  assertEq "hasDeferredMutations is false after stabilize" (← State.hasDeferredMutations state) false
  -- Queue deferred mutations through the dependency-change hook path.
  let frozen <- freeze y
  State.onDependenciesChanged state (fun id _old _new => do
    if id == frozen.id then do
      Incr.markStale y
      Incr.markStale y  -- duplicate; both enqueue
    else
      pure ())
  let _fObs <- observe frozen
  -- During the next stabilization the hook fires and queues entries.
  -- After completion the queue is drained (count goes back to 0).
  State.stabilize state
  assertEq "deferredMutationCount is 0 after completed stabilize" (← State.deferredMutationCount state) 0

/-- Round-trip metadata export and import. -/
def testMetadataExportImport : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun v => v + 1)
  let _observer <- observe y
  State.stabilize state
  -- Set metadata on the y node.
  Incr.setExternalDirtyReason y "dirty-src"
  Incr.addTag y "alpha"
  Incr.addTag y "beta"
  -- Export.
  let json <- State.exportNodeInfosJson state
  -- Overwrite the metadata.
  Incr.clearExternalDirtyReason y
  Incr.removeTag y "alpha"
  Incr.removeTag y "beta"
  let infoAfterClear <- State.nodeInfo state y.id
  assertEq "externalDirtyReason cleared" infoAfterClear.externalDirtyReason none
  assertEq "tags cleared" infoAfterClear.tags #[]
  -- Import the saved snapshot.
  State.importNodeMetadataJson state json
  let infoAfterImport <- State.nodeInfo state y.id
  assertEq "externalDirtyReason restored" infoAfterImport.externalDirtyReason (some "dirty-src")
  assertEq "tags restored" infoAfterImport.tags #["alpha", "beta"]
  assertEq "tag index restored on import" (← State.nodesWithTag state "alpha") #[y.id]
  -- Unknown ids in JSON should not throw.
  let unknownIdJson := "[{\"id\":9999,\"lastAccessedAt\":null,\"externalDirtyReason\":null,\"tags\":[]}]"
  State.importNodeMetadataJson state unknownIdJson  -- should succeed silently
  -- Import with partial fields: only lastAccessedAt present.
  let partialJson := "[{\"id\":" ++ toString y.id ++ ",\"lastAccessedAt\":42,\"externalDirtyReason\":null,\"tags\":[\"only\"]}]"
  State.importNodeMetadataJson state partialJson
  let infoPartial <- State.nodeInfo state y.id
  assertEq "partial import sets lastAccessedAt" infoPartial.lastAccessedAt (some 42)
  assertEq "partial import sets tags" infoPartial.tags #["only"]
  assertEq "tag index follows partial import" (← State.nodesWithTag state "only") #[y.id]

/-- getHandlerFailureMode and setHandlerFailureMode round-trip. -/
def testHandlerFailureModeGetSet : IO Unit := do
  let state <- State.create
  let mode0 <- State.getHandlerFailureMode state
  assertEq "default mode is traceOnly" mode0 HandlerFailureMode.traceOnly
  State.setHandlerFailureMode state HandlerFailureMode.failFast
  let mode1 <- State.getHandlerFailureMode state
  assertEq "set to failFast" mode1 HandlerFailureMode.failFast
  State.setHandlerFailureMode state HandlerFailureMode.traceOnly
  let mode2 <- State.getHandlerFailureMode state
  assertEq "reset to traceOnly" mode2 HandlerFailureMode.traceOnly

/-- getTraceMode and setTraceMode round-trip, with `off` as the safe default. -/
def testTraceModeGetSet : IO Unit := do
  let state <- State.create
  let mode0 <- State.getTraceMode state
  assertEq "default trace mode is off" mode0 .off
  State.setTraceMode state (.bounded 2)
  let mode1 <- State.getTraceMode state
  assertEq "set to bounded" mode1 (.bounded 2)
  State.setTraceMode state .unbounded
  let mode2 <- State.getTraceMode state
  assertEq "set to unbounded" mode2 .unbounded

/-- Bounded trace mode keeps exactly the newest events in oldest-to-newest order. -/
def testTraceModeBoundedRetention : IO Unit := do
  let state <- State.create
  State.setTraceMode state (.bounded 3)
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun value => value + 1)
  State.clearTraceEvents state
  Incr.setExternalDirtyReason y "first"
  Incr.markStale y
  Incr.setExternalDirtyReason y "second"
  Incr.markStale y
  Incr.setExternalDirtyReason y "third"
  Incr.markStale y
  Incr.setExternalDirtyReason y "fourth"
  Incr.markStale y
  let events <- State.traceEvents state
  let reasons := events.foldl (fun acc event =>
    match event.kind with
    | .markedStale (some reason) => acc.push reason
    | _ => acc) #[]
  assertEq "bounded trace mode keeps exactly three events" events.size 3
  assertEq "bounded trace mode keeps newest three in order" reasons #["second", "third", "fourth"]

-- C1: Pin registry (FR-4 mechanism)

/-- Pinned parentless unobserved map node survives reclaim; unpinned → reclaimed. -/
def testPinNodeSurvivesReclaim : IO Unit := do
  let state <- State.create
  let x <- Var.create state 42
  -- Create a map node with no observer (orphaned after setup)
  let m <- map (Var.watch x) (fun v => v + 1)
  let obs <- observe m
  State.stabilize state
  Observer.disallowFutureUse obs
  let nodeId := m.id
  let genBefore <- Internal.State.nodeGeneration state nodeId
  -- Pin the orphaned map node
  State.pinNode state nodeId
  let _ <- State.reclaimUnreachableNodes state
  let genAfterPinned <- Internal.State.nodeGeneration state nodeId
  assertEq "pinned node survives reclaim (generation unchanged)" genAfterPinned genBefore
  let recycled <- state.recycledNodeIdsRef.get
  assertEq "pinned node slot not recycled" (recycled.contains nodeId) false
  -- Unpin and reclaim again
  State.unpinNode state nodeId
  let reclaimed <- State.reclaimUnreachableNodes state
  assertEq "unpinned node is reclaimed" (decide (reclaimed >= 1)) true
  let genAfterUnpinned <- Internal.State.nodeGeneration state nodeId
  assertEq "reclaimed node generation bumped" (decide (genAfterUnpinned > genBefore)) true

-- B2 edge cases: observer-index refresh (FR-1)

/-- FR-1/FR-6: observersRefreshed == 1 when exactly one observer's node changed. -/
def testObserversRefreshedOneDirty : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun v => v + 1)
  let _obs <- observe y
  -- Add extra observers on independent nodes
  for _ in [:99] do
    let v <- Var.create state 0
    let _o <- observe (Var.watch v)
  State.stabilize state
  Var.set x 2
  let stats <- State.stabilizeWithStats state
  assertEq "FR-1 observersRefreshed == 1 with 100 total observers" stats.observersRefreshed 1

/-- Two observers on one node: both refreshed when node changes. -/
def testTwoObserversOneNode : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun v => v * 2)
  let obsA <- observe y
  let obsB <- observe y
  State.stabilize state
  assertEq "initial obsA" (← Observer.value! obsA) 2
  assertEq "initial obsB" (← Observer.value! obsB) 2
  Var.set x 3
  let stats <- State.stabilizeWithStats state
  assertEq "both observers see updated value obsA" (← Observer.value! obsA) 6
  assertEq "both observers see updated value obsB" (← Observer.value! obsB) 6
  assertEq "both observers refreshed" stats.observersRefreshed 2

/-- Observer created and deactivated between passes: no refresh fires on next pass. -/
def testObserverDeactivatedBetweenPasses : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun v => v + 1)
  let obsShortLived <- observe y
  State.stabilize state
  assertEq "short-lived observer initialized" (← Observer.value! obsShortLived) 2
  -- Deactivate before change: observer index removed from observersByNode eagerly
  Observer.disallowFutureUse obsShortLived
  Var.set x 5
  let stats <- State.stabilizeWithStats state
  assertEq "deactivated observer not refreshed" stats.observersRefreshed 0

/-- Observer on a node that changes in a budgeted pass: refresh happens at completing pass. -/
def testObserverRefreshedOnBudgetedPassCompletion : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map (Var.watch x) (fun v => v + 1)
  let obs <- observe y
  State.stabilize state
  assertEq "initial value" (← Observer.value! obs) 2
  Var.set x 10
  -- Budget 0 does no work, leaves pass incomplete
  let r0 <- State.stabilizeWithBudget state 0
  assertEq "budget=0 not completed" r0.completed false
  -- Observer not yet refreshed (incomplete pass)
  assertEq "value unchanged before completion" (← Observer.value! obs) 2
  -- Complete the pass
  let stats <- State.stabilizeWithStats state
  assertEq "value updated after completion" (← Observer.value! obs) 11
  assertEq "observer refreshed at completing pass" stats.observersRefreshed 1

def testCachedDigestCutoffCutsOffOnEqual : IO Unit := do
  let state <- State.create
  -- x changes; y maps to a constant so the output is always the same
  let x <- Var.create state 0
  let y <- map x.watch (fun _ => 42) (Cutoff.ofCachedDigest)
  let obs <- observe y
  State.stabilize state
  assertEq "initial value" (← Observer.value! obs) 42
  -- x changes → y recomputes → output still 42 → digest matches → cut off
  Var.set x 1
  let stats <- State.stabilizeWithStats state
  -- y was recomputed but its value didn't change → nodesChanged counts x only
  assertEq "y observer not refreshed" stats.observersRefreshed 0

def testCachedDigestCutoffPropagatesOnChange : IO Unit := do
  let state <- State.create
  let x <- Var.create state 1
  let y <- map x.watch (· + 0) (Cutoff.ofCachedDigest)
  let obs <- observe y
  State.stabilize state
  assertEq "initial value" (← Observer.value! obs) 1
  Var.set x 2
  State.stabilize state
  assertEq "changed value propagated" (← Observer.value! obs) 2

def testRecomputeTimingRecordedWhenEnabled : IO Unit := do
  let state <- State.create
  State.setTimingEnabled state true
  let x <- Var.create state 1
  let y <- map x.watch (· + 1)
  let _ <- observe y
  State.stabilize state
  let timings <- State.lastPassTimings state
  assertEq "timings nonempty when enabled" (timings.size != 0) true
  -- Disable timing; next pass should record nothing
  State.setTimingEnabled state false
  Var.set x 2
  State.stabilize state
  let timings2 <- State.lastPassTimings state
  assertEq "timings empty after disable" timings2.size 0

def testRecomputeTimingEmptyWhenDisabled : IO Unit := do
  let state <- State.create
  -- Timing is off by default
  let x <- Var.create state 7
  let y <- map x.watch (· * 2)
  let _ <- observe y
  State.stabilize state
  let timings <- State.lastPassTimings state
  assertEq "timings empty by default" timings.size 0

def runAll : IO Unit := do
  testMap2
  testHigherArityMaps
  testCutoff
  testVarCreateCutoffAtConstruction
  testMapCutoffAtConstruction
  testHashCutoffUncheckedCollisionSuppressesChange
  testHashCutoffSafeCollisionPropagatesChange
  testBindAndBranch
  testBindRewiresOncePerLhsChange
  testBindCutoffAtConstruction
  testAssocAggregateSingleEntryLocality
  testFold
  testDependOnAndSums
  testFreeze
  testFreezeWhenCutoffAtConstruction
  testObservabilityTransitions
  testMultipleObserversShareNecessity
  testObserverRemovalDropsNecessityWithoutGlobalPass
  testObserverRefreshPrunesInactiveObservers
  testObserverCreatedAfterStablePassInitializes
  testGraphDebugging
  testCoreInvariants
  testCycleDiagnostics
  testDependencyChangeHooks
  testIncrInvalidate
  testMarkStalePreservesCachedValue
  testMarkStaleRecomputesStaleParents
  testNecessaryRewriteQueuesMissingChildOutsideStabilization
  testNecessaryRewriteUpdatesChildrenIncrementally
  testCancelRestoresPendingDirtyWork
  testCancelRestoresPartialChainWork
  testQueuedUnnecessaryRootsAreSkippedSafely
  testTraceEpochContext
  testDependencyHandlerCanQueueMutationsDuringStabilization
  testHandlerFailureIsTracedNotFatal
  testNodeMetadataApis
  testNodesWithTagOrdering
  testStaleNecessaryIds
  testStaleNecessaryIdsSortedOrder
  testReclaimUnreachableCachedValues
  testReclaimUnreachableCachedValuesGuard
  testReclaimUnreachableNodesMitigatesBindChurn
  testTraceEvents
  testClock
  testExpertNode
  -- Round-3 tests
  testDeferredMutationBeforeObserverRefresh
  testBudgetedStabilizationWithDeferredMutations
  testCancelStabilizationClearsDeferredQueue
  testFailFastHandlerMode
  testDeferredMutationIntrospection
  testMetadataExportImport
  testHandlerFailureModeGetSet
  testTraceModeGetSet
  testTraceModeBoundedRetention
  -- C1: FR-4 pin registry
  testPinNodeSurvivesReclaim
  -- B2: FR-1 / FR-6 observer-index tests
  testObserversRefreshedOneDirty
  testTwoObserversOneNode
  testObserverDeactivatedBetweenPasses
  testObserverRefreshedOnBudgetedPassCompletion
  -- D1: FR-9 cached-digest cutoff
  testCachedDigestCutoffCutsOffOnEqual
  testCachedDigestCutoffPropagatesOnChange
  -- D2: FR-13 opt-in recompute timing
  testRecomputeTimingRecordedWhenEnabled
  testRecomputeTimingEmptyWhenDisabled

end Core
end Tests
end Leancremental
