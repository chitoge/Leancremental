import Leancremental
import Tests.Util

/-!
Checked copies of the executable snippets from `CONCEPTS.md`.
-/

namespace Leancremental
namespace Tests
namespace ConceptsExamples

def demo : IO Nat := do
  let state <- State.create

  let x <- Var.create state 2
  let y <- Var.create state 3
  let sum <- map2 (Var.watch x) (Var.watch y) (fun a b => a + b)

  let observer <- observe sum
  State.stabilize state
  let first <- Observer.value! observer

  Var.set x 10
  State.stabilize state
  let second <- Observer.value! observer

  pure (first + second)

def runAll : IO Unit := do
  assertEq "concepts demo" (← demo) 18

end ConceptsExamples
end Tests
end Leancremental
