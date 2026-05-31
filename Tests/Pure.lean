import Leancremental
import Tests.Util

/-! Pure model and executable snapshot bridge regression tests. -/

namespace Leancremental
namespace Tests
namespace PureModel

def testPureModel : IO Unit := do
  let x : Pure.Var Nat := { value := 2 }
  let y : Pure.Var Nat := { value := 3 }
  let expr := Pure.map2 (Pure.Var.watch x) (Pure.Var.watch y) (fun x y => x + y)
  assertEq "pure map2 eval" (Pure.eval expr) 5
  let rebound := (Pure.Var.set x 10).watch
  assertEq "pure var set" rebound.eval 10
  let total := Pure.Expr.sumNat #[Pure.const 1, Pure.const 2, Pure.const 3]
  assertEq "pure sum" total.eval 6
  let snapshot := Pure.Snapshot.ofModel expr
  assertEq "pure snapshot value" snapshot.value 5
  let coreSnapshot := CoreSnapshot.stableValueSnapshot 42
  assertEq "core snapshot value" coreSnapshot.value 42
  assertEq "core snapshot model" (Pure.eval coreSnapshot.model) 42
  let state <- State.create
  let compiledObserver <- CoreSnapshot.observeExpr state expr
  State.stabilize state
  assertEq "compiled pure expression" (← Observer.value! compiledObserver) (CoreSnapshot.expectedValue expr)
  let certifiedState <- State.create
    let certifiedValue <- CoreSnapshot.observeExprChecked certifiedState expr
    match CoreSnapshot.certifyValue expr certifiedValue with
    | .ok certifiedSnapshot =>
      let _certifiedSound : certifiedSnapshot.model.eval = certifiedSnapshot.value := certifiedSnapshot.sound
      assertEq "certified compiled pure expression" certifiedSnapshot.value (CoreSnapshot.expectedValue expr)
    | .error err => throw (IO.userError err)
  let foldState <- State.create
  let foldExprs := #[Pure.const 1, Pure.const 2, Pure.const 3]
  let foldObserver <- CoreSnapshot.observeFoldArray foldState foldExprs 0 (fun acc value => acc + value)
  State.stabilize foldState
  assertEq "compiled pure fold" (← Observer.value! foldObserver) (CoreSnapshot.expectedFoldValue foldExprs 0 (fun acc value => acc + value))
  let certifiedFoldState <- State.create
    let certifiedFoldValue <- CoreSnapshot.observeFoldArrayChecked certifiedFoldState foldExprs 0 (fun acc value => acc + value)
    match CoreSnapshot.certifyFoldValue foldExprs 0 (fun acc value => acc + value) certifiedFoldValue with
    | .ok certifiedFoldSnapshot =>
      let _certifiedFoldSound : certifiedFoldSnapshot.model.eval = certifiedFoldSnapshot.value := certifiedFoldSnapshot.sound
      assertEq "certified compiled pure fold" certifiedFoldSnapshot.value (CoreSnapshot.expectedFoldValue foldExprs 0 (fun acc value => acc + value))
    | .error err => throw (IO.userError err)

def runAll : IO Unit := do
  testPureModel

end PureModel
end Tests
end Leancremental
