import Tests.Core
import Tests.Query
import Tests.Pure
import Tests.TutorialExamples

/-! Test executable root for Leancremental. -/

def main : IO Unit := do
  Leancremental.Tests.Core.runAll
  Leancremental.Tests.Query.runAll
  Leancremental.Tests.PureModel.runAll
  Leancremental.Tests.TutorialExamples.runAll
  IO.println "leancremental tests passed"
