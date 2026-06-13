import Tests.Core
import Tests.Query
import Tests.Pure
import Tests.TutorialExamples
import Tests.Actions
import Tests.ConceptsExamples
import Tests.CookbookExamples

/-! Test executable root for Leancremental. -/

def main : IO Unit := do
  Leancremental.Tests.Core.runAll
  Leancremental.Tests.Query.runAll
  Leancremental.Tests.PureModel.runAll
  Leancremental.Tests.TutorialExamples.runAll
  Leancremental.Tests.Actions.runAll
  Leancremental.Tests.ConceptsExamples.runAll
  Leancremental.Tests.CookbookExamples.runAll
  IO.println "leancremental tests passed"
