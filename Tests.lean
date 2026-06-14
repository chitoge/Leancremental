import Tests.Core
import Tests.Query
import Tests.Pure
import Tests.TutorialExamples
import Tests.Actions
import Tests.ConceptsExamples
import Tests.CookbookExamples
import Tests.Parallel
import Tests.ConcurrencyExamples
import Tests.QueriesExamples
import Tests.FederationExamples

/-! Test executable root for Leancremental. -/

def main : IO Unit := do
  Leancremental.Tests.Core.runAll
  Leancremental.Tests.Query.runAll
  Leancremental.Tests.PureModel.runAll
  Leancremental.Tests.TutorialExamples.runAll
  Leancremental.Tests.Actions.runAll
  Leancremental.Tests.ConceptsExamples.runAll
  Leancremental.Tests.CookbookExamples.runAll
  Leancremental.Tests.Parallel.runAll
  Leancremental.Tests.ConcurrencyExamples.runAll
  Leancremental.Tests.QueriesExamples.runAll
  Leancremental.Tests.FederationExamples.runAll
  IO.println "leancremental tests passed"
