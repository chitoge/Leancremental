import Lake
open Lake DSL

package leancremental where
  version := v!"0.4.0"
  keywords := #["incremental", "self-adjusting-computation", "reactive"]

@[default_target]
lean_lib Leancremental where

lean_lib TestsSupport where
  roots := #[`Tests.Util, `Tests.Core, `Tests.Query, `Tests.Pure, `Tests.TutorialExamples, `Tests.Actions, `Tests.ConceptsExamples, `Tests.CookbookExamples, `Tests.Parallel, `Tests.ConcurrencyExamples, `Tests.QueriesExamples, `Tests.FederationExamples]

lean_exe tests where
  root := `Tests

lean_exe proptests where
  root := `Tests.Prop

lean_exe benchScaling where
  root := `Tests.BenchSize

lean_exe benchScaling2 where
  root := `Tests.BenchPropagation

lean_exe benchScaling3 where
  root := `Tests.BenchAggregate
