import Lake
open Lake DSL

package leancremental where
  version := v!"0.1.0"
  keywords := #["incremental", "self-adjusting-computation", "reactive"]

@[default_target]
lean_lib Leancremental where

lean_lib TestsSupport where
  roots := #[`Tests.Util, `Tests.Core, `Tests.Query, `Tests.Pure, `Tests.TutorialExamples]

lean_exe tests where
  root := `Tests
