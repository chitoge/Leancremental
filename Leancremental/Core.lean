import Leancremental.Core.Types
import Leancremental.Core.Internal
import Leancremental.Core.State
import Leancremental.Core.Basic
import Leancremental.Core.Memo
import Leancremental.Core.Query
import Leancremental.Core.Aggregate
import Leancremental.Core.Result
import Leancremental.Core.Document
import Leancremental.Core.Clock
import Leancremental.Core.Expert
import Leancremental.Core.Observer
import Leancremental.Core.Invariant
import Leancremental.Core.Snapshot

/-!
Leancremental's executable incremental runtime.

Import this module when you want to build and run incremental graphs in `IO`.
It provides mutable input variables, explicit stabilization, observers, cutoffs,
dynamic dependencies, memoization helpers, clocks, expert nodes, and debugging
support.
-/
