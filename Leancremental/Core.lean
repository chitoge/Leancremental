import Leancremental.Core.Types
import Leancremental.Core.Internal
import Leancremental.Core.State
import Leancremental.Core.Basic
import Leancremental.Core.Memo
import Leancremental.Core.Aggregate
import Leancremental.Core.Result
import Leancremental.Core.Document
import Leancremental.Core.Clock
import Leancremental.Core.Expert
import Leancremental.Core.Observer
import Leancremental.Core.Invariant
import Leancremental.Core.Snapshot

/-!
Leancremental's executable incremental graph engine.

The API mirrors the core ideas of Jane Street's Incremental library in Lean 4:
mutable input variables, explicit stabilization, observed values, cutoff
functions, dynamically changing dependencies, clocks, expert nodes, and a bridge
from stable executable values into the pure proof model. It also exposes
OCaml-Incremental-inspired graph invariant checks for proof and debugging work.
-/
