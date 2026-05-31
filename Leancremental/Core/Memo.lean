import Std.Data.HashMap
import Leancremental.Core.Basic

/-!
Keyed memoization for query-style incremental graph construction.

An LSP-oriented interpreter or compiler often has stable query keys such as
files, declaration names, syntax node ids, or request-local positions. A
`MemoTable` maps those keys to graph nodes so repeated requests reuse the same
incremental computation instead of allocating duplicate subgraphs.
-/

namespace Leancremental

def memoContainsKey [BEq κ] (keys : Array κ) (key : κ) : Bool :=
  keys.any (fun existing => existing == key)

/-- A keyed cache of incremental nodes in one `State`. -/
structure MemoTable (κ : Type) (α : Type) [BEq κ] [Hashable κ] where
  /-- State that owns every node stored in this table. -/
  state : State
  /-- Mutable key-to-node cache. -/
  cache : IO.Ref (Std.HashMap κ (Incr α))

namespace MemoTable

def ensureCanMutate [BEq κ] [Hashable κ] (table : MemoTable κ α) : IO Unit := do
  if <- State.amStabilizing table.state then
    Internal.throwUser "cannot mutate a memo table while stabilization is running"
  if <- State.hasPartialStabilization table.state then
    Internal.throwUser "cannot mutate a memo table while a budgeted stabilization is incomplete"

/-- Create an empty memo table for nodes owned by `state`. -/
def create [BEq κ] [Hashable κ] (state : State) : IO (MemoTable κ α) := do
  let cache <- IO.mkRef (Std.HashMap.emptyWithCapacity : Std.HashMap κ (Incr α))
  pure { state := state, cache := cache }

/-- Look up a cached incremental node by key. -/
def lookup [BEq κ] [Hashable κ] (table : MemoTable κ α) (key : κ) : IO (Option (Incr α)) := do
  let cache <- table.cache.get
  pure (cache.get? key)

/--
Return the cached node for `key`, or allocate it with `compute` and store it.

The table is append-only in this first query-oriented layer. Later lifecycle APIs
can add scoped invalidation and eviction without changing this stable lookup
contract.
-/
def getOrCreate [BEq κ] [Hashable κ]
    (table : MemoTable κ α) (key : κ) (compute : κ -> IO (Incr α)) : IO (Incr α) := do
  match <- lookup table key with
  | some node => pure node
  | none =>
      let node <- compute key
      table.cache.modify (fun cache => cache.insert key node)
      pure node

/-- Remove one key from the memo table. Existing observers of the old node keep working. -/
def invalidate [BEq κ] [Hashable κ] (table : MemoTable κ α) (key : κ) : IO Bool := do
  ensureCanMutate table
  let cache <- table.cache.get
  let existed := (cache.get? key).isSome
  table.cache.set (cache.erase key)
  pure existed

/-- Remove every key that satisfies `predicate`, returning the number of removed entries. -/
def invalidateMatching [BEq κ] [Hashable κ] (table : MemoTable κ α) (predicate : κ -> Bool) : IO Nat := do
  ensureCanMutate table
  let cache <- table.cache.get
  let before := cache.size
  let filtered := cache.filter (fun key _ => !predicate key)
  table.cache.set filtered
  pure (before - filtered.size)

/-- Remove all entries from the memo table, returning the number removed. -/
def clear [BEq κ] [Hashable κ] (table : MemoTable κ α) : IO Nat := do
  ensureCanMutate table
  let cache <- table.cache.get
  table.cache.set (Std.HashMap.emptyWithCapacity : Std.HashMap κ (Incr α))
  pure cache.size

/-- Number of entries currently cached in the memo table. -/
def size [BEq κ] [Hashable κ] (table : MemoTable κ α) : IO Nat := do
  let cache <- table.cache.get
  pure cache.size

end MemoTable

/-- A request- or owner-local view of a memo table. -/
structure MemoScope (κ : Type) (α : Type) [BEq κ] [Hashable κ] where
  /-- Shared table that stores the actual cached nodes. -/
  table : MemoTable κ α
  /-- Keys touched through this scope. -/
  keys : IO.Ref (Array κ)

namespace MemoScope

/-- Create an empty scope over an existing memo table. -/
def create [BEq κ] [Hashable κ] (table : MemoTable κ α) : IO (MemoScope κ α) := do
  let keys <- IO.mkRef #[]
  pure { table := table, keys := keys }

/-- Return the keys currently owned by this scope. -/
def ownedKeys [BEq κ] [Hashable κ] (scope : MemoScope κ α) : IO (Array κ) :=
  scope.keys.get

/-- Get or create a memoized node and record the key in this scope. -/
def getOrCreate [BEq κ] [Hashable κ]
    (scope : MemoScope κ α) (key : κ) (compute : κ -> IO (Incr α)) : IO (Incr α) := do
  let node <- MemoTable.getOrCreate scope.table key compute
  scope.keys.modify (fun keys => if memoContainsKey keys key then keys else keys.push key)
  pure node

/-- Remove all keys touched through this scope from the underlying table. -/
def clear [BEq κ] [Hashable κ] (scope : MemoScope κ α) : IO Nat := do
  let keys <- scope.keys.get
  let mut removed := 0
  for key in keys do
    if <- MemoTable.invalidate scope.table key then
      removed := removed + 1
  scope.keys.set #[]
  pure removed

end MemoScope
end Leancremental