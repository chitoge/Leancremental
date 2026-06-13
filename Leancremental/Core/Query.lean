import Leancremental.Core.Memo

/-!
Memoized query construction on top of Leancremental's dynamic dependency graph.

`QueryM` is a small monad for building memoized queries whose dependencies are
other queries keyed by stable request identifiers. Its `bind` uses the core
incremental `bind`, so switching dependencies rewires the graph instead of
flattening through plain `IO` sequencing.
-/

namespace Leancremental

/-- Services available while building one query node. -/
structure QueryRuntime (κ : Type) (α : Type) where
  /-- State that owns every query node. -/
  state : State
  /-- Request another memoized query by key. -/
  request : κ -> IO (Incr α)

/--
Monad for building query nodes that can depend on other memoized queries.

The result of a `QueryM` computation is still an `Incr` node, not an immediate
answer.
-/
structure QueryM (κ : Type) (α : Type) (β : Type) where
  /-- Build one incremental node in the supplied runtime. -/
  run : QueryRuntime κ α -> IO (Incr β)

namespace QueryM

/-- Lift an existing incremental node into `QueryM`. -/
def ofIncr (node : Incr β) : QueryM κ α β := {
  run := fun _ => pure node
}

/-- Lift an `IO` action that builds an incremental node into `QueryM`. -/
def ofIO (action : IO (Incr β)) : QueryM κ α β := {
  run := fun _ => action
}

/-- Depend on another memoized query identified by `key`. -/
def require (key : κ) : QueryM κ α α := {
  run := fun runtime => runtime.request key
}

instance : Functor (QueryM κ α) where
  map f query := {
    run := fun runtime => do
      let node <- query.run runtime
      Leancremental.map node f
  }

instance : Pure (QueryM κ α) where
  pure value := {
    run := fun runtime => Leancremental.const runtime.state value
  }

instance : Seq (QueryM κ α) where
  seq queryFn queryArg := {
    run := fun runtime => do
      let fnNode <- queryFn.run runtime
      Leancremental.bind fnNode (fun fn => do
        let argNode <- (queryArg ()).run runtime
        Leancremental.map argNode fn)
  }

instance : Bind (QueryM κ α) where
  bind query next := {
    run := fun runtime => do
      let node <- query.run runtime
      Leancremental.bind node (fun value => (next value).run runtime)
  }

instance : Applicative (QueryM κ α) where
  pure := Pure.pure
  seq := Seq.seq
  map := Functor.map

instance : Monad (QueryM κ α) where
  pure := Pure.pure
  bind := Bind.bind
  seq := Seq.seq
  map := Functor.map

end QueryM

/--
Rules for one memoized query family.

All keys in one `QueryTable` share the same result type `α`.
-/
structure QueryRules (κ : Type) (α : Type) where
  /-- Build the incremental node associated with one key. -/
  build : κ -> QueryM κ α α
  /-- Render one key for cycle and user-facing error messages. -/
  describeKey : κ -> String := fun _ => "<query>"

/--
Memoized query table with a guard against recursive construction cycles.

Use one table per query family, or multiple tables on the same `State` when
different query families have different result types.
-/
structure QueryTable (κ : Type) (α : Type) [BEq κ] [Hashable κ] where
  /-- State that owns the memoized query nodes. -/
  state : State
  /-- Rules used to build cache misses. -/
  rules : QueryRules κ α
  /-- Live memo table used to intern query nodes by key. -/
  memo : MemoTable κ α
  /-- Stack of keys currently being constructed. -/
  inFlightKeys : IO.Ref (Array κ)

namespace QueryTable

def dropUntilKey [BEq κ] (key : κ) : List κ -> List κ
  | [] => []
  | current :: rest =>
      if current == key then
        current :: rest
      else
        dropUntilKey key rest

def formatCycleError [BEq κ] [Hashable κ] (table : QueryTable κ α) (key : κ) (stack : Array κ) : String :=
  let cycle := dropUntilKey key stack.toList ++ [key]
  let rendered := cycle.map table.rules.describeKey
  "query cycle detected: " ++ Internal.joinWith " -> " rendered

def withInFlightKey [BEq κ] [Hashable κ] (table : QueryTable κ α) (key : κ) (action : IO β) : IO β := do
  let stack <- table.inFlightKeys.get
  if stack.any (fun current => current == key) then
    Internal.throwUser (formatCycleError table key stack)
  table.inFlightKeys.set (stack.push key)
  try
    action
  finally
    table.inFlightKeys.modify (fun current =>
      if current.size == 0 then
        current
      else
        current.extract 0 (current.size - 1))

/-- Create a memoized query table for the supplied rules. -/
def create [BEq κ] [Hashable κ] (state : State) (rules : QueryRules κ α) : IO (QueryTable κ α) := do
  let memo <- MemoTable.create (κ := κ) (α := α) state
  let inFlightKeys <- IO.mkRef #[]
  pure {
    state := state,
    rules := rules,
    memo := memo,
    inFlightKeys := inFlightKeys
  }

/--
Return the memoized node for `key`, building it on the first request.

Repeated requests for the same key reuse the same incremental node.
-/
partial def request [BEq κ] [Hashable κ] (table : QueryTable κ α) (key : κ) : IO (Incr α) := do
  match <- MemoTable.lookup table.memo key with
  | some node =>
      pure node
  | none =>
      if !(← State.amStabilizing table.state) && (← State.hasPartialStabilization table.state) then
        Internal.throwUser "cannot request a query while a budgeted stabilization is incomplete"
      withInFlightKey table key do
        MemoTable.getOrCreate table.memo key (fun key => do
          let runtime : QueryRuntime κ α := {
            state := table.state,
            request := request table
          }
          (table.rules.build key).run runtime)

/--
Invalidate the memoized node for `key` in place, preserving interned node identity.

Unlike `MemoTable.invalidate`, this does not erase the key from the memo table;
existing and future requests for the same key keep returning the same node id.
-/
def invalidate [BEq κ] [Hashable κ] (table : QueryTable κ α) (key : κ) : IO Bool := do
  match <- table.memo.store.lookup key with
  | some node =>
      Incr.invalidate node
      pure true
  | none =>
      pure false

/--
Invalidate every memoized query node accepted by `predicate` in place, returning
the number of invalidated nodes.
-/
def invalidateMatching [BEq κ] [Hashable κ]
    (table : QueryTable κ α) (predicate : κ -> Bool) : IO Nat := do
  let currentEntries <- MemoTable.entries table.memo
  let mut invalidated := 0
  for entry in currentEntries do
    if predicate entry.1 then
      Incr.invalidate entry.2
      invalidated := invalidated + 1
  pure invalidated

end QueryTable
end Leancremental
