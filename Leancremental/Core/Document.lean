import Leancremental.Core.Result

/-!
Lightweight document versions for LSP-style query graphs.

This is not a persistent multi-version runtime. It is a small layer that keeps a
document's content and version as ordinary incremental variables, lets query
outputs carry the version they were computed from, and provides request tokens
that can be checked before publishing responses.
-/

namespace Leancremental
namespace Document

/-- A value tagged with the document version it came from. -/
structure Versioned (α : Type) where
  /-- Document version used for this value. -/
  version : Nat
  /-- Query value for that version. -/
  value : α
deriving Repr, BEq

/-- A point-in-time document snapshot read outside the incremental graph. -/
structure Snapshot (α : Type) where
  /-- Current document version. -/
  version : Nat
  /-- Current document content. -/
  content : α
deriving Repr, BEq

/-- A request pinned to the document version visible when it was created. -/
structure RequestToken where
  /-- Caller-supplied request id. -/
  id : Nat
  /-- Document version associated with the request. -/
  version : Nat
deriving Repr, BEq

/--
Document handle containing mutable content and an incremental version counter.
-/
structure Handle (α : Type) where
  /-- State that owns the document variables. -/
  state : State
  /-- Mutable document content. -/
  content : Var α
  /-- Mutable document version. -/
  version : Var Nat

/-- Create a document handle. -/
def create (state : State) (initial : α) (initialVersion : Nat := 0) : IO (Handle α) := do
  let content <- Var.create state initial
  let version <- Var.create state initialVersion
  pure { state := state, content := content, version := version }

/-- Watch the document content. -/
def watchContent (doc : Handle α) : Incr α :=
  Var.watch doc.content

/-- Watch the document version. -/
def watchVersion (doc : Handle α) : Incr Nat :=
  Var.watch doc.version

/-- Read the current document version directly, outside the incremental graph. -/
def currentVersion (doc : Handle α) : IO Nat :=
  Var.value doc.version

/-- Read the current document content directly, outside the incremental graph. -/
def currentContent (doc : Handle α) : IO α :=
  Var.value doc.content

/-- Read the current content and version together outside the incremental graph. -/
def snapshot (doc : Handle α) : IO (Snapshot α) := do
  pure { version := (← currentVersion doc), content := (← currentContent doc) }

/-- Set document content and version explicitly. -/
def set (doc : Handle α) (version : Nat) (content : α) : IO Unit := do
  Var.set doc.content content
  Var.set doc.version version

/-- Apply an edit and increment the document version. -/
def edit (doc : Handle α) (f : α -> α) : IO Nat := do
  let nextContent := f (← currentContent doc)
  let nextVersion := (← currentVersion doc) + 1
  set doc nextVersion nextContent
  pure nextVersion

/-- Tag a query result with the document version used to compute it. -/
def tag (doc : Handle γ) (node : Incr α) : IO (Incr (Versioned α)) :=
  Leancremental.map2 (watchVersion doc) node (fun version value => { version := version, value := value })

/--
Reject a versioned value when it no longer matches the document's current
version.
-/
def requireCurrent (doc : Handle γ) (node : Incr (Versioned α)) : IO (Incr (Except String α)) :=
  Leancremental.map2 (watchVersion doc) node (fun currentVersion versioned =>
    if versioned.version == currentVersion then
      .ok versioned.value
    else
      .error s!"stale result for document version {versioned.version}, current version is {currentVersion}")

/-- Create a request token pinned to the document's current version. -/
def requestToken (doc : Handle α) (id : Nat) : IO RequestToken := do
  pure { id := id, version := (← currentVersion doc) }

/-- Return whether a request token still matches the current document version. -/
def requestIsCurrent (doc : Handle α) (token : RequestToken) : IO Bool := do
  pure ((← currentVersion doc) == token.version)

end Document
end Leancremental
