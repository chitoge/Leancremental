import Leancremental.Core.Basic

/-! Deterministic clock combinators. -/

namespace Leancremental
namespace Clock

/-- Create a deterministic clock starting at `start`. -/
def create (state : State) (start : Nat := 0) : IO Clock := do
  let nowVar <- Var.create state start
  pure { state := state, nowVar := nowVar }

/-- Return the clock's latest time. -/
def now (clock : Clock) : IO Nat :=
  Var.value clock.nowVar

/-- Watch the clock's current time as an incremental value. -/
def watchNow (clock : Clock) : Incr Nat :=
  clock.nowVar.watch

/-- Advance the clock to `time`, ignoring backwards moves. -/
def advanceTo (clock : Clock) (time : Nat) : IO Unit := do
  let current <- now clock
  if current <= time then
    Var.set clock.nowVar time
  else
    pure ()

/-- Advance the clock by a non-negative span. -/
def advanceBy (clock : Clock) (span : Nat) : IO Unit := do
  let current <- now clock
  advanceTo clock (current + span)

/-- Return whether the clock is before or after a fixed time. -/
def atTime (clock : Clock) (time : Nat) : IO (Incr BeforeOrAfter) :=
  map (watchNow clock) (fun now => if now < time then .before else .after)

/-- Return whether the clock is before or after `span` ticks from now. -/
def after (clock : Clock) (span : Nat) : IO (Incr BeforeOrAfter) := do
  let current <- now clock
  atTime clock (current + span)

/-- Return an incremental interval counter derived from the clock. -/
def atIntervals (clock : Clock) (interval : Nat) : IO (Incr Nat) :=
  map (watchNow clock) (fun now => if interval == 0 then now else now / interval)

/-- Return an incremental step function over deterministic `Nat` time. -/
def stepFunction (clock : Clock) (init : α) (steps : List (Nat × α)) : IO (Incr α) :=
  map (watchNow clock) (fun now =>
    steps.foldl
      (fun acc step => if step.fst <= now then step.snd else acc)
      init)

end Clock
end Leancremental
