import Zen.Init



/-! # Compilation failure checking

Syntax extension for checking errors appearing when compiling commands.

With some help by Eric Wieser, see [here].

[here]: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Catching.20command.20elaboration.20errors
-/
namespace Zen.CompileFail

open Lean.Elab (throwUnsupportedSyntax)
open Lean.Elab.Command (CommandElab CommandElabM liftCoreM)
open Lean.Elab.Term (evalTerm)



protected def typList (α : Lean.Expr) :=
  Lean.mkApp (Lean.mkConst ``List [.zero]) α

protected def typString :=
  Lean.mkConst ``String

protected def typListString :=
  Zen.CompileFail.typList Zen.CompileFail.typString

syntax (name := compileFail)
  "#compile_fail " term command
: command



def stringAsItem (s : String) : String := Id.run do
  let mut res := ""
  let mut first := true
  for line in s.splitOn "\n" do
    if first then
      first := false
      res := "- "
    else
      res := res ++ "\n  "
    res := res ++ line
  return res

def stringsAsItems (ss : List String) : String := Id.run do
  let mut res := ""
  for s in ss do
    if res ≠ "" then
      res := res ++ "\n"
    res := res ++ stringAsItem s
  return res

def confirmErrors :
  (expected : List String)
  → (msgs : List Lean.Message)
  → CommandElabM Bool
| expHead::expTail, msgHead::msgTail => do
  let msgHead ← msgHead.data.toString
  if expHead ≠ msgHead then
    return false
  else
    confirmErrors expTail msgTail
| [], [] => return true
| _, [] | [], _ => return false

/-- Checks that a command fails to compile with some errors and potentially some warnings.

`#compile_fail ["error/warning message 1", "error/warning message 2", ...] COMMAND`

For example:

```lean
#compile_fail ["\
invalid universe level in constructor 'Lst.cons', parameter has type
  α
at universe level
  2
it must be smaller than or equal to the inductive datatype universe level
  1\
"]
  inductive Lst (α : Type 1) : Type
  | nil
  | cons : α → Lst α → Lst α
```
-/
@[command_elab compileFail]
unsafe def elabCompileFail : CommandElab
| `(#compile_fail $expected:term $c:command) => do
  let expected ←
    evalTerm (List String) CompileFail.typListString expected
    |> Lean.Elab.Command.liftTermElabM
  let oldState ← get
  Lean.Elab.Command.elabCommand c
  let newState ← get
  let newErrorList :=
    newState.messages.toList.drop oldState.messages.toArray.size
    |>.filter fun msg => msg.severity == .error ∨ msg.severity == .warning
  if newErrorList.isEmpty then
    throwError "compilation was expected to fail but did not"
  else
    -- for msg in newErrorList do
    --   let err ← msg.data.toString
    --   println! "error:"
    --   for line in err.splitOn "\n" do
    --     println! "> `{line}`"
    let okay ← confirmErrors expected newErrorList
    if okay then
      set oldState
    else
      let errCount := newErrorList.length
      throwError
        s!"\
          failure: expected the following {expected.length} error{plural expected.length}\n\
          {stringsAsItems expected}\n\
          the actual {errCount} error{plural errCount} do not match\
        "
| _ => do
  throwUnsupportedSyntax

#compile_fail ["\
invalid universe level in constructor 'Zen.CompileFail.Lst.cons', parameter has type
  α
at universe level
  2
it must be smaller than or equal to the inductive datatype universe level
  1\
"]
  inductive Lst (α : Type 1) : Type
  | nil
  | cons : α → Lst α → Lst α

#compile_fail ["compilation was expected to fail but did not"]
  #compile_fail []
    inductive Lst (α : Type) : Type
    | nil
    | cons : α → Lst α → Lst α
