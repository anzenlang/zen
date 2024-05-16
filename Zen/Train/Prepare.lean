import Zen.Fs



namespace Zen.Train



/-- Prepares the sources of a training session for participants.

Trainers are expected to write things to remove ("solutions") between `section sol!` and `end sol!`,
each appearing on a single line and without leading or trailing whitespaces (or anything else).
Nested `section sol!` are supported.

Outer-most `section sol! ... end sol!`-s are replaced with a todo comment.
-/
def prepareSources (path : Fs.FilePath) : IO Unit := do
  Fs.iterFilesIn path (skip := skip) work
where
  /-- Skip non-`.lean` files. -/
  skip entry : IO Bool :=
    let nonLeanFile :=
      match entry.path.extension with
      | some "lean" | none => false
      | some _ => true
    return nonLeanFile
  /-- Copy file content, removing solutions. -/
  work entry : IO PUnit := do
    println! "working on `{entry.path}`"
    let path := entry.path
    Fs.cpFile path path (overwrite := true)
      fun txt h => do
        let rmed ← rmSolutions 0 h 0 (txt.splitOn "\n")
        println! "removed {rmed} line{plural rmed} from `{entry.path}`"
  /-- Remove everything between `section sol!` and `end sol!`. -/
  rmSolutions (rmed : Nat) handle : Nat → List String → IO Nat
    | d, "section sol!"::tl => do
      if d = 0 then
        handle.putStrLn "-- todo 🙀"
      rmSolutions rmed.succ handle d.succ tl
    | d, "end sol!"::tl => do
      if d = 0 then
        IO.throwServerError "`Zen.Train.prepareSources` failure, skip depth is `0` on `end sol!`"
      rmSolutions rmed.succ handle d.pred tl
    | 0, [hd] => do
      handle.putStr hd;
      return rmed
    | 0, hd::tl => do
      handle.putStrLn hd
      rmSolutions rmed handle 0 tl
    | d, _hd::tl => do
      rmSolutions rmed.succ handle d tl
    | _, [] =>
      return rmed

syntax (name := Zen.prepareCmd) "Zen.prepare! " term : command

open Lean.Elab in
@[command_elab Zen.prepareCmd]
unsafe def elabPrepareCmd : Command.CommandElab
| `(Zen.prepare! $dir) => do
  let pwd ← Command.liftIO IO.currentDir
  let dir ← Command.liftTermElabM (Term.evalTerm String (Lean.mkConst `String) dir)
  prepareSources (pwd / dir)
| _ => throwUnsupportedSyntax
