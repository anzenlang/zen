import Zen.Init



namespace Zen.Fs

export System (FilePath)



/-- Copies a file.

- `cp`: allows to modifies the content before it is copied;
- `overwrite`: (de)activates failure if the file already exists.
-/
def cpFile (src tgt : FilePath)
  (cp : String → IO.FS.Handle → IO Unit :=
    fun txt h => do
      h.putStr txt
      h.flush)
  (overwrite := false)
: IO PUnit := do
  let err blah :=
    IO.throwServerError s!"can't copy `{src}` to `{tgt}`{blah}"
  if ! (← src.pathExists) then
    err ", source does not exist"
  if ← src.isDir then
    err ", source is not a file"
  if ← tgt.isDir then
    err ", target exists and is a directory"
  if ¬ overwrite ∧ (← tgt.pathExists) then
    err ", target exists and overwrite is deactivated"
  let content ← IO.FS.readFile src
  let handle ← IO.FS.Handle.mk tgt IO.FS.Mode.write
  cp content handle
