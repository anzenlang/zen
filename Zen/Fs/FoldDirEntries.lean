import Zen.Fs.Init



namespace Zen.Fs

open IO.FS (DirEntry)



/-- Actions for `foldDirEntries` and similar functions. -/
inductive FoldDirEntries.Action (α : Type) : Type
| yield : α → Action α
| skip : Action α
| done : α → Action α
deriving Inhabited

/-- Internal `foldDirEntries` actions. -/
inductive FoldDirEntries.LoopAction (α : Type) : Type
| yield : α → LoopAction α
| done : α → LoopAction α
deriving Inhabited

/-- Directory exploration depth. -/
inductive Depth
| unlimited
| limited : Nat → Depth

namespace Depth
instance instCoeOfNat : Coe Nat Depth :=
  ⟨limited⟩

def isZero : Depth → Bool
| limited 0 => true
| limited (_ + 1) | unlimited => false

/-- Yields `none` on `limited 0`. -/
def dec : Depth → Option Depth
| limited 0 => none
| limited (d + 1) => limited d
| unlimited => unlimited
end Depth

open FoldDirEntries in
/-- Folds recursively over the entries of a directory.

- `depth`: optionally limits the exploration depth.
-/
partial def foldDirEntries
  (path : FilePath)
  (f : α → IO.FS.DirEntry → IO (Action α))
  (init : α)
  (depth : Depth := .unlimited)
: IO α := do
  let entries ← path.readDir
  match ← loop depth init entries with
  | .yield res => return res
  | .done res => return res
where
  loop
    (depth : Depth) (acc : α) (entries : Array DirEntry)
  : IO (LoopAction α) := do
    let mut acc := acc
    for entry in entries do
      let path := entry.path
      println! "current entry: {path}"
      -- ask user what to do
      match ← f acc entry with
      -- keep going
      | .yield nuAcc =>
        let isDir ← path.isDir
        match isDir, depth.dec with
        -- not a dir, or we're asked not to go deeper
        | false, _ | _, none =>
          acc := nuAcc
          continue
        -- directory we need to go down into
        | true, some nuDepth =>
          let entries ← path.readDir
          -- loop with decreased depth (if any)
          match ← loop nuDepth nuAcc entries with
          | .yield nuAcc =>
            -- keep going
            acc := nuAcc
            continue
          | .done nuAcc =>
            -- done, propagate upwards
            return .done nuAcc
      -- skip this entry
      | .skip => continue
      -- done, propagate upwards
      | .done res => return .done res
    -- normal exit, yield new accumulator
    return .yield acc

/-- Folds recursively over the files in a directory.

- `depth`: optionally limits the exploration depth;
- `skip`: skip files/directory for which this function returns `true`.
-/
def foldFilesIn (path : FilePath)
  (f : α → DirEntry → IO α)
  (init : α)
  (depth := Depth.unlimited)
  (skip : DirEntry → IO Bool := fun _ => return false)
: IO α := do
  init |> foldDirEntries (depth := depth) path
    fun acc entry => do
      if ← skip entry then
        return .skip
      if ← entry.path.isDir then
        return .yield acc
      return .yield (← f acc entry)

/-- Same as `foldFilesIn` with no accumulator. -/
def iterFilesIn (path : FilePath)
  (f : DirEntry → IO PUnit)
  (depth := Depth.unlimited)
  (skip : DirEntry → IO Bool := fun _ => return false)
: IO PUnit :=
  foldFilesIn (depth := depth) (skip := skip) path (𝕂 f) ()
