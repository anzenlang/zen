import Zen.Init



/-! # Random number generation (RNG)

RNG library shamelessly ~~stolen from~~ inspired by [mathlib's], but with relaxed constraints and
guarantees. In particular, no need for `Preorder α` for bounded RNG.

[mathlib's]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Control/Random.html
-/
namespace Zen.Rng


/-- (State-)monad transformer with custom generator. -/
abbrev RandGT (Gen : Type) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  StateT (ULift Gen) m α

/-- (State-)monad with custom generator. -/
abbrev RandG (Gen : Type) (α : Type u) : Type u :=
  RandGT Gen Id α

/-- (State-)monad transformer with `StdGen` generator. -/
abbrev RandT (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  RandGT StdGen m α

/-- (State-)monad with `StdGen` generator. -/
abbrev Rand (α : Type u) : Type u :=
  RandT Id α

instance [MonadLift m m'] : MonadLift (RandGT Gen m) (RandGT Gen m') where
  monadLift x s := x s



/-! ## Helpers/runners -/

section rng

namespace RandG
instance instMonadLift [Monad m] : MonadLift (RandG Gen) (RandGT Gen m) where
  monadLift randG state := do
    let (res, state) := randG state
    return (res, state)
end RandG



variable [RandomGen Gen] [Monad m]



/-- Runs RNG code given a generator, returns the result and the updated generator state.

See also `Rng.run`.
-/
def run' (code : RandGT Gen m α) (gen : Gen) : m (α × Gen) := do
  let (res, gen) ← code.run (ULift.up gen)
  return (res, gen.down)

/-- Runs RNG code given a generator, discards the final generator state.

See also `Rng.run'`
-/
def run (code : RandGT Gen m α) (gen : Gen) : m α :=
  Prod.fst <$> run' code gen

/-- Runs `StdGen`-RNG code with a seed.

See also `Rng.runStd` to use the environment's generator.
-/
def runStdWith (seed : Nat) (code : RandT m α) : m α :=
  let stdGen := mkStdGen seed
  run code stdGen

/-- Runs `StdGen`-RNG code using the generator from `IO.RealWorld` if no seed is provided.

If `seed?.isSome`, this function is the same as `Rng.runStdWith`.
-/
def runStd [MonadLiftT (ST IO.RealWorld) m]
  (code : RandT m α) (seed? : Option Nat := none)
: m α :=
  if let some seed := seed? then
    runStdWith seed code
  else do
    let stdGen ← IO.stdGenRef.get
    let (res, stdGen) ← run' code stdGen
    IO.stdGenRef.set stdGen
    return res



/-- Generator state accessor. -/
def getRngState : RandGT Gen m Gen := do
  return (← get).down

/-- Performs a read/write operation on the generator. -/
def rngStateDo (f : Gen → (α × Gen)) : RandGT Gen m α := do
  let rng ← getRngState
  let (res, rng) := f rng
  set (ULift.up rng)
  return res

/-- Applies a read operation on the generator. -/
def rngStateApply (f : Gen → α) : RandGT Gen m α :=
  rngStateDo (fun gen => (f gen, gen))

/-- Splits the generator in two, useful for recursion/branching. -/
def split : RandGT Gen m Gen :=
  -- the `Prod.swap` is not really needed, it's just to match mathlib's version
  rngStateDo <| Prod.swap ∘ RandomGen.split

/-- The range of values of the generator. -/
def range : RandGT Gen m (Nat × Nat) :=
  rngStateApply RandomGen.range

end rng
