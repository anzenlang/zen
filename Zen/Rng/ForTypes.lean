import Zen.Rng.Basic



/-! # Random generation for specific types -/
namespace Zen.Rng

variable [RandomGen Gen] [Monad m]



/-- Generates a random `Nat`. -/
def genNat : RandGT Gen m Nat := gen



/-- Generates a random `Fin (n + 1)`. -/
def genFin {n : Nat} : RandGT Gen m (Fin n.succ) := do
  let n ← genNat
  return Fin.ofNat n

instance {n : Nat} : Random m (Fin n.succ) :=
  ⟨genFin⟩



/-- Generates a random `Bool`. -/
def genBool : RandGT Gen m Bool :=
  return (← gen' (Fin 2)) = 1

instance : Random m Bool :=
  ⟨genBool⟩



/-- Generates a random `Int`. -/
def genInt : RandGT Gen m Int := do
  let n ← genNat
  let pos ← genBool
  if pos then
    return Int.ofNat n
  else
    return Int.negSucc n

instance : Random m Int :=
  ⟨genInt⟩



/-- Generates a random `Float`.

Consider using `genFloat` instead.
-/
protected def genFloat' : RandGT Gen m Float := do
  let num ← Float.ofInt <$> genInt
  -- make sure `den` can't be zero
  --                       vvvvvvvv
  let den ← (Float.ofNat ∘ Nat.succ) <$> genNat
  return num / den

/-- Generates a random `Float` between `0` and `1`.

See also `Rng.genFloat`.

# TODO

- super naive implementation
- add `lo ≤ hi` constraint?
-/
def genFloatBounded (lo hi : Float) : RandGT Gen m Float := do
  let f ← Rng.genFloat'
  return lo + (0.5 + f.cos / 2) * (hi - lo)

/-- Generates a random `Float`.

- `normalized`: if true the result will be in `[0, 1]`

See also `Rng.genFloatBounded`.
-/
def genFloat (normalized := false) : RandGT Gen m Float :=
  if normalized then
    genFloatBounded 0 1
  else
    Rng.genFloat'

/-- info:
0.513177
0.265150
0.003262
0.634325
0.002402
-/
#guard_msgs in #eval do
  inIO <| Rng.runStdWith 0 do
    for _ in [0:5] do
      let f ← genFloatBounded 0 1
      println! "{f}"



/-- Repeats an action over an accumulator something `n` times, where `n` is specified or random.

- `acc : Nat → α` initializes the accumulator given the actual `count` value.
-/
def accumulate
  (acc : Nat → α)
  (f : Nat → α → RandGT Gen m α)
  (count : Option Nat)
: RandGT Gen m α := do
  let count ←
    if let some count := count
    then pure count else gen
  let mut acc := acc count
  for i in [0 : count] do
    acc := (← f i acc)
  return acc



/-- Generates a random `List`. -/
def genList [Random m α] (length : Option Nat := none) : RandGT Gen m (List α) :=
  length |> accumulate (𝕂 [])
    fun _ list => list.cons <$> gen

instance [Random m α] : Random m (List α) :=
  ⟨genList⟩



/-- Generates a random `Array`. -/
def genArray [Random m α] (size : Option Nat := none) : RandGT Gen m (Array α) :=
  size |> accumulate (fun size => Array.mkEmpty size)
    fun _ array => array.push <$> gen

instance [Random m α] : Random m (Array α) :=
  ⟨genArray⟩



/-! ## Bounded random generation -/

instance : RandomBounded m Nat where
  randomBounded lo hi _ := do
    let fin ← gen' (Fin (hi - lo).succ)
    return lo + fin.val

instance : RandomBounded m Int where
  randomBounded lo hi _ := do
    let n : Nat ← genBounded 0 (hi - lo).natAbs
    return lo + n

instance : RandomBounded m Float where
  randomBounded lo hi _ := do
    genFloatBounded lo hi

instance {n : Nat} : RandomBounded m (Fin n.succ) where
  randomBounded lo hi _ := do
    let n ← genBounded lo.val hi.val
    return Fin.ofNat n



/-- Generates a random `List` with bounded random elements. -/
def genListBounded [RandomBoundedBy ι m α]
  (lo hi : ι)
  (length : Option Nat := none)
: RandGT Gen m (List α) :=
  length |> accumulate (𝕂 [])
    fun _ list => list.cons <$> genBounded lo hi

/-- Generates a random `List` with bounded length. -/
def genBoundedList [Random m α] (lengthLo lengthHi : Nat) : RandGT Gen m (List α) := do
  let length ← genBounded lengthLo lengthHi
  genList (some length)

/-- Generates a random `List` with bounded length and elements. -/
def genBoundedListBounded [RandomBoundedBy ι m α]
  (lengthLo lengthHi : Nat)
  (elemLo elemHi : ι)
: RandGT Gen m (List α) := do
  let length ← genBounded lengthLo lengthHi
  genListBounded elemLo elemHi (some length)

instance [Random m α] : RandomBoundedBy Nat m (List α) where
  randomBounded lo hi _ :=
    genBoundedList lo hi



/-- Generates a random `List` with bounded random elements. -/
def genArrayBounded [RandomBoundedBy ι m α]
  (lo hi : ι)
  (length : Option Nat := none)
: RandGT Gen m (Array α) :=
  length |> accumulate Array.mkEmpty
    fun _ array => array.push <$> genBounded lo hi

/-- Generates a random `Array` with bounded length. -/
def genBoundedArray [Random m α] (lengthLo lengthHi : Nat) : RandGT Gen m (Array α) := do
  let length ← genBounded lengthLo lengthHi
  genArray (some length)

/-- Generates a random `Array` with bounded length and elements. -/
def genBoundedArrayBounded [RandomBoundedBy ι m α]
  (lengthLo lengthHi : Nat)
  (elemLo elemHi : ι)
: RandGT Gen m (Array α) := do
  let length ← genBounded lengthLo lengthHi
  genArrayBounded elemLo elemHi (some length)

instance [Random m α] : RandomBoundedBy Nat m (Array α) where
  randomBounded lo hi _ :=
    genBoundedArray lo hi
