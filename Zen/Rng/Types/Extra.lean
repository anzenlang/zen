import Zen.Rng.Types.Basic



/-! # `Rng.Random` instances for type constructors -/
namespace Zen.Rng



variable [Monad m] [RandomGen Gen]



section prod
variable {α β : Type u} [instA : Random m α] [instB : Random m β]

/-- Generates a random product. -/
def genProd
  (c : instA.Constraint × instB.Constraint := Constraint.none)
: RandGT Gen m (α × β) := do
  let a ← gen c.1
  let b ← gen c.2
  return (a, b)

instance : Random m (α × β) :=
  .mk (instA.Constraint × instB.Constraint) (genProd ·)
end prod



/-- Generates a random option.

The `Rng.Constraint.Plain` constraint `c.1` specifies the odds of getting `none`: one in `c.1.succ`
(ten if `none`).
-/
def genOption
  [inst : Random m α]
  (c : (Rng.Constraint.Plain Nat) × inst.Constraint)
: RandGT Gen m (Option α) := do
  let odds := c.1.getD 9
  let n : Fin odds.succ ← gen
  if n = 0 then return none else some <$> gen c.2

instance [inst : Random m α] : Random m (Option α) :=
  Random.mk (((Rng.Constraint.Plain Nat) × inst.Constraint)) genOption


/-- Collection RNG specification.

An instance `Coll m γ` with a `R : Random m α` instance implies `Random m (γ α)` with constraint
type `Constraint.Bounds Nat × R.C`
``
-/
protected class Coll (m : Type → Type) (γ : Type → Type) where
  /-- Builds an empty collection given a length hint. -/
  empty {Gen : Type} : (length : Nat) → RandGT Gen m (γ α)
  /-- Adds an element to a collection. -/
  add {Gen : Type} : (γ α) → Nat → α → RandGT Gen m (γ α)

namespace Coll
variable [self : Rng.Coll m γ]


/-- Generates a collection of length `length` with random elements. -/
def genWithLength
  (length : Nat)
  (genElm : Nat → RandGT Gen m α)
: RandGT Gen m (γ α) := do
  let mut acc ← self.empty length
  for i in [0:length] do
    acc ← self.add acc i (← genElm i)
  return acc

/-- Generates a collection of potentially random length with random elements. -/
def genWithLength?
  (length? : Option Nat)
  (genElm : Nat → RandGT Gen m α)
: RandGT Gen m (γ α) := do
  let len ←
    if let some len := length?
    then pure len
    else gen
  genWithLength len genElm

instance instRandom [R : Random m α] : Random m (γ α) :=
  .mk
    (Constraint.Bounds Nat × R.Constraint)
    fun c => do
      let len ← gen' Nat c.1
      self.genWithLength len (𝕂 $ gen c.2)

instance instCollList : Rng.Coll m List where
  empty _ := return []
  add tl _ hd := return hd :: tl

instance instCollArray : Rng.Coll m Array where
  empty size := return Array.mkEmpty size
  add array _ next := return array.push next

end Coll

section coll
variable [Monad m] [RandomGen Gen] [Rng.Coll m γ]

/-- Generates a random collection with constrained random elements.

See also `Rng.genColl'`.
-/
protected def genColl {α : outParam Type} [R : Random m α]
  (c : Constraint.Bounds Nat × R.Constraint := Constraint.none)
: RandGT Gen m (List α) :=
  Coll.instRandom.gen c

/-- Generates a random collection with unconstrained random elements.

See also `Rng.genColl`.
-/
protected def genColl' {α : outParam Type} [Random m α]
  (c : Constraint.Bounds Nat := Constraint.none)
: RandGT Gen m (List α) :=
  Coll.instRandom.gen (c, Constraint.none)
end coll
