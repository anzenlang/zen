import Zen.Rng.Basic
import Zen.Rng.Constraint



/-! # Main class for random generation -/
namespace Zen.Rng



/-- Specifies random generation of `α`-values. -/
class Random (m : Type u → Type v) (α : Type u) : Type (max (max u 1) v) where mkRaw ::
  /-- The constraint-style supported the random generation.

  For instance, `C = Constraint.Bounds Nat` for `Nat`.
  -/
  Constraint : Type
  /-- `C` must be a `Constraint` so that `gen` has a default (vacuous) constraint `C`-value. -/
  isConstraint : Rng.Constraint Constraint
  /-- Generates a random `α`-value given some constraint (visible as `Zen.Rng.gen`).

  See also `Rng.gen'`, where `α` is explicit.
  -/
  gen [RandomGen Gen] (constraint : Constraint := Rng.Constraint.none) : RandGT Gen m α

namespace Random

instance instConstraint [inst : Random m α] : Rng.Constraint inst.Constraint :=
  inst.isConstraint

/-- Builds a `Random` instance, retrieve the `Constraint C` instance from the context. -/
def mk
  (C : Type) [inst : Rng.Constraint C]
  (g : {Gen : Type} → [RandomGen Gen] → (constraint : C := Constraint.none) → RandGT Gen m α)
: Random m α :=
  ⟨C, inst, (g ·)⟩

/-- Generates a random `α`-value given some constraint (visible as `Zen.Rng.gen'`).

See also `Rng.gen`, where `α` is implicit.
-/
def gen'
  (α : Type u)
  [self : Random m α] [RandomGen Gen]
  (constraint : self.Constraint := Constraint.none)
: RandGT Gen m α :=
  gen constraint

end Random

export Random (gen gen')
