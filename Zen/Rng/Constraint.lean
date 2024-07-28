import Zen.Init



/-! ## RNG constraints -/
namespace Zen.Rng



/-- An RNG constraint, specifies an "unconstrained" constructor. -/
protected class Constraint (α : Type u) where
  /-- Creates a constrainless constraint. -/
  protected none : α

namespace Constraint

instance instConstraintProd
  [Rng.Constraint α] [Rng.Constraint β]
: Rng.Constraint (α × β) :=
  ⟨Constraint.none, Constraint.none⟩



/-- Allows no RNG contraint.

Used by for types which RNG cannot be constrained such as `Bool` and `Fin n.succ`.
-/
def None : Type u := PUnit

namespace None
instance instConstraint : Rng.Constraint None :=
  ⟨()⟩
end None



/-- Inclusive open interval.

Sadly, when `low? = some low` and `high? = some high` we have no proof that `low ≤ high` and the
interval does not make sense RNG-wise (generates no value). The behavior when `high < low` is
unspecified, but it's safe and does not crash.

The main reason there is no `low ≤ high` proof is so that working with `Float` is not too much of a
pain.
-/
structure Bounds (α : Type u) where
  /-- Optional lower bound. -/
  low? : Option α
  /-- Optional upper bound. -/
  high? : Option α

namespace Bounds

/-- Creates an interval. -/
def between (lo hi : α)
: Bounds α := ⟨lo, hi⟩

/-- Creates an interval containing just `val`. -/
def exact (val : α) : Bounds α :=
  between val val

/-- Lower bound and no upper bound. -/
def lbound (lo : α) : Bounds α :=
  ⟨some lo, none⟩

/-- Upper bound and no lower bound. -/
def ubound (hi : α) : Bounds α :=
  ⟨none, some hi⟩

/-- Unconstrained bounds. -/
protected def none : Bounds α :=
  ⟨none, none⟩

instance instConstraint : Rng.Constraint (Bounds α) :=
  ⟨Bounds.none⟩

variable (self : Bounds α)

/-- True if both bounds are `none`. -/
def isNone : Bool :=
  self.low?.isNone ∧ self.high?.isNone

/-- `Prod`uct of two bounds. -/
@[inline]
def and (that : Bounds β) : Bounds α × Bounds β :=
  (self, that)

/-- `Prod`uct of two bounds, same as `Bounds.and`.

Useful when specifying a collection. For instance, the constraint \
(of type `Bounds Nat × Bounds Int`) for `List Int` values with length in `[3; 5]` and elements in
`[-2; 2]` can be written as `[3; 5].withElems [-2; 2]`, which is really `([3; 5], [-2; 2])` but
conveys more meaning.
-/
@[inline]
def withElems := @and

end Bounds

end Constraint

export Constraint (Bounds)
