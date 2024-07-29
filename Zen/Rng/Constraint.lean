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

Used for types which RNG cannot be constrained such as `Bool` and `Fin n.succ`.
-/
def None : Type u := PUnit

namespace None
instance instConstraint : Rng.Constraint None :=
  ⟨()⟩
end None



/-- A plain value to interpret as a constraint. -/
abbrev Plain (α : Type u) := Option α

namespace Plain
instance instConstraint : Rng.Constraint (Plain α) :=
  ⟨none⟩
end Plain



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



/-- `[lo ; hi]` is `Rng.Constraint.Bounds.between lo hi`.

## Variants

- `[lo ; hi | ty]`: ensures the type of `lo`/`hi` is `ty`;
- `[val]`: `Rng.Constraint.Bounds.exact val`;
- `[val | ty]`: ensures the type of `val` is `ty`.
-/
scoped syntax (name := rngV1) "[" term (" ; " term)? (" |" term)? "]" : term

/-- `[≤ hi]` is `Rng.Constraint.Bounds.ubound hi`.

## Variants

- `[≤ hi | ty]`: ensures the type of `hi` is `ty`.
-/
scoped syntax (name := rngV2) "[" " ≤ " term (" |" term)? "]" : term

/-- `[≥ hi]` is `Rng.Constraint.Bounds.lbound hi`.

## Variants

- `[≥ hi | ty]`: ensures the type of `hi` is `ty`.
-/
scoped syntax (name := rngV3) "[" " ≥ " term (" |" term)? "]" : term

macro_rules
| `(rngV1| [$lo | $ty]) => `(
  _root_.Zen.Rng.Constraint.Bounds.exact ($lo : $ty)
)
| `(rngV1| [$lo ; $hi | $ty]) => `(
  _root_.Zen.Rng.Constraint.Bounds.between ($lo : $ty) ($hi : $ty)
)
| `(rngV2| [≤ $hi | $ty]) => `(
  _root_.Zen.Rng.Constraint.Bounds.ubound ($hi : $ty)
)
| `(rngV3| [≥ $lo | $ty]) => `(
  _root_.Zen.Rng.Constraint.Bounds.lbound ($lo : $ty)
)

| `(rngV1| [$lo]) => `(
  _root_.Zen.Rng.Constraint.Bounds.exact $lo
)
| `(rngV1| [$lo ; $hi]) => `(
  _root_.Zen.Rng.Constraint.Bounds.between $lo $hi
)
| `(rngV2| [≤ $hi]) => `(
  _root_.Zen.Rng.Constraint.Bounds.ubound $hi
)
| `(rngV3| [≥ $lo]) => `(
  _root_.Zen.Rng.Constraint.Bounds.lbound $lo
)
