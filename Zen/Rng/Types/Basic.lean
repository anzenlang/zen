import Zen.Rng.Random



/-! # `Rng.Random` instances for simple types -/
namespace Zen.Rng



variable [Monad m] [RandomGen Gen]



/-- Generates an unconstrained `Nat`. -/
def genAnyNat : RandGT Gen m Nat := fun gen =>
  let (n, gen) := RandomGen.next gen.down
  return (n, ULift.up gen)



section fin
variable {n : Nat}

/-- Generates a random `Fin (n + 1)`. -/
def genFin : RandGT Gen m (Fin n.succ) := do
  let n ← genAnyNat
  return Fin.ofNat n

instance instRandomFin : Random m (Fin n.succ) :=
  .mk Constraint.None (𝕂 genFin)

end fin



/-- Generates a `Nat` within some bounds. -/
def genNat : (c : Constraint.Bounds Nat := .none) → RandGT Gen m Nat
| ⟨none, none⟩ =>
  genAnyNat
| ⟨lo?, some hi⟩ => do
  let lo := lo?.getD 0
  let fin ← genFin (n := hi - lo)
  return lo + fin.val
| ⟨some lo, none⟩ =>
  (· + lo) <$> genAnyNat

instance instRandomNat : Random m Nat :=
  .mk (Constraint.Bounds Nat) (genNat ·)



/-- Generates a random `Bool`. -/
def genBool : RandGT Gen m Bool :=
  return (← gen' (Fin 2)) = 1

instance instRandomBool : Random m Bool :=
  .mk Constraint.None (𝕂 genBool)



/-- Generates an unconstrained `Int`. -/
def genAnyInt : RandGT Gen m Int := do
  let pos ← genBool
  if pos then
    return Int.ofNat (← genNat)
  else
    return Int.negSucc (← genNat)

/-- Generates a random `Int`. -/
def genInt : (c : Constraint.Bounds Int := .none) → RandGT Gen m Int
| ⟨none, none⟩ => genAnyInt
| ⟨none, some hi⟩ => do
  let n ← gen' Nat
  return hi - n
| ⟨some lo, none⟩ => do
  let n ← gen' Nat
  return lo + n
| ⟨some lo, some hi⟩ => do
  let range := (hi - lo).natAbs
  let n ← genFin (n := range)
  return lo + n

instance instRandomInt : Random m Int :=
  .mk (Constraint.Bounds Int) (genInt ·)



/-- Generates an unconstrained random `Float`, this function does not give very varied values.

Use `Rng.genAnyFloat`, `Rng.genFloat` or just `Rng.gen`/`Rng.gen'` instead.
-/
private def genBadFloat : RandGT Gen m Float := do
  let num ← Float.ofInt <$> genInt
  -- make sure `den` can't be zero
  --  vvv                  vvvvvvvv
  let den ← (Float.ofNat ∘ Nat.succ) <$> genNat
  return num / den

/-- Generates a `Float` between `0` and `1`. -/
protected def genUnitFloat : RandGT Gen m Float := do
  let f ← Rng.genBadFloat
  return 0.5 + f.cos / 2

/-- Generates an unconstrained random `Float`. -/
protected def genAnyFloat : RandGT Gen m Float := do
  let int ← Float.ofInt <$> gen' Int
  let dec ← Rng.genUnitFloat
  return int + dec

/-- Generates a random `Float`. -/
def genFloat : (c : Constraint.Bounds Float := .none) → RandGT Gen m Float
| ⟨none, none⟩ => Rng.genAnyFloat
| ⟨none, some hi⟩ => (hi - ·) <$> Rng.genAnyFloat
| ⟨some lo, none⟩ => (· + lo) <$> Rng.genAnyFloat
| ⟨some lo , some hi⟩ => do
  let factor ← Rng.genUnitFloat
  return lo + factor * (hi - lo)

instance instRandomFloat : Random m Float :=
  .mk (Constraint.Bounds Float) (genFloat ·)
