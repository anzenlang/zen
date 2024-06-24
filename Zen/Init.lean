import Lean



namespace Zen


/-- The `𝕂`onstant combinator. -/
def 𝕂 (val : α) (_ : β) : α :=
  val

/-- Empty string on `0` and `1`, `"s"` otherwise. -/
def plural : Nat → String
| 0 | 1 => ""
| _ => "s"

/-- Haskell's `liftM`, wraps a function's domain and codomain in a monad. -/
def liftF [Functor M] (f : α → β) : M α → M β :=
  (f <$> ·)
