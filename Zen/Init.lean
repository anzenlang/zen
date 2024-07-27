import Batteries

/-! # Basic types and helpers -/



/-! ## Extensions -/
section ext

def Prod.swap : α × β → β × α
| (a, b) => (b, a)

end ext



namespace Zen


/-- The `𝕂`onstant combinator. -/
def 𝕂 (val : α) (_ : β) : α :=
  val

/-- Empty string on `1`, `"s"` otherwise. -/
def plural : Nat → String
| 1 => ""
| _ => "s"

/-- Identity over `IO _`.

Useful to force a meta-variable for a monad to resolve to `IO`, for `#eval` in particular.
-/
def inIO : IO α → IO α :=
  id
