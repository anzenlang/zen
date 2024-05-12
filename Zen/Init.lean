import Batteries



namespace Zen


/-- The `𝕂`onstant combinator. -/
def 𝕂 (val : α) (_ : β) : α :=
  val

/-- Empty string on `0` and `1`, `"s"` otherwise. -/
def plural : Nat → String
| 0 | 1 => ""
| _ => "s"
