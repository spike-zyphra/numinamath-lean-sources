import Mathlib

/- Our basketball team has 12 members, each of whom can play any position.  In how many ways can we choose a starting lineup consisting of a center, a power forward, a shooting forward, a point guard, and a shooting guard? -/
theorem algebra_14876 : Nat.choose 12 5 * Nat.factorial 5 = 95040 := by
  rfl