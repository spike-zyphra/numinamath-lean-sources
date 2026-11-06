import Mathlib

theorem algebra_275996 (x y : ℤ) :
    2 * x ^ 2 + 2 * y ^ 2 ∣ (x ^ 2 - x * y + y ^ 2) ^ 3 + (x ^ 2 + x * y + y ^ 2) ^ 3 := by
  have eq : (x ^ 2 - x * y + y ^ 2) ^ 3 + (x ^ 2 + x * y + y ^ 2) ^ 3 =
    2 * ((x ^ 2 + y ^ 2) * ( (x^2 + y^2)^2 + 3 * (x * y)^2 )) := by
    ring
  rw [eq] at *
  use ( (x ^ 2 + y ^ 2) ^ 2 + 3 * (x * y) ^ 2 )
  all_goals
    ring