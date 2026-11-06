import Mathlib

theorem algebra_268327 {x y : ℕ} (hy : y > 0) (h : x * 2 = y + 80 * x / 12) :
    x = 5 ∧ y = 10 := by
  have h1 : x < 6 := by
    omega
  interval_cases x <;> omega