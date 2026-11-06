import Mathlib

theorem algebra_2797 {x y : ℤ} (hx : x > 0) (hy : y > 0) (h : x^2 + y^2 + 4 * y - 96 = 0) : x * y = 32 ∨ x * y = 36 := by
  have h1 : x^2 + (y + 2)^2 = 100 := by linarith
  have h4 : x ≤ 9 := by
    nlinarith [h1]
  have h5 : y ≤ 8 := by
    nlinarith [h1]
  interval_cases x <;> interval_cases y
  <;> omega