import Mathlib

theorem algebra_300447 (x y : ℝ) (h₁ : |y - 2| ≤ 1) (h₂ : x + y = 3) :
    2 * x ^ 2 - 12 * x + y ^ 2 + 1 ≥ -14 := by
  have h3 : 1 ≤ y := by
    linarith [abs_le.mp h₁]
  have h4 : y ≤ 3 := by
    linarith [abs_le.mp h₁]
  have hx : x = 3 - y := by
    linarith
  rw [hx]
  nlinarith [sq_nonneg (y - 1), sq_nonneg (y - 3), h3, h4]