import Mathlib

theorem algebra_325772 (x y z : ℝ) (h₀ : x + y + z = 5) (h₁ : x * y + y * z + z * x = 3) :
    z ≤ 13 / 3 := by
  have h2 : x + y = 5 - z := by
    linarith
  have h3 : x * y = z^2 - 5 * z + 3 := by 
    have eq1 : x * y + z * (x + y) = 3 := by
      nlinarith
    rw [h2] at eq1
    nlinarith
  have h4 : (x + y)^2 - 4 * (x * y) ≥ 0 := by
    nlinarith [sq_nonneg (x - y)]
  rw [h2, h3] at h4
  nlinarith [sq_nonneg (z - 13 / 3), sq_nonneg (z + 1)]