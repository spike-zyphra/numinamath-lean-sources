import Mathlib

theorem algebra_299919 {x y : ℝ} (h₁ : x * y + x + y = 17) (h₂ : x^2 * y + x * y^2 = 66) :
    x^4 + x^3 * y + x^2 * y^2 + x * y^3 + y^4 = 12499 := by
  have eq1 : x * y = 17 - (x + y) := by
    linarith
  have eq2 : (x * y) * (x + y) = 66 := by
    linarith
  have h4 : (x + y) ^ 2 - 17 * (x + y) + 66 = 0 := by
    have h5 : (x * y) = 17 - (x + y) := by linarith
    rw [h5] at eq2
    linarith
  have : (x + y - 11) * (x + y - 6) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 this) with h6 h7
  · -- x + y = 11
    have hS11 : x + y = 11 := by linarith
    have h4 : x * y = 6 := by
      have : x * y = 17 - (x + y) := by linarith
      rw [hS11] at this
      linarith
    have eq1 : x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4 = (x + y) ^ 4 - 3 * (x * y) * (x + y) ^ 2 + (x * y) ^ 2 := by
      ring
    rw [eq1, hS11, h4]
    nlinarith
  · -- x + y = 6
    have hS6 : x + y = 6 := by linarith
    have h4 : x * y = 11 := by
      have : x * y = 17 - (x + y) := by linarith
      rw [hS6] at this
      linarith
    have eq1 : x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4 = (x + y) ^ 4 - 3 * (x * y) * (x + y) ^ 2 + (x * y) ^ 2 := by
      ring
    rw [eq1, hS6, h4]
    nlinarith