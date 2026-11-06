import Mathlib

theorem algebra_243171 (x y z : ℝ) (h₀ : x + y - 2 - 4 * x * y = 0) (h₁ : y + z - 2 - 4 * y * z = 0)
    (h₂ : z + x - 2 - 4 * z * x = 0) :
    False := by
  have eq1 : (z - x) * (1 - 4 * y) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp eq1) with h3 h4 
  · -- Case where z = x 
    have h5 : z = x := by linarith
    have h6 : z + x - 2 - 4 * z * x = 0 := h₂
    rw [show z = x by linarith [h5]] at h6 
    nlinarith [sq_nonneg (x - 1 / 4), sq_nonneg (y - 1 / 4), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
  · -- Case where y = 1/4 
    have h7 : y = 1 / 4 := by linarith 
    rw [show y = 1 / 4 by linarith [h7]] at h₀ 
    nlinarith [sq_nonneg (x - 1 / 4), sq_nonneg (y - 1 / 4), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]