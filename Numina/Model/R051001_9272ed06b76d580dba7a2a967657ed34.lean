import Mathlib

theorem calculus_155793 (s : ℝ → ℝ) (h₀ : s = fun t => 2 * t ^ 2 + 3 * t - 1) :
    (deriv s 3) ^ 2 * 8 / 2 = 900 := by 
  rw [h₀]
  -- compute the derivative at 3
  simp [deriv_pow, deriv_mul, deriv_id', mul_comm]
  -- norm_num is powerful enough to compute derivatives of polynomial at a point
  -- s(t) = 2t^2 + 3t - 1, s'(t) = 4t + 3, so s'(3) = 4 * 3 + 3 = 15
  norm_num [deriv_const]