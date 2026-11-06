import Mathlib

theorem algebra_111569 (x y z : ℝ) (h₀ : x + y + z = 2) (h₁ : x * y + y * z + z * x = 1) :
    x - y ≤ 2 * √3 / 3 := by

  have h2 : z = 2 - x - y := by nlinarith
  rw [h2] at h₁

  nlinarith [sq_nonneg (x + y - 4 / 3), sq_nonneg (x - (2 + Real.sqrt 3) / 3), sq_nonneg (y - (2 - Real.sqrt 3) / 3), sq_nonneg (y - (2 + Real.sqrt 3) / 3), sq_nonneg (x - (2 - Real.sqrt 3) / 3),
            Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num),
            Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]