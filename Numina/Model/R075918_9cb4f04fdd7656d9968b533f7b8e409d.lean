import Mathlib

theorem algebra_199605 {x y z : ℝ} (h₀ : x^2 + y^2 + z^2 = 1) (h₁ : x + 2 * y + 3 * z = Real.sqrt 14) :
    x = Real.sqrt 14 / 14 ∧ y = 2 * Real.sqrt 14 / 14 ∧ z = 3 * Real.sqrt 14 / 14 := by
  have h2 : (x - Real.sqrt 14 / 14)^2 + (y - 2 * Real.sqrt 14 / 14)^2 + (z - 3 * Real.sqrt 14 / 14)^2 = 0 := by
    nlinarith [Real.sqrt_nonneg 14, Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num : (0 : ℝ) ≤ 14), sq_nonneg (x - Real.sqrt 14 / 14), sq_nonneg (y - 2 * Real.sqrt 14 / 14), sq_nonneg (z - 3 * Real.sqrt 14 / 14), 
                sq_nonneg (x + 2 * y + 3 * z - Real.sqrt 14), 
                sq_nonneg (x - Real.sqrt 14 / 14 - (y - 2 * Real.sqrt 14 / 14)), 
                sq_nonneg (x - Real.sqrt 14 / 14 - (z - 3 * Real.sqrt 14 / 14)), 
                sq_nonneg (y - 2 * Real.sqrt 14 / 14 - (z - 3 * Real.sqrt 14 / 14)), 
                mul_self_nonneg (Real.sqrt 14)
      ]
  have hx : x - Real.sqrt 14 / 14 = 0 := by 
    nlinarith [sq_nonneg (x - Real.sqrt 14 / 14), sq_nonneg (y - 2 * Real.sqrt 14 / 14), sq_nonneg (z - 3 * Real.sqrt 14 / 14), h2]
  have hy : y - 2 * Real.sqrt 14 / 14 = 0 := by 
    nlinarith [sq_nonneg (x - Real.sqrt 14 / 14), sq_nonneg (y - 2 * Real.sqrt 14 / 14), sq_nonneg (z - 3 * Real.sqrt 14 / 14), h2]
  have hz : z - 3 * Real.sqrt 14 / 14 = 0 := by 
    nlinarith [sq_nonneg (x - Real.sqrt 14 / 14), sq_nonneg (y - 2 * Real.sqrt 14 / 14), sq_nonneg (z - 3 * Real.sqrt 14 / 14), h2]
  constructor
  · linarith
  constructor
  · linarith
  · linarith