import Mathlib

theorem algebra_98752 (x y : ℝ) (h : x^2 - 2 * x * y + y^2 - Real.sqrt 2 * x - Real.sqrt 2 * y + 6 = 0)
    (u : ℝ) (hu : u = x + y) :
    u ≥ 3 * Real.sqrt 2 := by
  have eq1 : (x - y) ^ 2 = Real.sqrt 2 * u - 6 := by
    rw [show u = x + y from hu]
    nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h1 : Real.sqrt 2 * u - 6 ≥ 0 := by
    have h2 : (x - y) ^ 2 ≥ 0 := by
      nlinarith
    linarith [eq1, h2]
  have h2 : u ≥ 3 * Real.sqrt 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
      mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (Real.sqrt_nonneg (2 : ℝ)), h1
    ]
  exact h2