import Mathlib

theorem algebra_285580 (x : ℝ) (hx : x = Real.sqrt (19 - 8 * Real.sqrt 3)) :
    ((x ^ 4 - 6 * x ^ 3 - 2 * x ^ 2 + 18 * x + 23) / (x ^ 2 - 8 * x + 15)) = 5 := by
  have h1 : x = 4 - Real.sqrt 3 := by
    rw [hx]
    have h2 : Real.sqrt (19 - 8 * Real.sqrt 3) = 4 - Real.sqrt 3 := by 
      have h4 : (4 - Real.sqrt 3) ^ 2 = 19 - 8 * Real.sqrt 3 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h5 : 4 - Real.sqrt 3 ≥ 0 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      rw [←h4]
      field_simp [Real.sqrt_sq h5]
    exact h2
  rw [h1]
  have h6 : (4 - Real.sqrt 3 : ℝ) ^ 2 - 8 * (4 - Real.sqrt 3) + 15 ≠ 0 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3
    ]
  field_simp [h6]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3
  ]