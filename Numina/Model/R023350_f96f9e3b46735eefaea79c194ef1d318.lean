import Mathlib

theorem algebra_243924 {A : ℝ} (hA : A = (Real.sqrt 6 + Real.sqrt 2) * (Real.sqrt 3 - 2) * Real.sqrt (Real.sqrt 3 + 2)) :
    A = -2 := by 
  have h1 : Real.sqrt (Real.sqrt 3 + 2) = (Real.sqrt 6 + Real.sqrt 2) / 2 := by
    have h2 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
      calc
        Real.sqrt 6 = Real.sqrt (2 * 3) := by norm_num
        _ = Real.sqrt 2 * Real.sqrt 3 := by rw [Real.sqrt_mul (by norm_num)]
        _ = Real.sqrt 2 * Real.sqrt 3 := by ring
    have h3 : Real.sqrt (Real.sqrt 3 + 2) = (Real.sqrt 6 + Real.sqrt 2) / 2 := by
      have h4 : (Real.sqrt 6 + Real.sqrt 2) / 2 ≥ 0 := by
        positivity
      have h5 : ((Real.sqrt 6 + Real.sqrt 2) / 2) ^ 2 = Real.sqrt 3 + 2 := by
        nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (6 : ℝ),
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num),
          Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ),
          mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (Real.sqrt_nonneg (3 : ℝ)),
          h2, Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ)
        ]
      have h6 : Real.sqrt (Real.sqrt 3 + 2) = (Real.sqrt 6 + Real.sqrt 2) / 2 := by
        rw [← h5]
        field_simp [Real.sqrt_sq (show 0 ≤ (Real.sqrt 6 + Real.sqrt 2) / 2 by linarith [h4]), h4]
      exact h6
    exact h3
  rw [hA]
  rw [h1]
  have h7 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    calc
      Real.sqrt 6 = Real.sqrt (2 * 3) := by norm_num
      _ = Real.sqrt 2 * Real.sqrt 3 := by rw [Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 2 * Real.sqrt 3 := by ring
  -- Calculate (sqrt 6 + sqrt 2)^2
  have h8 : (Real.sqrt 6 + Real.sqrt 2) ^ 2 = 8 + 4 * Real.sqrt 3 := by
    calc
      (Real.sqrt 6 + Real.sqrt 2) ^ 2 = (Real.sqrt 6) ^ 2 + (Real.sqrt 2) ^ 2 + 2 * (Real.sqrt 6 * Real.sqrt 2) := by ring
      _ = 6 + 2 + 2 * (Real.sqrt 6 * Real.sqrt 2) := by rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
      _ = 8 + 2 * (Real.sqrt 6 * Real.sqrt 2) := by ring
      _ = 8 + 2 * (Real.sqrt 2 * Real.sqrt 3 * Real.sqrt 2) := by rw [h7]
      _ = 8 + 2 * (Real.sqrt 2 * Real.sqrt 2 * Real.sqrt 3) := by ring
      _ = 8 + 2 * (2 * Real.sqrt 3) := by rw [show Real.sqrt 2 * Real.sqrt 2 = 2 by rw [Real.mul_self_sqrt]; all_goals norm_num]
      _ = 8 + 4 * Real.sqrt 3 := by ring
  -- Calculate the final expression
  have h9 : (Real.sqrt 6 + Real.sqrt 2) * (Real.sqrt 3 - 2) * ((Real.sqrt 6 + Real.sqrt 2) / 2) = -2 := by
    have h10 : (Real.sqrt 6 + Real.sqrt 2) * (Real.sqrt 3 - 2) * ((Real.sqrt 6 + Real.sqrt 2) / 2) = ((Real.sqrt 6 + Real.sqrt 2) ^ 2 * (Real.sqrt 3 - 2)) / 2 := by
      ring
    rw [h10]
    rw [h8]
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  linarith [h9]