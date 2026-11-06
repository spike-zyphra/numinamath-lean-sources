import Mathlib

theorem algebra_322351 : √(14 + 6 * √5) - √(14 - 6 * √5) = 2 * √5 := by
  have h1 : √(14 + 6 * √5) = √5 + 3 := by
    have h2 : (Real.sqrt 5 + 3) ^ 2 = 14 + 6 * Real.sqrt 5 := by 
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    have h3 : Real.sqrt 5 + 3 ≥ 0 := by positivity
    rw [← h2]
    field_simp [Real.sqrt_sq (show Real.sqrt 5 + 3 ≥ 0 by positivity)]
  have h4 : √(14 - 6 * √5) = 3 - √5 := by
    have h5 : (3 - Real.sqrt 5) ^ 2 = 14 - 6 * Real.sqrt 5 := by 
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), 
        Real.sqrt_le_sqrt (show (4 : ℝ) ≤ (5 : ℝ) by norm_num), 
        show Real.sqrt 4 = (2 : ℝ) by rw [Real.sqrt_eq_cases]; norm_num, 
        show Real.sqrt 5 < (3 : ℝ) by 
          have h7 : Real.sqrt 5 < (3 : ℝ) := by 
            rw [Real.sqrt_lt] <;> norm_num
          linarith
        ]
    have h6 : 3 - Real.sqrt 5 ≥ 0 := by
      have h7 : Real.sqrt 5 < (3 : ℝ) := by 
        rw [Real.sqrt_lt] <;> norm_num
      linarith
    rw [← h5]
    rw [Real.sqrt_sq (by linarith)]
    all_goals linarith
  rw [h1, h4]
  all_goals nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]