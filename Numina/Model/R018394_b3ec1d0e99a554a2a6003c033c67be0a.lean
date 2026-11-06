import Mathlib

open Real

theorem algebra_108763 {a b : ℝ} (ha : a > 1) (hb : b > 1) (hab : a * b = 1000) :
    sqrt (1 + logb 10 a) + sqrt (1 + logb 10 b) ≤ sqrt 10 := by

  have h1 : logb 10 a + logb 10 b = 3 := by
    have h2 : logb 10 a + logb 10 b = logb 10 (a * b) := by 
      rw [logb_mul (by linarith) (by linarith)]
    rw [h2]
    rw [show a * b = 1000 by linarith [hab]]
    have h3 : logb 10 (1000 : ℝ) = 3 := by
      rw [logb_eq_iff_rpow_eq] <;> (norm_num)
    linarith [h3]

  have h1' : 1 + logb 10 a + (1 + logb 10 b) = 5 := by
    have h2 : logb 10 a + logb 10 b = 3 := h1
    linarith

  have h2 : (sqrt (1 + logb 10 a) + sqrt (1 + logb 10 b)) ^ 2 ≤ 10 := by
    nlinarith [sq_nonneg (sqrt (1 + logb 10 a) - sqrt (1 + logb 10 b)), 
              Real.sqrt_nonneg (1 + logb 10 a), 
              Real.sqrt_nonneg (1 + logb 10 b), 
              sq_nonneg (sqrt (1 + logb 10 a) ^ 2 - sqrt (1 + logb 10 b) ^ 2),
              Real.sq_sqrt (show (0 : ℝ) ≤ 1 + logb 10 a by 
                have h3 : logb 10 a > 0 := by 
                  apply logb_pos 
                  all_goals linarith 
                linarith 
              ), 
              Real.sq_sqrt (show (0 : ℝ) ≤ 1 + logb 10 b by 
                have h4 : logb 10 b > 0 := by 
                  apply logb_pos 
                  all_goals linarith 
                linarith 
              ), 
              h1', 
              sq_nonneg (sqrt (1 + logb 10 a) + sqrt (1 + logb 10 b)), 
              Real.sqrt_nonneg 10, 
              Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)
            ]

  have h3 : sqrt (1 + logb 10 a) + sqrt (1 + logb 10 b) ≤ sqrt 10 := by
    have h4 : (sqrt (1 + logb 10 a) + sqrt (1 + logb 10 b)) ^ 2 ≤ (10 : ℝ) := h2
    have h5 : sqrt ((sqrt (1 + logb 10 a) + sqrt (1 + logb 10 b)) ^ 2) ≤ sqrt (10 : ℝ) := by 
      apply Real.sqrt_le_sqrt 
      linarith 
    have h6 : sqrt ((sqrt (1 + logb 10 a) + sqrt (1 + logb 10 b)) ^ 2) = (sqrt (1 + logb 10 a) + sqrt (1 + logb 10 b)) := by 
      rw [Real.sqrt_sq] 
      positivity 
    linarith [h5, h6] 
  exact h3