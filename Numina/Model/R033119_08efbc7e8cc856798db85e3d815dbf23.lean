import Mathlib

open Real

theorem algebra_6006 : (3 : ℝ) ^ (logb (2 / 3) 3) / 2 ^ (logb (2 / 3) 2) = 1 / 6 := by
  have h2 : logb (2 / 3) 3 = (log 3) / (log 2 - log 3) := by
    have h3 : logb (2 / 3) 3 = log 3 / log (2 / 3) := by
      field_simp [logb]
    have h4 : log (2 / 3) = log 2 - log 3 := by
      rw [log_div (by norm_num) (by norm_num)]
    rw [h3, h4]
  have h3 : logb (2 / 3) 2 = (log 2) / (log 2 - log 3) := by
    have h4 : logb (2 / 3) 2 = log 2 / log (2 / 3) := by
      field_simp [logb]
    have h5 : log (2 / 3) = log 2 - log 3 := by
      rw [log_div (by norm_num) (by norm_num)]
    rw [h4, h5]
  rw [h2, h3]
  have h4 : log 2 - log 3 < 0 := by
    have h5 : log 2 < log 3 := by
      apply Real.log_lt_log
      all_goals norm_num
    linarith
  have h8 : (3 : ℝ) ^ ((log 3) / (log 2 - log 3)) / (2 : ℝ) ^ ((log 2) / (log 2 - log 3)) = (1 / 6 : ℝ) := by
    have h9 : (3 : ℝ) ^ ((log 3) / (log 2 - log 3)) / (2 : ℝ) ^ ((log 2) / (log 2 - log 3)) = Real.exp ((log 3 / (log 2 - log 3)) * log 3 - (log 2 / (log 2 - log 3)) * log 2) := by
      have h11 : (3 : ℝ) ^ ((log 3) / (log 2 - log 3)) = Real.exp ((log 3 / (log 2 - log 3)) * log 3) := by
        rw [Real.rpow_def_of_pos (show (3 : ℝ) > 0 by norm_num)]
        <;> ring
      have h12 : (2 : ℝ) ^ ((log 2) / (log 2 - log 3)) = Real.exp ((log 2 / (log 2 - log 3)) * log 2) := by 
        rw [Real.rpow_def_of_pos (show (2 : ℝ) > 0 by norm_num)]
        <;> ring
      rw [h11, h12]
      have h13 : Real.exp ((log 3 / (log 2 - log 3)) * log 3) / Real.exp ((log 2 / (log 2 - log 3)) * log 2) = Real.exp ((log 3 / (log 2 - log 3)) * log 3 - (log 2 / (log 2 - log 3)) * log 2) := by 
        rw [Real.exp_sub]
      rw [h13]
    rw [h9]
    have h10 : (log 3 / (log 2 - log 3)) * log 3 - (log 2 / (log 2 - log 3)) * log 2 = log (1 / 6) := by
      have h11 : log (1 / 6) = - log 6 := by simp [log_div, log_one]
      have h12 : log 6 = log 2 + log 3 := by 
        rw [show (6 : ℝ) = 2 * 3 by norm_num]
        rw [log_mul (by norm_num) (by norm_num)]
      rw [h11, h12]
      field_simp [(show log 2 - log 3 ≠ 0 by
        have h13 : log 2 < log 3 := by
          apply Real.log_lt_log
          all_goals norm_num
        have h14 : log 2 - log 3 < 0 := by linarith
        have h15 : log 2 - log 3 ≠ 0 := by linarith
        exact h15
      )
      ]
      <;> ring
    rw [h10]
    have h11 : Real.exp (log (1 / 6)) = (1 / 6 : ℝ) := by 
      rw [Real.exp_log]
      all_goals norm_num
    linarith
  linarith