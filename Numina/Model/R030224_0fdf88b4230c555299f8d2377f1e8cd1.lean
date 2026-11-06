import Mathlib

theorem algebra_238094 {t : ℝ} (ht : t = 1 / (1 - 2 ^ ((1 : ℝ) / 4))) :
    t = -(1 + 2 ^ ((1 : ℝ) / 4)) * (1 + 2 ^ ((1 : ℝ) / 2)) := by 
  rw [ht]
  have h1 : (1 - (2 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 := by 
    have h2 : (2 : ℝ) ^ ((1 : ℝ) / 4) > 1 := by
      apply Real.one_lt_rpow
      all_goals linarith
    intro h
    have h3 : (2 : ℝ) ^ ((1 : ℝ) / 4) = 1 := by linarith
    linarith [h2, h3]
  field_simp [h1]
  have h2 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = 2 := by 
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith
  have h3 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = (2 : ℝ) ^ ((1 : ℝ) / 2) := by 
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith
  have h4 : ((2: ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = (2 : ℝ) ^ ((1 : ℝ) / 2) := h3
  nlinarith [sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 4) - 1), sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 4) + 1), 
          sq_nonneg ((2 : ℝ) ^ ((1 : ℝ) / 4) ^ 2 - (2 : ℝ) ^ ((1 : ℝ) / 2)), 
          h2, Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (1 / 4 : ℝ), 
          Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (1 / 2 : ℝ), 
          Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (1 / 4 : ℝ), 
          Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (1 / 2 : ℝ)]