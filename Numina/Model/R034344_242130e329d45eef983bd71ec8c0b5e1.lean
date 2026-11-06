import Mathlib

theorem algebra_98550 {t : ℝ} (ht : t = 1 / (1 - (2 : ℝ) ^ ((1 : ℝ) / 4))) :
    t = -(1 + (2 : ℝ) ^ ((1 : ℝ) / 4)) * (1 + (2 : ℝ) ^ ((1 : ℝ) / 2)) := by
  rw [ht]
  have h1 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = (2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals norm_num
  have h2 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = (2 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals norm_num
  have h3 : (1 - (2 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 := by
    have h4 : (2 : ℝ) ^ ((1 : ℝ) / 4) > 0 := by positivity
    by_contra h
    have h5 : (2 : ℝ) ^ ((1 : ℝ) / 4) = 1 := by linarith
    have h6 : (2 : ℝ) ^ ((1 : ℝ) / 4) > 1 := by
      have h7 : (2 : ℝ) ^ ((1 : ℝ) / 4) > (1 : ℝ) := by
        have h8 : (2 : ℝ) > (1 : ℝ) := by norm_num
        have h9 : (2 : ℝ) ^ ((1 : ℝ) / 4) > (1 : ℝ) ^ ((1 : ℝ) / 4) := by
          apply Real.rpow_lt_rpow
          all_goals linarith
        have h10 : (1 : ℝ) ^ ((1 : ℝ) / 4) = 1 := by
          simp
        linarith [h10, h9]
      linarith
    linarith [h5, h6]
  field_simp [h3, h2]
  nlinarith [h1, h2, sq_pos_of_pos (show 0 < (2 : ℝ) ^ ((1 : ℝ) / 4) by positivity), sq_nonneg ( (2 : ℝ) ^ ((1 : ℝ) / 4) - 1 ), sq_nonneg ( (2 : ℝ) ^ ((1 : ℝ) / 4) ^ 2 - 1 ), Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (1 / 4), Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (1 / 2) ]