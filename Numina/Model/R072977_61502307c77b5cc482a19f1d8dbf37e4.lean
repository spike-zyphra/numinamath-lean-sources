import Mathlib

theorem algebra_187738 : 1 / ((16 : ℝ) ^ ((1 : ℝ) / 5) + (8 : ℝ) ^ ((1 : ℝ) / 5) +
    (4 : ℝ) ^ ((1 : ℝ) / 5) + (2 : ℝ) ^ ((1 : ℝ) / 5) + 1) = (2 ^ ((1 : ℝ) / 5) - 1) := by
  have h1 : (16 : ℝ) ^ ((1 : ℝ) / 5) = (2 : ℝ) ^ ((4 : ℝ) / 5) := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  have h2 : (8 : ℝ) ^ ((1 : ℝ) / 5) = (2 : ℝ) ^ ((3 : ℝ) / 5) := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  have h3 : (4 : ℝ) ^ ((1 : ℝ) / 5) = (2 : ℝ) ^ ((2 : ℝ) / 5) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  have h4 : (2 : ℝ) ^ ((1 : ℝ) / 5) = (2 : ℝ) ^ ((1 : ℝ) / 5) := by
    rfl
  have eq1 : (16 : ℝ) ^ ((1 : ℝ) / 5) + (8 : ℝ) ^ ((1 : ℝ) / 5) + (4 : ℝ) ^ ((1 : ℝ) / 5) + (2 : ℝ) ^ ((1 : ℝ) / 5) + 1 = (2 : ℝ) ^ ((4 : ℝ) / 5) + (2 : ℝ) ^ ((3 : ℝ) / 5) + (2 : ℝ) ^ ((2 : ℝ) / 5) + (2 : ℝ) ^ ((1 : ℝ) / 5) + 1 := by
    rw [h1, h2, h3, h4]
  have h5 : (2 : ℝ) ^ ((4 : ℝ) / 5) = ((2 : ℝ) ^ (1 / 5 : ℝ)) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    field_simp
    all_goals norm_num
  have h6 : (2 : ℝ) ^ ((3 : ℝ) / 5) = ((2 : ℝ) ^ (1 / 5 : ℝ)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    field_simp
    all_goals norm_num
  have h7 : (2 : ℝ) ^ ((2 : ℝ) / 5) = ((2 : ℝ) ^ (1 / 5 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    field_simp
    all_goals norm_num
  rw [eq1, h5, h6, h7, h4]
  -- The right side.
  have ht5 : ((2 : ℝ) ^ (1 / 5 : ℝ)) ^ 5 = 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul]
    field_simp
    all_goals norm_num

  field_simp [(show ((2 : ℝ) ^ (1 / 5 : ℝ) - 1) ≠ 0 by
    have h9 : (2 : ℝ) ^ (1 / 5 : ℝ) > 1 := by
      have h1 : (2 : ℝ) ^ (1 / 5 : ℝ) > (1 : ℝ) := by
        apply Real.one_lt_rpow
        all_goals norm_num
      linarith
    have h10 : (2 : ℝ) ^ (1 / 5 : ℝ) - 1 > 0 := by linarith
    linarith
  )]
  <;> nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (4 / 5),
  Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (3 / 5),
  Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (2 / 5),
  Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (1 / 5),
  Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (1 / 5),
  sq_nonneg ((2 : ℝ) ^ (1 / 5 : ℝ) - 1),
  sq_nonneg (((2 : ℝ) ^ (1 / 5 : ℝ)) ^ 2 - 1),
  Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (4 / 5),
  Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (3 / 5),
  Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (2 / 5),
  Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (1 / 5),
  ht5]