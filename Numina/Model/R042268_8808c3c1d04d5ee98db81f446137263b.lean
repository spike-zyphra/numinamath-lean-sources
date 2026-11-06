import Mathlib

theorem algebra_313520 : 1 / (1 - 3 ^ ((1 : ℝ) / 4)) + 1 / (1 + 3 ^ ((1 : ℝ) / 4)) + 2 / (1 + Real.sqrt 3) = -2 := by

  have h2 : ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = (3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith

  have h3 : ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt 3 := by
    have h31 : ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = (3 : ℝ) ^ ((1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h32 : (3 : ℝ) ^ ((1 / 2 : ℝ)) = Real.sqrt 3 := by
      rw [Real.sqrt_eq_rpow]
    rw [h31, h32]

  have h4 : (1 - (3 : ℝ) ^ ((1 : ℝ) / 4)) * (1 + (3 : ℝ) ^ ((1 : ℝ) / 4)) = 1 - ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by
    nlinarith

  have h5 : 1 - ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = 1 - Real.sqrt 3 := by
    rw [h3]

  have h6 : 1 - Real.sqrt 3 ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

  have eq1 : 1 / (1 - (3 : ℝ) ^ ((1 : ℝ) / 4)) + 1 / (1 + (3 : ℝ) ^ ((1 : ℝ) / 4)) = 2 / (1 - Real.sqrt 3) := by
    have h7 : (1 - (3 : ℝ) ^ ((1 : ℝ) / 4)) * (1 + (3 : ℝ) ^ ((1 : ℝ) / 4)) = 1 - Real.sqrt 3 := by
      rw [h4, h5]
    have h9 : (1 - (3 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 := by
      by_contra h
      have h11 : (3 : ℝ) ^ ((1 : ℝ) / 4) = 1 := by linarith
      have h12 : ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = (1 : ℝ) := by
        rw [h11]
        norm_num
      have h13 : ((3 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = (3 : ℝ) := h2
      linarith
    have h10 : (1 + (3 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 := by
      have h41 : (3 : ℝ) ^ ((1 : ℝ) / 4) > 0 := by positivity
      linarith
    field_simp [(show (1 - (3 : ℝ) ^ ((1 : ℝ) / 4) ) ≠ 0 by assumption), (show (1 + (3 : ℝ) ^ ((1 : ℝ) / 4) ) ≠ 0 by assumption)]
    <;> nlinarith [h7, Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg ((3 : ℝ) ^ ((1 : ℝ) / 4) - 1), sq_nonneg ((3 : ℝ) ^ ((1 : ℝ) / 4) + 1), h2, h3]

  have eq2 : (2 / (1 + Real.sqrt 3) ) = Real.sqrt 3 - 1 := by
    have h51 : 1 + Real.sqrt 3 ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    field_simp [h51]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

  rw [eq1]
  rw [eq2]

  have eq3 : (2 / (1 - Real.sqrt 3) ) = - (1 + Real.sqrt 3) := by
    have h41 : 1 - Real.sqrt 3 ≠ 0 := h6
    field_simp [h41]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

  rw [eq3]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]