import Mathlib

open Real

theorem algebra_315936 {x y : ℝ} (hx : x = (2 + sqrt 3) / (sqrt 2 + sqrt (2 + sqrt 3))) (hy : y = (2 - sqrt 3) / (sqrt 2 - sqrt (2 - sqrt 3))) :
    x + y = sqrt 2 := by

  have h1 : sqrt (2 + sqrt 3) = (sqrt 3 + 1) / sqrt 2 := by
    have h2 : ((sqrt 3 + 1) / sqrt 2) ^ 2 = (2 + sqrt 3) := by
      have h3 : sqrt 2 > 0 := by positivity
      field_simp
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt 3 - 1)]
    have h3 : ((sqrt 3 + 1) / sqrt 2) ≥ 0 := by
      apply div_nonneg
      · -- sqrt 3 + 1 ≥ 0
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2]
      · -- sqrt 2 ≥ 0
        positivity
    have h4 : sqrt ((2 + sqrt 3)) = (sqrt 3 + 1) / sqrt 2 := by
      rw [←h2]
      field_simp
    linarith

  have h2 : sqrt (2 - sqrt 3) = (sqrt 3 - 1) / sqrt 2 := by
    have h3 : ((sqrt 3 - 1) / sqrt 2) ^ 2 = (2 - sqrt 3) := by
      have h4 : sqrt 2 > 0 := by positivity
      field_simp
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt 3 - 1)]
    have h4 : ((sqrt 3 - 1) / sqrt 2) ≥ 0 := by
      apply div_nonneg
      · -- Show sqrt 3 - 1 ≥ 0
        nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), show sqrt 3 ≥ Real.sqrt 1 by apply Real.sqrt_le_sqrt (by norm_num), show sqrt 1 = (1 : ℝ) by rw [Real.sqrt_one]]
      · -- Show sqrt 2 ≥ 0
        positivity
    have h5 : sqrt ((2 - sqrt 3)) = (sqrt 3 - 1) / sqrt 2 := by
      rw [←h3]
      field_simp
    linarith

  rw [hx, hy, h1, h2]

  have h3 : sqrt 2 > 0 := by positivity
  have h4 : sqrt 3 > 0 := by positivity
  have h5 : sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
  have h6 : sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)

  have eq1 : (2 + sqrt 3) / (sqrt 2 + (sqrt 3 + 1) / sqrt 2) = (2 + sqrt 3) * sqrt 2 / (3 + sqrt 3) := by
    have h7 : sqrt 2 + (sqrt 3 + 1) / sqrt 2 = (3 + sqrt 3) / sqrt 2 := by
      field_simp
      nlinarith [h6, h5, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    rw [h7]
    field_simp
    all_goals nlinarith

  have eq2 : (2 - sqrt 3) / (sqrt 2 - (sqrt 3 - 1) / sqrt 2) = (2 - sqrt 3) * sqrt 2 / (3 - sqrt 3) := by
    have h8 : sqrt 2 - (sqrt 3 - 1) / sqrt 2 = (3 - sqrt 3) / sqrt 2 := by
      field_simp
      nlinarith [h6, h5, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    rw [h8]
    field_simp
    all_goals nlinarith

  rw [eq1, eq2]

  have eq3 : (2 + sqrt 3) * sqrt 2 / (3 + sqrt 3) + (2 - sqrt 3) * sqrt 2 / (3 - sqrt 3) = sqrt 2 := by
    have h7 : (3 + sqrt 3) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h8 : (3 - sqrt 3) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    field_simp [h7, h8]
    nlinarith [sq_pos_of_pos h3, sq_pos_of_pos (show sqrt 3 > 0 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt 2 ^ 2 - 2), sq_nonneg (sqrt 3 ^ 2 - 3)]
  nlinarith