import Mathlib
open Real

theorem algebra_889 : 1 / (3 + 2 * √2) + 1 / (2 * √2 + √7) + 1 / (√7 + √6) + 1 / (√6 + √5) + 1 / (√5 + 2) + 1 / (2 + √3) = 3 - √3 := by

  have h1 : 1 / (3 + 2 * √2) = 3 - 2 * √2 := by
    have h1 : (3 + 2 * √2) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (2:ℝ) > 0 by norm_num), Real.sq_sqrt (show (2:ℝ) ≥ 0 by norm_num)]
    field_simp [h1]
    ring_nf
    nlinarith [Real.sqrt_pos.mpr (show (2:ℝ) > 0 by norm_num), Real.sq_sqrt (show (2:ℝ) ≥ 0 by norm_num)]

  have h2 : 1 / (2 * √2 + √7) = 2 * √2 - √7 := by
    have h2 : (2 * √2 + √7) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (2:ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (7:ℝ) > 0 by norm_num), Real.sq_sqrt (show (2:ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (7:ℝ) ≥ 0 by norm_num)]
    field_simp [h2]
    ring_nf
    nlinarith [Real.sqrt_pos.mpr (show (2:ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (7:ℝ) > 0 by norm_num), Real.sq_sqrt (show (2:ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (7:ℝ) ≥ 0 by norm_num)]

  have h3 : 1 / (√7 + √6) = √7 - √6 := by
    have h3 : (√7 + √6) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (7:ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (6:ℝ) > 0 by norm_num), Real.sq_sqrt (show (7:ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (6:ℝ) ≥ 0 by norm_num)]
    field_simp [h3]
    ring_nf
    nlinarith [Real.sqrt_pos.mpr (show (7:ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (6:ℝ) > 0 by norm_num), Real.sq_sqrt (show (7:ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (6:ℝ) ≥ 0 by norm_num)]

  have h4 : 1 / (√6 + √5) = √6 - √5 := by
    have h4 : (√6 + √5) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (6:ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (5:ℝ) > 0 by norm_num), Real.sq_sqrt (show (6:ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (5:ℝ) ≥ 0 by norm_num)]
    field_simp [h4]
    ring_nf
    nlinarith [Real.sqrt_pos.mpr (show (6:ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (5:ℝ) > 0 by norm_num), Real.sq_sqrt (show (6:ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (5:ℝ) ≥ 0 by norm_num)]

  have h5 : 1 / (√5 + 2) = √5 - 2 := by
    have h5 : (√5 + 2) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (5:ℝ) > 0 by norm_num), Real.sq_sqrt (show (5:ℝ) ≥ 0 by norm_num)]
    field_simp [h5]
    ring_nf
    nlinarith [Real.sqrt_pos.mpr (show (5:ℝ) > 0 by norm_num), Real.sq_sqrt (show (5:ℝ) ≥ 0 by norm_num)]

  have h6 : 1 / (2 + √3) = 2 - √3 := by
    have h6 : (2 + √3) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (3:ℝ) > 0 by norm_num), Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num)]
    field_simp [h6]
    ring_nf
    nlinarith [Real.sqrt_pos.mpr (show (3:ℝ) > 0 by norm_num), Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num)]

  rw [h1, h2, h3, h4, h5, h6]
  ring