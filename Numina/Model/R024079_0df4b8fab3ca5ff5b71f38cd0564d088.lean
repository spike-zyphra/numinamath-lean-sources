import Mathlib

theorem algebra_310032 : (1 / (4 + Real.sqrt (59 + 30 * Real.sqrt 2)) + 1 / (3 - Real.sqrt (66 - 40 * Real.sqrt 2))) = -14 := by
  have h1 : Real.sqrt (59 + 30 * Real.sqrt 2) = 3 + 5 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
  have h2 : Real.sqrt (66 - 40 * Real.sqrt 2) = 5 * Real.sqrt 2 - 4 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]
  rw [h1, h2]
  have h3 : (4 : ℝ) + (3 + 5 * Real.sqrt 2) = 7 + 5 * Real.sqrt 2 := by
    nlinarith
  have h4 : (3 : ℝ) - (5 * Real.sqrt 2 - 4) = 7 - 5 * Real.sqrt 2 := by
    nlinarith
  rw [h3, h4]
  have h5 : (7 + 5 * Real.sqrt 2) ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
  have h6 : (7 - 5 * Real.sqrt 2) ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
  field_simp [h5, h6]
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]