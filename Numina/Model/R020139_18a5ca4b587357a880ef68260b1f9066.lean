import Mathlib

open Real

theorem algebra_187936 : sqrt (6 + sqrt 32) - sqrt (6 - sqrt 32) = 2 * sqrt 2 := by
  have h1 : sqrt 32 = 4 * sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num

  have h2 : sqrt (6 + sqrt 32) = 2 + Real.sqrt 2 := by
    rw [h1]
    have h3 : sqrt (6 + (4 * Real.sqrt 2 : ℝ)) = (2 + Real.sqrt 2 : ℝ) := by
      have h4 : (2 + Real.sqrt 2 : ℝ) ^ 2 = (6 + (4 * Real.sqrt 2 : ℝ)) := by
        nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h5 : (2 + Real.sqrt 2 : ℝ) ≥ 0 := by
        nlinarith [Real.sqrt_nonneg 2]
      rw [←h4]
      field_simp [Real.sqrt_sq (show 0 ≤ (2 + Real.sqrt 2 : ℝ) by nlinarith), Real.sqrt_nonneg (6 + 4 * Real.sqrt 2)]
      all_goals nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    exact h3

  have h3 : sqrt (6 - sqrt 32) = (2 - Real.sqrt 2 : ℝ) := by
    rw [h1]
    have h4 : sqrt (6 - (4 * Real.sqrt 2 : ℝ)) = (2 - Real.sqrt 2 : ℝ) := by
      have h5 : (2 - Real.sqrt 2 : ℝ) ^ 2 = (6 - (4 * Real.sqrt 2 : ℝ) : ℝ) := by
        nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h6 : (2 - Real.sqrt 2 : ℝ) ≥ 0 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      rw [←h5]
      field_simp [Real.sqrt_sq (show 0 ≤ (2 - Real.sqrt 2 : ℝ) by nlinarith), Real.sqrt_nonneg (6 - (4 * Real.sqrt 2 : ℝ))]
      all_goals nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    exact h4

  rw [h2, h3]
  ring_nf
  all_goals norm_num