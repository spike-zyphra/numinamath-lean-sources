import Mathlib

theorem algebra_51013 {a : ℝ} (ha : a > 1) (h : 20 * a / (a ^ 2 + 1) = Real.sqrt 2) :
    14 * a / (a ^ 2 - 1) = 1 := by

  have h1 : a ^ 2 + 1 > 0 := by
    nlinarith [h, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  have h2 : 20 * a = Real.sqrt 2 * (a ^ 2 + 1) := by
    field_simp [h1] at h ⊢
    linarith

  have h3 : (20 * a) ^ 2 = 2 * (a ^ 2 + 1) ^ 2 := by
    calc
      (20 * a) ^ 2 = (Real.sqrt 2 * (a ^ 2 + 1)) ^ 2 := by
        rw [h2]
      _ = (Real.sqrt 2) ^ 2 * (a ^ 2 + 1) ^ 2 := by ring
      _ = 2 * (a ^ 2 + 1) ^ 2 := by
        rw [Real.sq_sqrt]
        all_goals nlinarith

  have h4 : a ^ 4 - 198 * a ^ 2 + 1 = 0 := by
    nlinarith [h3]

  have h5 : a ^ 2 = 99 + 70 * Real.sqrt 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (a ^ 2 - (99 + 70 * Real.sqrt 2)), h4, Real.sqrt_nonneg 2]

  have h6 : a ^ 2 - 1 > 0 := by
    nlinarith [h5, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  have h7 : 14 * a / (a ^ 2 - 1) = 1 := by
    field_simp [h6]
    nlinarith [h, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h5, sq_nonneg (a ^ 2 - (99 + 70 * Real.sqrt 2)), Real.sqrt_nonneg 2]

  exact h7