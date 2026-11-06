import Mathlib

open Real

theorem inequalities_141937 : (1 + sqrt 5) / 2 < (18 : ℝ) ^ ((1 : ℝ) / 6) := by
  have h1 : ((1 + sqrt 5) / 2 : ℝ)^6 < (18 : ℝ) := by
    nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (sqrt 5 ^ 2 - 4), sq_nonneg (sqrt 5 - 2), Real.sqrt_nonneg 5, mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 5)]
  have h2 : ((1 + sqrt 5) / 2 : ℝ) < (18 : ℝ) ^ ((1 : ℝ) / 6) := by
    have h3 : ((18 : ℝ) ^ ((1 : ℝ) / 6)) ^ 6 = (18 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals norm_num
    have h4 : ((1 + sqrt 5) / 2 : ℝ) > 0 := by
      have h8 : sqrt 5 > 0 := by positivity
      linarith
    have h5 : ((18 : ℝ) ^ ((1 : ℝ) / 6) : ℝ) > 0 := by positivity
    by_contra h
    push_neg at h
    have h6 : ((1 + sqrt 5) / 2 : ℝ) ^ 6 ≥ ((18 : ℝ) ^ ((1 : ℝ) / 6)) ^ 6 := by
      have h7 : ((1 + sqrt 5) / 2 : ℝ) ≥ ((18 : ℝ) ^ ((1 : ℝ) / 6)) := h
      have h8 : ((1 + sqrt 5) / 2 : ℝ) ^ 6 ≥ ((18 : ℝ) ^ ((1 : ℝ) / 6)) ^ 6 := by
        apply pow_le_pow_left
        all_goals
          linarith [h4, h5, h7]
      exact h8
    linarith [h1, h3, h6]
  exact h2