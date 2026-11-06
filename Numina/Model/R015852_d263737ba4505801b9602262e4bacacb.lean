import Mathlib

theorem algebra_306402 (k : ℝ) (h : ∃ x1 x2 : ℝ, x1^2 + 2 * k * x1 + 1 / 4 - k = 0 ∧ x2^2 + 2 * k * x2 + 1 / 4 - k = 0) :
    k ≥ (Real.sqrt 2 - 1) / 2 ∨ k ≤ -(Real.sqrt 2 + 1) / 2 := by
  rcases h with ⟨x1, x2, h1, h2⟩
  have h3 : 4 * k ^ 2 + 4 * k - 1 ≥ 0 := by
    nlinarith [sq_nonneg (x1 + k), sq_nonneg (x2 + k), sq_nonneg (x1 - x2)]
  by_contra h4
  push_neg at h4
  nlinarith [sq_nonneg (k + 1 / 2), Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ)), sq_nonneg (k - (Real.sqrt 2 - 1) / 2), sq_nonneg (k + (Real.sqrt 2 + 1) / 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]