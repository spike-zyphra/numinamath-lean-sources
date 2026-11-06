import Mathlib

theorem algebra_6051 {x : ℝ} (hx : x = 38 - 10 * Real.sqrt 13) :
    Real.sqrt x = 5 - Real.sqrt 13 := by
  rw [hx]
  have h1 : (5 - Real.sqrt 13) ^ 2 = 38 - 10 * Real.sqrt 13 := by
    nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
  have h2 : (5 - Real.sqrt 13 : ℝ) ≥ 0 := by
    nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), Real.sqrt_nonneg 13]
  rw [← h1]
  field_simp [Real.sqrt_sq h2]
  all_goals
    nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]