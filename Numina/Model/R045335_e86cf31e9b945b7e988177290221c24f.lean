import Mathlib

theorem algebra_290099 : √(3 * (7 + 4 * √3)) = 2 * √3 + 3 := by
  have h1 : (2 * √3 + 3) ^ 2 = 3 * (7 + 4 * √3) := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h2 : 2 * √3 + 3 ≥ 0 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  rw [← h1]
  field_simp [h2]