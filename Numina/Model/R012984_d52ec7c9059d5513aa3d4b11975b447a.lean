import Mathlib

theorem algebra_317971 {x : ℝ} (hx : x = (3 - Real.sqrt 5) / 2) :
    x^3 - 3 * x^2 + 3 * x + 6 / (x^2 + 1) = 6 := by
  rw [hx]
  have h1 : ((3 - Real.sqrt 5) / 2 : ℝ) ^ 2 = (7 - 3 * Real.sqrt 5) / 2 := by
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
  have h2 : ((3 - Real.sqrt 5) / 2 : ℝ) ^ 2 + 1 = (9 - 3 * Real.sqrt 5) / 2 := by
    rw [h1]
    ring
  have h3 : 6 / (((3 - Real.sqrt 5) / 2 : ℝ) ^ 2 + 1) = 3 + Real.sqrt 5 := by 
    rw [h2]
    have h4 : (9 - 3 * Real.sqrt 5 : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    field_simp [h4]
    <;> nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
  have h4 : ((3 - Real.sqrt 5) / 2 : ℝ) ^ 3 - 3 * ((3 - Real.sqrt 5) / 2 : ℝ) ^ 2 + 3 * ((3 - Real.sqrt 5) / 2 : ℝ) = 3 - Real.sqrt 5 := by
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
  rw [h3]
  linarith [h4]