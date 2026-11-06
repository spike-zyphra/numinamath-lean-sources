import Mathlib

theorem inequalities_245436 {x y : ℝ} (hx : x > y) (hy : 0 ≤ y) :
    x + 4 / ((x - y) * (y + 1)^2) ≥ 3 := by

  have h1 : 0 < x - y := by linarith
  have h2 : 0 < (y + 1) ^ 2 := by
    have h3 : 0 < y + 1 := by linarith
    positivity
  have h3 : 0 < (x - y) * (y + 1) ^ 2 := mul_pos h1 h2
  have h4 : x + 4 / ((x - y) * (y + 1)^2) - 3 ≥ 0 := by
    have h5 : (x + 4 / ((x - y) * (y + 1) ^ 2) - 3) = (x * (x - y) * (y + 1) ^ 2 + 4 - 3 * (x - y) * (y + 1) ^ 2) / ((x - y) * (y + 1) ^ 2) := by
      field_simp
      all_goals
        ring
    rw [h5] 
    have h6 : x * (x - y) * (y + 1) ^ 2 + 4 - 3 * (x - y) * (y + 1) ^ 2 ≥ 0 := by
      nlinarith [sq_nonneg ((x - y) - 1), sq_nonneg ((y + 1) ^ 2 - 1), sq_nonneg (y - 1), sq_nonneg (x - 2), sq_nonneg ((y + 1) * (x - y) - 1), sq_nonneg (x - y - 1), sq_nonneg (y - 1), sq_nonneg (x - y - 1), mul_nonneg (show 0 ≤ (y : ℝ) by linarith) (show 0 ≤ (y + 1 : ℝ) by linarith), sq_nonneg (y * (x - y) - 1), sq_nonneg ((x - y) * (y + 1) ^ 2 - 2), sq_nonneg (y + 1 - 1), mul_nonneg (show 0 ≤ (y : ℝ) by linarith) (show 0 ≤ (x - y : ℝ) by linarith), sq_nonneg ((x - 2) * (y + 1)), sq_nonneg (y * (y + 1)), sq_nonneg ((x - 2) * (y - 1))]
    have h7 : (x * (x - y) * (y + 1) ^ 2 + 4 - 3 * (x - y) * (y + 1) ^ 2) / ((x - y) * (y + 1) ^ 2) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith