import Mathlib

theorem inequalities_303296 (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    a ^ 2 / (b - 1) + b ^ 2 / (a - 1) ≥ 8 := by
  have h1 : 0 < b - 1 := by linarith
  have h2 : 0 < a - 1 := by linarith
  have h3 : a ^ 2 / (b - 1) + b ^ 2 / (a - 1) - 8 ≥ 0 := by
    have h4 : (a ^ 2 / (b - 1) + b ^ 2 / (a - 1) - 8) = (a^2 * (a - 1) + b^2 * (b - 1) - 8 * (b - 1) * (a - 1)) / ((b - 1) * (a - 1)) := by
      field_simp
      ring
    rw [h4]
    apply div_nonneg
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (a - b), sq_nonneg (a * b - 2), mul_pos (show 0 < b - 1 by linarith) (show 0 < a - 1 by linarith), sq_nonneg (a^2 - b^2), sq_nonneg (a*b - 4)]
    positivity
  linarith