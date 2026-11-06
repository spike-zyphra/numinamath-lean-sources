import Mathlib

theorem inequalities_600735 (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    a ^ 2 / (b - 1) + b ^ 2 / (a - 1) ≥ 8 := by 
  have ha1 : 0 < b - 1 := by linarith
  have ha2 : 0 < a - 1 := by linarith
  have h1 : a ^ 2 / (b - 1) + b ^ 2 / (a - 1) - (8 : ℝ) ≥ 0 := by
    have h2 : 0 < (b - 1) * (a - 1) := by positivity
    have h3 : a ^ 2 / (b - 1) + b ^ 2 / (a - 1) - (8 : ℝ) =
        (a ^ 2 * (a - 1) + b ^ 2 * (b - 1) - 8 * (b - 1) * (a - 1)) / ((b - 1) * (a - 1)) := by
      field_simp
      <;> ring
    rw [h3] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (a - 1 - (b - 1)), sq_nonneg (a * (b - 1) - b * (a - 1)), sq_nonneg (a^2 - b^2), sq_nonneg (a - 1 - 1), sq_nonneg (b - 1 - 1), mul_pos (show (0 : ℝ) < a - 1 by linarith) (show (0 : ℝ) < b - 1 by linarith), mul_pos (show (0 : ℝ) < a - 1 by linarith) (show (0 : ℝ) < a - 1 by linarith), mul_pos (show (0 : ℝ) < b - 1 by linarith) (show (0 : ℝ) < b - 1 by linarith) ]
    all_goals
      positivity
  linarith