import Mathlib

theorem inequalities_316954 (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    8 ≤ a^2 / (b - 1) + b^2 / (a - 1) := by
  have h1 : 0 < b - 1 := by linarith
  have h2 : 0 < a - 1 := by linarith
  have h3 : a^2 / (b - 1) + b^2 / (a - 1) - 8 ≥ 0 := by
    have h4 : a^2 / (b - 1) + b^2 / (a - 1) - 8 =
        (a^2 * (a - 1) + b^2 * (b - 1) - 8 * (b - 1) * (a - 1)) / ((b - 1) * (a - 1)) := by
      field_simp [h1, h2]
      ring
    have h5 : a^2 * (a - 1) + b^2 * (b - 1) - 8 * (b - 1) * (a - 1) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (a + b - 2),
                 sq_nonneg (a + b - 4), mul_pos h1 h2, mul_pos h1 (show (0:ℝ) < a - 1 by linarith), mul_pos h2 (show (0:ℝ) < b - 1 by linarith)]
    have h6 : (b - 1) * (a - 1) > 0 := mul_pos h1 h2
    rw [h4]
    apply div_nonneg
    linarith [h5]
    nlinarith [h6]
  linarith [h3]