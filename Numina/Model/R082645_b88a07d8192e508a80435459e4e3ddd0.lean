import Mathlib

theorem inequalities_7918 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    1 / (2 + a + b) + a / (2 * a + b + 1) + b / (2 * b + a + 1) ≤ 3 / 4 := by 
  have h1 : 0 < 2 + a + b := by linarith
  have h2 : 0 < 2 * a + b + 1 := by nlinarith
  have h3 : 0 < 2 * b + a + 1 := by nlinarith

  have h4 : 1 / (2 + a + b) + a / (2 * a + b + 1) + b / (2 * b + a + 1) - 3 / 4 ≤ 0 := by
    have pos1 : 0 < (2 + a + b) * (2 * a + b + 1) * (2 * b + a + 1) := mul_pos (mul_pos h1 h2) h3

    have h5 : (1 / (2 + a + b) + a / (2 * a + b + 1) + b / (2 * b + a + 1) - 3 / 4) ≤ 0 := by
      have h6 : (1 / (2 + a + b) + a / (2 * a + b + 1) + b / (2 * b + a + 1) - 3 / 4) =
          ((2 * a + b + 1) * (2 * b + a + 1) + a * (2 + a + b) * (2 * b + a + 1) + b * (2 + a + b) * (2 * a + b + 1) - 3 / 4 * (2 + a + b) * (2 * a + b + 1) * (2 * b + a + 1)) / ((2 + a + b) * (2 * a + b + 1) * (2 * b + a + 1)) := by
        field_simp [h1, h2, h3]
        ring
      rw [h6]
      apply div_nonpos_of_nonpos_of_nonneg
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), mul_pos ha hb, 
          sq_nonneg (a + b - 1)]
      positivity

    linarith
  linarith [h4]