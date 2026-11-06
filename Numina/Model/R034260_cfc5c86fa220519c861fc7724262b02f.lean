import Mathlib

theorem inequalities_312251 (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    8 ≤ a^2 / (b - 1) + b^2 / (a - 1) := by
  have h1 : 0 < b - 1 := by linarith
  have h2 : 0 < a - 1 := by linarith
  have h3 : a^2 / (b - 1) + b^2 / (a - 1) - 8 ≥ 0 := by
    have h4 : a^2 / (b - 1) + b^2 / (a - 1) - 8 =
        (a^2 * (a - 1) + b^2 * (b - 1) - 8 * ( (a - 1) * (b - 1) )) / ( (a - 1) * (b - 1) ) := by
      field_simp
      <;> ring
    have h5 : a^2 * (a - 1) + b^2 * (b - 1) - 8 * ( (a - 1) * (b - 1) ) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - 2), sq_nonneg (b - 2), 
        sq_nonneg (a^2 - b^2), sq_nonneg (a - 1), sq_nonneg (b - 1),
        mul_pos (show (0 : ℝ) < a - 1 by linarith) (show (0 : ℝ) < b - 1 by linarith),
        mul_pos (show (0 : ℝ) < a - 1 by linarith) (show (0 : ℝ) < a - 1 by linarith),
        mul_pos (show (0 : ℝ) < b - 1 by linarith) (show (0 : ℝ) < b - 1 by linarith),
        sq_nonneg (a^2 - b^2), sq_nonneg (a - 1 - (b - 1))
      ]
    have h6 : (a^2 * (a - 1) + b^2 * (b - 1) - 8 * ( (a - 1) * (b - 1) )) / ( (a - 1) * (b - 1) ) ≥ 0 := by
      apply div_nonneg
      linarith [h5]
      all_goals positivity
    linarith [h4, h6]
  linarith [h3]