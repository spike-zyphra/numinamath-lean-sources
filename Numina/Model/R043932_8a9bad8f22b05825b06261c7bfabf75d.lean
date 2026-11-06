import Mathlib

theorem inequalities_92434 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 + b^2 / c^2) * (b^2 + c^2 / a^2) * (c^2 + a^2 / b^2) ≥ a * b * c * (a + 1 / a) * (b + 1 / b) * (c + 1 / c) := by

  have h1 : 0 < a * b * c := by
    positivity

  have h2 : a * b * c * (a + 1 / a) * (b + 1 / b) * (c + 1 / c) = (a^2 + 1) * (b^2 + 1) * (c^2 + 1) := by
    field_simp
    <;> ring

  rw [h2] at *
  have h3 : (a^2 + b^2 / c^2) * (b^2 + c^2 / a^2) * (c^2 + a^2 / b^2) - (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ 0 := by
    have pos1 : 0 < a^2 := by positivity
    have pos2 : 0 < b^2 := by positivity
    have pos3 : 0 < c^2 := by positivity
    have pos4 : 0 < a^2 * b^2 * c^2 := by positivity
    have h4 : (a^2 + b^2 / c^2) * (b^2 + c^2 / a^2) * (c^2 + a^2 / b^2) - (a^2 + 1) * (b^2 + 1) * (c^2 + 1) =
        ( (a^2 * c^2 + b^2) * (b^2 * a^2 + c^2) * (c^2 * b^2 + a^2) - (a^2 + 1) * (b^2 + 1) * (c^2 + 1) * (a^2 * b^2 * c^2) ) / (a^2 * b^2 * c^2) := by
      field_simp
      <;> ring
    rw [h4] at *
    have h5 : ( (a^2 * c^2 + b^2) * (b^2 * a^2 + c^2) * (c^2 * b^2 + a^2) - (a^2 + 1) * (b^2 + 1) * (c^2 + 1) * (a^2 * b^2 * c^2) ) / (a^2 * b^2 * c^2) ≥ 0 := by
      have pos1' : (0 : ℝ) < a^2 * b^2 * c^2 := by positivity
      have h6 : (a^2 * c^2 + b^2) * (b^2 * a^2 + c^2) * (c^2 * b^2 + a^2) - (a^2 + 1) * (b^2 + 1) * (c^2 + 1) * (a^2 * b^2 * c^2) ≥ 0 := by
        nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
            sq_nonneg (a^2 * b^2 - b^2 * c^2), sq_nonneg (b^2 * c^2 - c^2 * a^2), sq_nonneg (c^2 * a^2 - a^2 * b^2), 
            sq_nonneg (a^2 * c^2 - b^2 * a^2), sq_nonneg (b^2 * a^2 - c^2 * b^2), sq_nonneg (c^2 * b^2 - a^2 * c^2), 
            sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2), 
            sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
            mul_pos (show (0 : ℝ) < a^2 by positivity) (show (0 : ℝ) < b^2 by positivity), 
            mul_pos (show (0 : ℝ) < a^2 by positivity) (show (0 : ℝ) < c^2 by positivity), 
            mul_pos (show (0 : ℝ) < b^2 by positivity) (show (0 : ℝ) < c^2 by positivity)
          ]
      apply div_nonneg
      linarith
      all_goals positivity
    linarith
  all_goals linarith