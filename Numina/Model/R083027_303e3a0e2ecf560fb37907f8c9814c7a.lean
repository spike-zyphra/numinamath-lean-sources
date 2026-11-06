import Mathlib

theorem inequalities_225675 (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    a^2 / (b - 1) + b^2 / (a - 1) ≥ 8 := by 
  have h1 : 0 < b - 1 := by linarith
  have h2 : 0 < a - 1 := by linarith

  have h3 : a^2 / (b - 1) + b^2 / (a - 1) - 8 ≥ 0 := by
    have h4 : a^2 / (b - 1) + b^2 / (a - 1) - 8 =
        (a^2 * (a - 1) + b^2 * (b - 1) - 8 * (b - 1) * (a - 1)) / ((b - 1) * (a - 1)) := by 
      field_simp [h1, h2]
      ring
    rw [h4]
    -- Show numerator is greater than zero
    have h5 : a^2 * (a - 1) + b^2 * (b - 1) - 8 * (b - 1) * (a - 1) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2), sq_nonneg (a - 2), sq_nonneg (b - 2), 
        mul_pos h1 h2
      ]
    -- Denominator is positive
    have h6 : 0 < (b - 1) * (a - 1) := by 
      positivity
    -- Combine numerator and denominator to get final result
    exact div_nonneg h5 (by positivity)
  linarith