import Mathlib

theorem inequalities_90629 (a b : ℝ) (_ : 0 < a) (h₀ : 0 < b)
    (h₁ : a + b = a * b) :
    1 / 2 ≤ a / (b ^ 2 + 4) + b / (a ^ 2 + 4) := by
  have h2 : a / (b ^ 2 + 4) + b / (a ^ 2 + 4) - 1 / 2 ≥ 0 := by
    have pos1 : 0 < (b^2 + 4) * (a^2 + 4) := by positivity
    have h3 : a / (b ^ 2 + 4) + b / (a ^ 2 + 4) - 1 / 2 =
        (2 * a * (a^2 + 4) + 2 * b * (b^2 + 4) - (b^2 + 4) * (a^2 + 4)) / (2 * (b^2 + 4) * (a^2 + 4)) := by 
      field_simp
      ring
    rw [h3] at *
    apply div_nonneg
    -- Show that the numerator is non-negative
    have h1' : a + b = a * b := h₁
    have h4 : 0 ≤ 2 * a * (a ^ 2 + 4) + 2 * b * (b ^ 2 + 4) - (b^2 + 4) * (a ^ 2 + 4) := by
      have h5 : a * b ≥ 4 := by
        nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), 
          mul_pos (show 0 < (a : ℝ) by linarith) (show 0 < (b : ℝ) by linarith), 
          sq_nonneg (a * b - 4), sq_nonneg ((a + b) - 4)]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - 4), sq_nonneg (a ^ 2 - b ^ 2), 
        sq_nonneg (a * (a - 2)), sq_nonneg (b * (b - 2)), 
        sq_nonneg (a - 2), sq_nonneg (b - 2), 
        mul_pos (show 0 < (a : ℝ) by linarith) (show 0 < (b : ℝ) by linarith), 
        sq_nonneg (a * b - a - b)]
    linarith
    -- Show that the denominator is positive
    all_goals positivity
  linarith