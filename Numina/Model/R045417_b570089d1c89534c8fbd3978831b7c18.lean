import Mathlib

theorem inequalities_128273 (a b : ℝ) (_ : 0 < a) (h₀ : 0 < b) (h₁ : a ≠ b) :
    a^3 * b^2 + a^2 * b^3 < a^5 + b^5 := by

  have h2 : a - b ≠ 0 := by
    intro h
    apply h₁
    linarith
  -- Show that $(a - b)^2 > 0$ since $a \neq b$.
  have h3 : (a - b) ^ 2 > 0 := by
    apply pow_two_pos_of_ne_zero
    exact h2
  -- Show that $a + b > 0$.
  have h4 : a + b > 0 := by nlinarith [show 0 < a from by assumption, show 0 < b from by assumption]
  -- Show that $a^2 + ab + b^2 > 0$.
  have h5 : a^2 + a * b + b^2 > 0 := by
    nlinarith [sq_nonneg (a - b), sq_pos_of_pos (show (0 : ℝ) < a from by assumption), sq_pos_of_pos (show (0 : ℝ) < b from by assumption), sq_nonneg (a + b)]
  -- Show that $(a - b)^2 \cdot (a + b) \cdot (a^2 + ab + b^2) > 0$.
  have h6 : (a - b) ^ 2 * (a + b) * (a^2 + a * b + b^2) > 0 := by
    apply mul_pos
    apply mul_pos
    exact h3
    exact h4
    exact h5

  -- Show that $a^5 + b^5 - (a^3 \cdot b^2 + a^2 \cdot b^3) > 0$.
  have h7 : a^5 + b^5 - (a^3 * b^2 + a^2 * b^3) > 0 := by
    nlinarith [sq_nonneg (a - b), sq_pos_of_pos (show (0 : ℝ) < a from by assumption), sq_pos_of_pos (show (0 : ℝ) < b from by assumption), sq_pos_of_ne_zero (show a - b ≠ 0 by exact h2), sq_nonneg (a^2 - b^2), sq_nonneg (a^3 - b^3), h6]
  -- Rearrange the inequality using linear arithmetic.
  linarith [h7]