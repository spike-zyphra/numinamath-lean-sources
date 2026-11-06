import Mathlib

theorem inequalities_8494 (a b c d : ℝ) (h₀ : a < b) (h₁ : b < c) (h₂ : c < d) :
    (a + b + c + d)^2 > 8 * (a * c + b * d) := by

  have h3 : b - a > 0 := by linarith
  have h4 : c - b > 0 := by linarith
  have h5 : d - c > 0 := by linarith
  have h6 : c - a > 0 := by linarith
  have h7 : d - b > 0 := by linarith
  have h8 : d - a > 0 := by linarith

  nlinarith [sq_pos_of_pos h3, sq_pos_of_pos h4, sq_pos_of_pos h5,
          sq_pos_of_pos h6, sq_pos_of_pos h7, sq_pos_of_pos h8,
          mul_pos h3 h4, mul_pos h4 h5, mul_pos h3 h5,
          mul_pos h3 h6, mul_pos h4 h7, mul_pos h5 h8,
          sq_nonneg (a + d - (b + c)), sq_nonneg (a + c - (b + d)), sq_nonneg (b - a - (d - c)), sq_nonneg (c - b - (d - a))]