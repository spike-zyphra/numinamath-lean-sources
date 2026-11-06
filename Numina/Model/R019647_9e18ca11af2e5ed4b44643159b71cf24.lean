import Mathlib

theorem inequalities_5545 (a b c : ℝ) (habc : a ≠ b ∧ b ≠ c ∧ a ≠ c) :
    (1 / (a - b)^2 + 1 / (b - c)^2 + 1 / (c - a)^2) * (a^2 + b^2 + c^2) ≥
    (a / (b - c))^2 + (b / (c - a))^2 + (c / (a - b))^2 + 1 := by
  rcases habc with ⟨ha1, hb1, ha2⟩
  have hab2 : a - b ≠ 0 := by
    intro h
    apply ha1
    linarith
  have hbc2 : b - c ≠ 0 := by
    intro h
    apply hb1
    linarith
  have hca2 : c - a ≠ 0 := by
    intro h
    apply ha2
    linarith
  have h1 : (1 / (a - b)^2 + 1 / (b - c)^2 + 1 / (c - a)^2) * (a^2 + b^2 + c^2) - ((a / (b - c))^2 + (b / (c - a))^2 + (c / (a - b))^2 + 1) ≥ 0 := by
    have h2 : 0 < (a - b)^2 := by
      apply pow_two_pos_of_ne_zero
      intro h
      apply ha1
      linarith
    have h3 : 0 < (b - c)^2 := by
      apply pow_two_pos_of_ne_zero
      intro h
      apply hb1
      linarith
    have h4 : 0 < (c - a)^2 := by
      apply pow_two_pos_of_ne_zero
      intro h
      apply ha2
      linarith
    have h5 : (1 / (a - b)^2 + 1 / (b - c)^2 + 1 / (c - a)^2) * (a^2 + b^2 + c^2) - ((a / (b - c))^2 + (b / (c - a))^2 + (c / (a - b))^2 + 1) =
          ( (a^2 + b^2 + c^2) * ((b - c)^2 * (c - a)^2 + (a - b)^2 * (c - a)^2 + (a - b)^2 * (b - c)^2) - ((a^2 * (a - b)^2 * (c - a)^2 + b^2 * (a - b)^2 * (b - c)^2 + c^2 * (b - c)^2 * (c - a)^2 ) + (b - c)^2 * (c - a)^2 * (a - b)^2 ) ) / ((a - b)^2 * (b - c)^2 * (c - a)^2) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    -- Show that the numerator is non-negative
    nlinarith [sq_nonneg (a * (b - c) + b * (c - a) + c * (a - b)), sq_nonneg (a * (b - c) - b * (c - a) - c * (a - b)), sq_nonneg (a * (c - a) - b * (a - b) + c * (b - c)), sq_nonneg (a * (b - c) - b * (a - b) + c * (c - a)), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a * b - b * c), sq_nonneg (a * b - a * c), sq_nonneg (a * c - b * c), sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), mul_pos (show (0 : ℝ) < (a - b)^2 by positivity) (show (0 : ℝ) < (b - c)^2 by positivity), mul_pos (show (0 : ℝ) < (a - b)^2 by positivity) (show (0 : ℝ) < (c - a)^2 by positivity), mul_pos (show (0 : ℝ) < (b - c)^2 by positivity) (show (0 : ℝ) < (c - a)^2 by positivity)]
    -- Show that the denominator is positive
    positivity
  linarith [h1]