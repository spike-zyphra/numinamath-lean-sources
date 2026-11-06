import Mathlib

theorem inequalities_600340 (a b c : ℝ) (h : a * b * c ≠ 0) :
    a ^ 4 / (4 * a ^ 4 + b ^ 4 + c ^ 4) +
    b ^ 4 / (a ^ 4 + 4 * b ^ 4 + c ^ 4) +
    c ^ 4 / (a ^ 4 + b ^ 4 + 4 * c ^ 4) ≤ 1 / 2 := by
  have h1 : a ≠ 0 := by
    by_contra h1
    have h2 : a * b * c = 0 := by
      simp [h1]
    contradiction
  have h2 : b ≠ 0 := by
    by_contra h2
    have h3 : a * b * c = 0 := by
      simp [h2]
    contradiction
  have h3 : c ≠ 0 := by
    by_contra h3
    have h4 : a * b * c = 0 := by
      simp [h3]
    contradiction
  have h4 : 0 < 4 * a ^ 4 + b ^ 4 + c ^ 4 := by
    nlinarith [sq_nonneg (a ^ 2), sq_nonneg (b ^ 2), sq_nonneg (c ^ 2),
      sq_pos_of_ne_zero (show a ≠ 0 by exact h1),
      sq_pos_of_ne_zero (show b ≠ 0 by exact h2),
      sq_pos_of_ne_zero (show c ≠ 0 by exact h3),
      sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c)]
  have h5 : 0 < a ^ 4 + 4 * b ^ 4 + c ^ 4 := by
    nlinarith [sq_nonneg (a ^ 2), sq_nonneg (b ^ 2), sq_nonneg (c ^ 2),
      sq_pos_of_ne_zero (show a ≠ 0 by exact h1),
      sq_pos_of_ne_zero (show b ≠ 0 by exact h2),
      sq_pos_of_ne_zero (show c ≠ 0 by exact h3),
      sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c)]
  have h6 : 0 < a ^ 4 + b ^ 4 + 4 * c ^ 4 := by
    nlinarith [sq_nonneg (a ^ 2), sq_nonneg (b ^ 2), sq_nonneg (c ^ 2),
      sq_pos_of_ne_zero (show a ≠ 0 by exact h1),
      sq_pos_of_ne_zero (show b ≠ 0 by exact h2),
      sq_pos_of_ne_zero (show c ≠ 0 by exact h3),
      sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c)]
  have h7 : a ^ 4 / (4 * a ^ 4 + b ^ 4 + c ^ 4) + b ^ 4 / (a ^ 4 + 4 * b ^ 4 + c ^ 4) + c ^ 4 / (a ^ 4 + b ^ 4 + 4 * c ^ 4) - 1 / 2 ≤ 0 := by
    have h8 : a ^ 4 / (4 * a ^ 4 + b ^ 4 + c ^ 4) + b ^ 4 / (a ^ 4 + 4 * b ^ 4 + c ^ 4) + c ^ 4 / (a ^ 4 + b ^ 4 + 4 * c ^ 4) - 1 / 2 ≤ 0 := by
      have h9 : 0 < (4 * a ^ 4 + b ^ 4 + c ^ 4) * (a ^ 4 + 4 * b ^ 4 + c ^ 4) * (a ^ 4 + b ^ 4 + 4 * c ^ 4) := by positivity
      have h10 : a ^ 4 / (4 * a ^ 4 + b ^ 4 + c ^ 4) + b ^ 4 / (a ^ 4 + 4 * b ^ 4 + c ^ 4) + c ^ 4 / (a ^ 4 + b ^ 4 + 4 * c ^ 4) - 1 / 2 =
          ( (a ^ 4) * (a ^ 4 + 4 * b ^ 4 + c ^ 4) * (a ^ 4 + b ^ 4 + 4 * c ^ 4) +
            (b ^ 4) * (4 * a ^ 4 + b ^ 4 + c ^ 4) * (a ^ 4 + b ^ 4 + 4 * c ^ 4) +
            (c ^ 4) * (4 * a ^ 4 + b ^ 4 + c ^ 4) * (a ^ 4 + 4 * b ^ 4 + c ^ 4) - 1 / 2 * (4 * a ^ 4 + b ^ 4 + c ^ 4) * (a ^ 4 + 4 * b ^ 4 + c ^ 4) * (a ^ 4 + b ^ 4 + 4 * c ^ 4) ) / ( (4 * a ^ 4 + b ^ 4 + c ^ 4) * (a ^ 4 + 4 * b ^ 4 + c ^ 4) * (a ^ 4 + b ^ 4 + 4 * c ^ 4) ) := by
        field_simp
        ring
      rw [h10] at *
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show the numerator is non-positive
        nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2),
          sq_nonneg (a^2 * b^2 - a^2 * c^2), sq_nonneg (b^2 * c^2 - a^2 * b^2), sq_nonneg (a^2 * c^2 - b^2 * c^2),
          sq_nonneg (a^4 - b^4), sq_nonneg (b^4 - c^4), sq_nonneg (a^4 - c^4),
          sq_nonneg (a^2 * b^2 - a^2 * c^2), sq_nonneg (b^2 * c^2 - a^2 * b^2), sq_nonneg (a^2 * c^2 - b^2 * c^2),
          mul_pos (show 0 < a^2 by positivity) (show 0 < b^2 by positivity),
          mul_pos (show 0 < a^2 by positivity) (show 0 < c^2 by positivity),
          mul_pos (show 0 < b^2 by positivity) (show 0 < c^2 by positivity)]
      · -- Show the denominator is non-negative
        positivity
    linarith
  linarith