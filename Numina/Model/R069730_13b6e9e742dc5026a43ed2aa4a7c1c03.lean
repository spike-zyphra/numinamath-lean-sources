import Mathlib

theorem inequalities_118726 (a b : ℝ) (ha : a ≠ 0) : a^2 + b^2 + 2 / a^2 + 2 * b / a ≥ 2 := by
  have h4 : a^2 + 1 / a^2 ≥ 2 := by
    have h2 : a^2 > 0 := by
      exact sq_pos_of_ne_zero ha
    have h3 : a^2 + 1 / a^2 - 2 ≥ 0 := by
      have h4 : a^2 + 1 / a^2 - 2 = (a^4 + 1 - 2 * a^2) / a^2 := by
        field_simp
        ring
      rw [h4]
      apply div_nonneg
      nlinarith [sq_nonneg (a ^ 2 - 1)]
      positivity
    linarith

  have h5 : (b + 1 / a) ^ 2 ≥ 0 := by
    apply sq_nonneg

  have h6 : a^2 + 1 / a^2 + (b + 1 / a) ^ 2 ≥ 2 := by
    linarith [h4, h5]

  have h7 : a^2 + b^2 + 2 / a^2 + 2 * b / a = a^2 + 1 / a^2 + (b + 1 / a) ^ 2 := by
    field_simp
    ring

  rw [h7]
  linarith [h6]