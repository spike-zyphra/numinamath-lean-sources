import Mathlib

open Real

theorem inequalities_146955 (a b : ℝ) (ha : a ≠ 0) :
    a^2 + b^2 + 1 / a^2 + b / a ≥ sqrt 3 := by
  have h1 : a^2 + b^2 + 1 / a^2 + b / a = a^2 + (3 / 4) / a^2 + (b + 1 / (2 * a))^2 := by
    field_simp
    ring
  rw [h1]
  have h2 : a^2 + (3 / 4) / a^2 ≥ sqrt 3 := by
    have h3 : a^2 > 0 := by
      exact sq_pos_of_ne_zero (by exact ha)
    have h4 : a^2 + (3 / 4) / a^2 - sqrt 3 ≥ 0 := by
      have h5 : a^2 + (3 / 4) / a^2 - sqrt 3 = (4 * (a^2)^2 - 4 * sqrt 3 * (a^2) + 3) / (4 * (a^2)) := by
        field_simp
        ring
      rw [h5]
      have h6 : (4 * (a^2)^2 - 4 * sqrt 3 * (a^2) + 3 : ℝ) ≥ 0 := by
        nlinarith [Real.sqrt_nonneg 3, sq_nonneg (a^2 - sqrt 3 / 2), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (4 * (a^2) - 4 * sqrt 3) ]
      have h7 : (4 * (a^2)^2 - 4 * sqrt 3 * (a^2) + 3) / (4 * (a^2)) ≥ 0 := by
        apply div_nonneg
        linarith only [h6]
        nlinarith
      linarith only [h7]
    linarith only [h4]
  have h8 : (b + 1 / (2 * a))^2 ≥ 0 := by
    apply sq_nonneg
  linarith [h2, h8]