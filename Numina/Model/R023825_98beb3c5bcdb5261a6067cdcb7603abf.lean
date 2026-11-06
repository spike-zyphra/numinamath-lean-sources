import Mathlib

theorem inequalities_302672 (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    a^2 / (b - 1) + b^2 / (a - 1) ≥ 8 := by
  have h1 : 0 < b - 1 := by linarith
  have h2 : 0 < a - 1 := by linarith
  have h3 : a^2 / (b - 1) + b^2 / (a - 1) - (8 : ℝ) ≥ 0 := by
    have pos1 : (b - 1) * (a - 1) > 0 := mul_pos h1 h2
    have h4 : a^2 / (b - 1) + b^2 / (a - 1) - 8 = (a^2 * (a - 1) + b^2 * (b - 1) - 8 * (b - 1) * (a - 1)) / ((b - 1) * (a -1)) := by
      field_simp
      <;> ring
    rw [h4] at *
    have pos2 : (b - 1) * (a - 1) > 0 := by positivity
    have h5 : a^2 * (a - 1) + b^2 * (b - 1) - 8 * (b - 1) * (a - 1) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - 2), sq_nonneg (b - 2),
        sq_nonneg (a * b - 4), mul_pos (show 0 < a - 1 by linarith) (show 0 < b - 1 by linarith),
        pow_two_nonneg (a - 2), pow_two_nonneg (b - 2)
        ]
    apply div_nonneg
    · linarith [h5]
    · positivity
  linarith [h3]