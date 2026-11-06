import Mathlib

theorem inequalities_603774 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 ≤ 1 / (1 + 3 * a) + 1 / (1 + 3 * b) + 1 / (1 + 3 * c) +
        1 / (1 + a + b + c) := by

  have h3 : 1 / (1 + 3 * a) + 1 / (1 + 3 * b) + 1 / (1 + 3 * c) + 1 / (1 + a + b + c) - 1 ≥ 0 := by
    have pos1 : 0 < (1 + 3 * a) * (1 + 3 * b) * (1 + 3 * c) * (1 + a + b + c) := by
      positivity
    have h4 : (1 / (1 + 3 * a) + 1 / (1 + 3 * b) + 1 / (1 + 3 * c) + 1 / (1 + a + b + c) - 1) =
        ((1 + 3 * b) * (1 + 3 * c) * (1 + a + b + c) + (1 + 3 * a) * (1 + 3 * c) * (1 + a + b + c) + (1 + 3 * a) * (1 + 3 * b) * (1 + a + b + c) + (1 + 3 * a) * (1 + 3 * b) * (1 + 3 * c) - (1 + 3 * a) * (1 + 3 * b) * (1 + 3 * c) * (1 + a + b + c)) / ((1 + 3 * a) * (1 + 3 * b) * (1 + 3 * c) * (1 + a + b + c)) := by
      field_simp
      <;> ring
    rw [h4] at *
    apply div_nonneg
    · -- Show the numerator is ≥ 0
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        sq_nonneg (a * b + b * c + c * a - 3), sq_nonneg (a + b + c - 3),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (mul_pos ha hb) hc
      ]
    all_goals
      positivity

  linarith