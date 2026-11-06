import Mathlib

theorem inequalities_121790 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    64 / (a + b + c + d) ≤ 1 / a + 1 / b + 4 / c + 16 / d := by
  have h1 : 0 < a * b * c * d := by
    positivity
  have h2 : 0 < a + b + c + d := by
    positivity
  have h3 : 1 / a + 1 / b + 4 / c + 16 / d - 64 / (a + b + c + d) ≥ 0 := by
    have h4 : a * b * c * d > 0 := by positivity
    have h5 : a + b + c + d > 0 := by positivity
    have h6 : (1 / a + 1 / b + 4 / c + 16 / d - 64 / (a + b + c + d)) =
        ( (b * c * d * (a + b + c + d) + a * c * d * (a + b + c + d) + 4 * a * b * d * (a + b + c + d) + 16 * a * b * c * (a + b + c + d) - 64 * (a * b * c * d) ) / (a * b * c * d * (a + b + c + d)) ) := by
      field_simp
      <;> ring
      all_goals positivity
    rw [h6] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c / 2), sq_nonneg (a - d / 4), sq_nonneg (b - c / 2), sq_nonneg (b - d / 4), sq_nonneg (c / 2 - d / 4),
      sq_nonneg (a * b - a * c / 2), sq_nonneg (a * b - a * d / 4), sq_nonneg (a * b - b * c / 2), sq_nonneg (a * b - b * d / 4), sq_nonneg (a * c / 2 - b * c / 2), sq_nonneg (a * c / 2 - b * d / 4),
      mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd,
      mul_pos (show 0 < a * b by positivity) (show 0 < c * d by positivity)
      ]
    all_goals positivity
  linarith