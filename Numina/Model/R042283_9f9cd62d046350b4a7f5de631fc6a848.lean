import Mathlib

theorem inequalities_87916 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    69 / 4 ≤ (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) := by
  have h1 : 0 < (1 + a) * (1 + b) * (1 + c) := by
    positivity
  have h2 : (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) - 69 / 4 ≥ 0 := by
    have h3 : 0 < (1 + a) := by linarith
    have h4 : 0 < (1 + b) := by linarith
    have h5 : 0 < (1 + c) := by linarith
    have h6 : (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) - 69 / 4 =
        ((7 + 2 * b) * (1 + b) * (1 + c) + (7 + 2 * c) * (1 + a) * (1 + c) + (7 + 2 * a) * (1 + a) * (1 + b) - (69 / 4) * (1 + a) * (1 + b) * (1 + c)) / ((1 + a) * (1 + b) * (1 + c)) := by 
      field_simp
      ring 
    rw [h6] at *
    apply div_nonneg
    -- Show that the numerator is non-negative
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
      sq_nonneg (a - 1 / 4), sq_nonneg (b - 1 / 4), sq_nonneg (c - 1 / 4),
      h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    all_goals 
      positivity
  linarith