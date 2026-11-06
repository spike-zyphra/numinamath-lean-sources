import Mathlib

theorem inequalities_599433 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 8) :
    (a - 2) / (a + 1) + (b - 2) / (b + 1) + (c - 2) / (c + 1) ≤ 0 := by
  have h1 : 0 < a + 1 := by linarith
  have h2 : 0 < b + 1 := by linarith
  have h3 : 0 < c + 1 := by linarith
  have h4 : (a + 1) * (b + 1) * (c + 1) > 0 := by positivity
  have h5 : (a - 2) / (a + 1) + (b - 2) / (b + 1) + (c - 2) / (c + 1) =
      ((a - 2) * (b + 1) * (c + 1) + (b - 2) * (a + 1) * (c + 1) + (c - 2) * (a + 1) * (b + 1)) / ((a + 1) * (b + 1) * (c + 1)) := by
    field_simp
    ring
  rw [h5]
  apply div_nonpos_of_nonpos_of_nonneg
  -- Show that the numerator is non-positive
  have h7 : (a - 2) * (b + 1) * (c + 1) + (b - 2) * (a + 1) * (c + 1) + (c - 2) * (a + 1) * (b + 1) ≤ 0 := by
    nlinarith [sq_nonneg (a * b - 4), sq_nonneg (a * c - 4), sq_nonneg (b * c - 4),
      sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  linarith
  -- Show that the denominator is non-negative
  positivity