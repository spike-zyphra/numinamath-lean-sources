import Mathlib

theorem inequalities_133173 (a b c : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (h : a^2 + b^2 + c^2 = 12) :
    3 ≤ 1 / (a - 1) + 1 / (b - 1) + 1 / (c - 1) := by

  have ha1 : 0 < a - 1 := by linarith
  have hb1 : 0 < b - 1 := by linarith
  have hc1 : 0 < c - 1 := by linarith

  have h1 : (b - 1) * (c - 1) + (a - 1) * (c - 1) + (a - 1) * (b - 1) ≥ 3 * (a - 1) * (b - 1) * (c - 1) := by
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
      sq_nonneg (a * b - 4), sq_nonneg (a * c - 4), sq_nonneg (b * c - 4),
        mul_pos ha1 hb1, mul_pos ha1 hc1, mul_pos hb1 hc1
       ]

  have h2 : 1 / (a - 1) + 1 / (b - 1) + 1 / (c - 1) - 3 ≥ 0 := by
    have h3 : (a - 1) * (b - 1) * (c - 1) > 0 := by
      positivity
    have h4 : 1 / (a - 1) + 1 / (b - 1) + 1 / (c - 1) - 3 =
        ((b - 1) * (c - 1) + (a - 1) * (c - 1) + (a - 1) * (b - 1) - 3 * (a - 1) * (b - 1) * (c - 1)) / ((a - 1) * (b - 1) * (c - 1)) := by
      field_simp [ne_of_gt ha1, ne_of_gt hb1, ne_of_gt hc1]
      ring
    rw [h4] at *
    apply div_nonneg
    linarith [h1]
    positivity

  linarith [h2]