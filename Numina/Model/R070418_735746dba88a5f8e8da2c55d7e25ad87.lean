import Mathlib

theorem inequalities_601350 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
  have h1 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h2 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
        (2 * a^3 + 2 * b^3 + 2 * c^3 - a^2 * b - a^2 * c - a * b^2 - b^2 * c - a * c^2 - b * c^2) / (2 * (b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [h2]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a - b + c), sq_nonneg (b - c + a), sq_nonneg (c - a + b),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
    -- Show that denominator is positive
    positivity
  linarith