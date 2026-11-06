import Mathlib

theorem inequalities_52697 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (2 * a + b) + b / (2 * b + c) + c / (2 * c + a) ≤ 1 := by
  have h1 : 0 < (2 * a + b) * (2 * b + c) * (2 * c + a) := by
    positivity
  have h2 : a / (2 * a + b) + b / (2 * b + c) + c / (2 * c + a) - 1 ≤ 0 := by
    have pos1 : 0 < (2 * a + b) * (2 * b + c) * (2 * c + a) := h1
    have h3 : a / (2 * a + b) + b / (2 * b + c) + c / (2 * c + a) - 1 =
        (a * (2 * b + c) * (2 * c + a) + b * (2 * a + b) * (2 * c + a) + c * (2 * a + b) * (2 * b + c) - (2 * a + b) * (2 * b + c) * (2 * c + a)) / ((2 * a + b) * (2 * b + c) * (2 * c + a)) := by
      field_simp
      ring
    rw [h3] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is nonpositive.
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
    · -- Show that the denominator is nonnegative.
      positivity
  linarith