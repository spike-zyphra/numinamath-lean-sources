import Mathlib

theorem inequalities_33048 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 8) :
    1 / a + 1 / b + 4 / c + 16 / d ≥ 8 := by
  have h1 : 0 < a * b * c * d := by
    positivity
  have h2 : 1 / a + 1 / b + 4 / c + 16 / d - 8 ≥ 0 := by
    have h3 : 0 < a * b * c * d := h1
    have h4 : 1 / a + 1 / b + 4 / c + 16 / d - 8 = (b * c * d + a * c * d + 4 * a * b * d + 16 * a * b * c - 8 * (a * b * c * d)) / (a * b * c * d) := by
      field_simp
      ring
    rw [h4] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c / 2), sq_nonneg (a - d / 4), 
          sq_nonneg (b - c / 2), sq_nonneg (b - d / 4), sq_nonneg (c / 2 - d / 4), 
          h, 
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
          mul_pos hb hc, mul_pos hb hd, 
          mul_pos hc hd
        ]
    positivity
  linarith