import Mathlib

theorem inequalities_263079 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 1) :
    2 * (a^3 + b^3 + c^3) / (a * b * c) + 3 ≤
    1 / a^2 + 1 / b^2 + 1 / c^2 := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : 1 / a^2 + 1 / b^2 + 1 / c^2 - (2 * (a^3 + b^3 + c^3) / (a * b * c) + 3) ≥ 0 := by
    have h3 : 0 < a * b * c := h1
    have h4 : 1 / a^2 + 1 / b^2 + 1 / c^2 - (2 * (a^3 + b^3 + c^3) / (a * b * c) + 3) = (b^2 * c^2 + a^2 * c^2 + a^2 * b^2 - 2 * (a^3 + b^3 + c^3) * (a * b * c) - 3 * (a * b * c) ^ 2) / (a^2 * b^2 * c^2) := by
      field_simp
      ring
    rw [h4] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < b * c from mul_pos hb hc),
      mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < c * a from mul_pos hc ha),
      mul_pos (show 0 < b * c from mul_pos hb hc) (show 0 < c * a from mul_pos hc ha), 
      h, mul_pos (show 0 < a from ha) (show 0 < b from hb), 
      mul_pos (show 0 < b from hb) (show 0 < c from hc), 
      mul_pos (show 0 < a from ha) (show 0 < c from hc)
    ]
    positivity
  linarith