import Mathlib

theorem inequalities_200106
    (a b c d : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d) :
    (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) ≥ 16 := by

  have h1 : 0 < a * b * c * d := by
    apply mul_pos
    apply mul_pos
    apply mul_pos
    all_goals linarith


  have h2 : (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) - 16 ≥ 0 := by
    have h3 : 0 < a * b * c * d := h1
    have h4 : (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) - 16 =
        ( (a + b + c + d) * (b * c * d + a * c * d + a * b * d + a * b * c) - 16 * a * b * c * d ) / (a * b * c * d) := by
      field_simp
      ring
    rw [h4]

    apply div_nonneg
    nlinarith [ 
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
        sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
        sq_nonneg (a * b - a * c), sq_nonneg (a * b - a * d), sq_nonneg (a * b - c * d),
        sq_nonneg (a * c - a * d), sq_nonneg (a * c - b * d), sq_nonneg (b * c - b * d),
        mul_pos ha hb, mul_pos ha hc, mul_pos ha hd,
        mul_pos hb hc, mul_pos hb hd, mul_pos hc hd 
    ]
    all_goals positivity

  linarith