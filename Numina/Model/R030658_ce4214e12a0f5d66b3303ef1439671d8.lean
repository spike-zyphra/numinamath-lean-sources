import Mathlib

theorem inequalities_598385 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * b / (a ^ 2 + a * b + b * c) + b * c / (b ^ 2 + b * c + c * a) +
    c * a / (c ^ 2 + c * a + a * b) ≤ 1 := by

  have h1 : 0 < a * b := by
    nlinarith
  have h2 : 0 < b * c := by
    nlinarith
  have h3 : 0 < c * a := by
    nlinarith
  have h4 : 0 < a ^ 2 + a * b + b * c := by
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h5 : 0 < b ^ 2 + b * c + c * a := by
    nlinarith [mul_pos hb hc, mul_pos ha hc, mul_pos ha hb]
  have h6 : 0 < c ^ 2 + c * a + a * b := by
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h7 : a * b / (a ^ 2 + a * b + b * c) + b * c / (b ^ 2 + b * c + c * a) +
      c * a / (c ^ 2 + c * a + a * b) - 1 ≤ 0 := by
    have h8 : a * b / (a ^ 2 + a * b + b * c) + b * c / (b ^ 2 + b * c + c * a) +
        c * a / (c ^ 2 + c * a + a * b) - 1 =
        ( (a * b) * (b ^ 2 + b * c + c * a) * (c ^ 2 + c * a + a * b) +
            (b * c) * (a ^ 2 + a * b + b * c) * (c ^ 2 + c * a + a * b) +
            (c * a) * (a ^ 2 + a * b + b * c) * (b ^ 2 + b * c + c * a) - (a ^ 2 + a * b + b * c) * (b ^ 2 + b * c + c * a) * (c ^ 2 + c * a + a * b) ) / ( (a ^ 2 + a * b + b * c) * (b ^ 2 + b * c + c * a) * (c ^ 2 + c * a + a * b) ) := by
      field_simp
      ring
    rw [h8]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is non-positive.
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith),
          mul_pos (show 0 < a * b by nlinarith) (show 0 < c * a by nlinarith),
          mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith) ]
    · -- Show that the denominator is non-negative.
      positivity
  linarith