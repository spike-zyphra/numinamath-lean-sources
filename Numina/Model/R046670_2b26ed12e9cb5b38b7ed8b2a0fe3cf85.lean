import Mathlib

theorem inequalities_600560
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    a^3 / (b + 2 * c) + b^3 / (c + 2 * a) + c^3 / (a + 2 * b) ≥
    (a^2 + b^2 + c^2) / 3 := by
  have h1 : 0 < b + 2 * c := by
    linarith
  have h2 : 0 < c + 2 * a := by
    linarith
  have h3 : 0 < a + 2 * b := by
    linarith
  have h4 : a^3 / (b + 2 * c) + b^3 / (c + 2 * a) + c^3 / (a + 2 * b) - (a^2 + b^2 + c^2) / 3 ≥ 0 := by
    have h5 : a^3 / (b + 2 * c) + b^3 / (c + 2 * a) + c^3 / (a + 2 * b) - (a^2 + b^2 + c^2) / 3 =
        (a^3 * (c + 2 * a) * (a + 2 * b) + b^3 * (b + 2 * c) * (a + 2 * b) + c^3 * (b + 2 * c) * (c + 2 * a) - (a^2 + b^2 + c^2) * ( (b + 2 * c) * (c + 2 * a) * (a + 2 * b) ) / 3 ) / ( (b + 2 * c) * (c + 2 * a) * (a + 2 * b) ) := by
      field_simp
      ring
    rw [h5] at *
    have h6 : 0 < (b + 2 * c) * (c + 2 * a) * (a + 2 * b) := by
      positivity
    have h7 : a^3 * (c + 2 * a) * (a + 2 * b) + b^3 * (b + 2 * c) * (a + 2 * b) + c^3 * (b + 2 * c) * (c + 2 * a) - (a^2 + b^2 + c^2) * ( (b + 2 * c) * (c + 2 * a) * (a + 2 * b) ) / 3 ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    apply div_nonneg h7 (by positivity)
  linarith