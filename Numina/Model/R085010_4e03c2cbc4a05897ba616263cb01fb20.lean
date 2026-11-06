import Mathlib

theorem inequalities_601504 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^3 / (b * c) + b^3 / (c * a) + c^3 / (a * b) ≥ a + b + c := by
  have pos1 : 0 < b * c := by nlinarith [hb, hc]
  have pos2 : 0 < c * a := by nlinarith [hc, ha]
  have pos3 : 0 < a * b := by nlinarith [ha, hb]
  have pos4 : 0 < a * b * c := by positivity

  have h1 : a^3 / (b * c) + b^3 / (c * a) + c^3 / (a * b) - (a + b + c) ≥ 0 := by

    have h2 : a^3 / (b * c) + b^3 / (c * a) + c^3 / (a * b) - (a + b + c) =
        (a^4 + b^4 + c^4 - (a + b + c) * (a * b * c)) / (a * b * c) := by
      field_simp [pos1, pos2, pos3, pos4]
      ring
    rw [h2]

    have h3 : a^4 + b^4 + c^4 ≥ a * b * c * (a + b + c) := by
      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]
    have h4 : (a^4 + b^4 + c^4 - (a + b + c) * (a * b * c)) ≥ 0 := by
      linarith
    have h5 : (a^4 + b^4 + c^4 - (a + b + c) * (a * b * c)) / (a * b * c) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith [h1
  ]