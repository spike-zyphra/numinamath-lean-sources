import Mathlib

theorem inequalities_114441 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    1 / a + 1 / b + 9 / c + 25 / d ≥ 100 / (a + b + c + d) := by
  have h1 : 0 < a * b * c * d := by
    apply mul_pos
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
    exact hd

  have h2 : 1 / a + 1 / b + 9 / c + 25 / d - 100 / (a + b + c + d) ≥ 0 := by
    have pos1 : 0 < a := ha
    have pos2 : 0 < b := hb
    have pos3 : 0 < c := hc
    have pos4 : 0 < d := hd
    have pos5 : 0 < a + b + c + d := by
      linarith
    have h3 : 1 / a + 1 / b + 9 / c + 25 / d - 100 / (a + b + c + d) =
        ( (b * c * d * (a + b + c + d) + a * c * d * (a + b + c + d) + 9 * a * b * d * (a + b + c + d) + 25 * a * b * c * (a + b + c + d) - 100 * a * b * c * d ) ) / ( (a * b * c * d * (a + b + c + d) ) ) := by
      field_simp
      ring
    rw [h3] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c / 3), sq_nonneg (a - d / 5),
      sq_nonneg (b - c / 3), sq_nonneg (b - d / 5),
      sq_nonneg (c / 3 - d / 5),
      sq_nonneg (a + b - c / 3 - d / 5),
      mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd
    ]
    positivity
  linarith [h2]