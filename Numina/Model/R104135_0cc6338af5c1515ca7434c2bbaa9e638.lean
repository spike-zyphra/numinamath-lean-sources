import Mathlib

theorem inequalities_315289 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 + a + b + c = 4 * a * b * c) :
    1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) ≤ 1 := by
  have h1 : 0 < 1 + a + b := by
    linarith [ha, hb]
  have h2 : 0 < 1 + b + c := by
    linarith [hb, hc]
  have h3 : 0 < 1 + c + a := by
    linarith [hc, ha]

  have h4 : 1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) - 1 ≤ 0 := by
    have h5 : 0 < (1 + a + b) * (1 + b + c) * (1 + c + a) := by positivity
    have h7 : (1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) - 1) =
        ((1 * (1 + b + c) * (1 + c + a) +
           1 * (1 + c + a) * (1 + a + b) +
           1 * (1 + a + b) * (1 + b + c) - (1 + a + b) * (1 + b + c) * (1 + c + a))
         / ((1 + a + b) * (1 + b + c) * (1 + c + a))) := by
      field_simp
      ring
    rw [h7]
    apply div_nonpos_of_nonpos_of_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos ha hb, mul_pos hb hc, mul_pos hc ha,
      h]
    positivity
  linarith