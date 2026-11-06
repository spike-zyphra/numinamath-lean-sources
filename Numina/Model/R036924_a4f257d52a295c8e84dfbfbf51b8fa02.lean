import Mathlib

theorem inequalities_60401 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    9 / 2 * 1 / (a + b + c) ≤ 1 / (a + b) + 1 / (b + c) + 1 / (c + a) := by
  have h1 : 0 < a + b := by linarith
  have h2 : 0 < b + c := by linarith
  have h3 : 0 < c + a := by linarith
  have h4 : 0 < a + b + c := by linarith
  have h5 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) - 9 / 2 * 1 / (a + b + c) ≥ 0 := by
    have pos1 : 0 < (a + b) * (b + c) * (c + a) * (a + b + c) := by positivity
    have h5 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) - 9 / 2 * 1 / (a + b + c) =
        ( (b + c) * (c + a) * (a + b + c) + (a + b) * (c + a) * (a + b + c) + (a + b) * (b + c) * (a + b + c) - (9 / 2) * (a + b) * (b + c) * (c + a) ) / ( (a + b) * (b + c) * (c + a) * (a + b + c) ) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [ sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc ]
    positivity
  linarith