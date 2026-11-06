import Mathlib

theorem inequalities_602070 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 3) :
    3 ≤ (a + b) / (1 + b) + (b + c) / (1 + c) + (c + a) / (1 + a) := by
  have h1 : 0 < 1 + a := by linarith
  have h2 : 0 < 1 + b := by linarith
  have h3 : 0 < 1 + c := by linarith
  have h4 : (a + b) / (1 + b) + (b + c) / (1 + c) + (c + a) / (1 + a) - 3 ≥ 0 := by
    have h5 : (a + b) / (1 + b) + (b + c) / (1 + c) + (c + a) / (1 + a) - 3 =
        ( (a + b) * (1 + c) * (1 + a) + (b + c) * (1 + a) * (1 + b) + (c + a) * (1 + b) * (1 + c) - 3 * (1 + a) * (1 + b) * (1 + c) ) / ( (1 + b) * (1 + c) * (1 + a) ) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        hsum, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc
    ]
    positivity
  linarith