import Mathlib

theorem inequalities_105047
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
  have h1 : 0 < b + c := by nlinarith
  have h2 : 0 < c + a := by nlinarith
  have h3 : 0 < a + b := by nlinarith
  have h4 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h5 : (a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2) =
      ( (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 3 / 2 * (b + c) * (c + a) * (a + b)) ) / ((b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [h5]
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
    positivity
  linarith