import Mathlib

theorem inequalities_602502 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 + b * c) / (b + c) + (b ^ 2 + c * a) / (c + a) + (c ^ 2 + a * b) / (a + b) ≥
    a + b + c := by
  have h1 : b + c > 0 := by nlinarith
  have h2 : c + a > 0 := by nlinarith
  have h3 : a + b > 0 := by nlinarith
  have h4 : (a ^ 2 + b * c) / (b + c) + (b ^ 2 + c * a) / (c + a) + (c ^ 2 + a * b) / (a + b) - (a + b + c) ≥ 0 := by
    have h5 : (a ^ 2 + b * c) / (b + c) + (b ^ 2 + c * a) / (c + a) + (c ^ 2 + a * b) / (a + b) - (a + b + c) =
        ((a ^ 2 + b * c) * (c + a) * (a + b) + (b ^ 2 + c * a) * (b + c) * (a + b) + (c ^ 2 + a * b) * (b + c) * (c + a) - (a + b + c) * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [h5]
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
    positivity
  linarith