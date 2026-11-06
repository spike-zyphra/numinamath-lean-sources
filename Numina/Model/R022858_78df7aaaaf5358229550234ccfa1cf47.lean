import Mathlib


theorem inequalities_67609 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 + a * b * c = 4) :
    (a + b) / c + (b + c) / a + (c + a) / b ≥
    a + b + c + 1 / a + 1 / b + 1 / c := by 
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h3 : (a + b) / c + (b + c) / a + (c + a) / b - (a + b + c + 1 / a + 1 / b + 1 / c) ≥ 0 := by
    have h4 : (a + b) / c + (b + c) / a + (c + a) / b - (a + b + c + 1 / a + 1 / b + 1 / c) =
        ( (a + b) * a * b + (b + c) * b * c + (c + a) * c * a - (a + b + c) * (a * b * c) - (b * c + a * c + a * b) ) / (a * b * c) := by
      field_simp
      ring
    rw [h4]
    have h5 : (a + b) * a * b + (b + c) * b * c + (c + a) * c * a - (a + b + c) * (a * b * c) - (b * c + a * c + a * b) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * b + b * c + c * a - a * b * c), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (mul_pos ha hb) hc
      ]
    have h7 : ( (a + b) * a * b + (b + c) * b * c + (c + a) * c * a - (a + b + c) * (a * b * c) - (b * c + a * c + a * b) ) / (a * b * c) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith