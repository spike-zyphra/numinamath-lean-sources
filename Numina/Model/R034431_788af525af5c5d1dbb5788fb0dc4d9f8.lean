import Mathlib
theorem algebra_604441 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 / 3 * (a ^ 2 + b ^ 2 + c ^ 2) ≤
    (a ^ 3 + 3 * b ^ 3) / (5 * a + b) + (b ^ 3 + 3 * c ^ 3) / (5 * b + c) +
    (c ^ 3 + 3 * a ^ 3) / (5 * c + a) := by
  have h1 : 0 < 5 * a + b := by nlinarith
  have h2 : 0 < 5 * b + c := by nlinarith
  have h3 : 0 < 5 * c + a := by nlinarith
  have h4 : (a ^ 3 + 3 * b ^ 3) / (5 * a + b) + (b ^ 3 + 3 * c ^ 3) / (5 * b + c) + (c ^ 3 + 3 * a ^ 3) / (5 * c + a) - 2 / 3 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 0 := by
    have pos1 : 0 < (5 * a + b) * (5 * b + c) * (5 * c + a) := by positivity
    have h5 : (a ^ 3 + 3 * b ^ 3) / (5 * a + b) + (b ^ 3 + 3 * c ^ 3) / (5 * b + c) + (c ^ 3 + 3 * a ^ 3) / (5 * c + a) - 2 / 3 * (a ^ 2 + b ^ 2 + c ^ 2) = ((a ^ 3 + 3 * b ^ 3) * (5 * b + c) * (5 * c + a) + (b ^ 3 + 3 * c ^ 3) * (5 * a + b) * (5 * c + a) + (c ^ 3 + 3 * a ^ 3) * (5 * a + b) * (5 * b + c) - 2 / 3 * (a ^ 2 + b ^ 2 + c ^ 2) * ((5 * a + b) * (5 * b + c) * (5 * c + a)) ) / ((5 * a + b) * (5 * b + c) * (5 * c + a)) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
      sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (b * (a - c)), 
      sq_nonneg (c * (a - b)), sq_nonneg (c * (b - c)), sq_nonneg (c * (a - c)), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2)
    ]
    positivity
  linarith