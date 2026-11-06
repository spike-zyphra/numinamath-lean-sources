import Mathlib

theorem inequalities_603591 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 + b * c) / (b + c) + (b ^ 2 + c * a) / (c + a) +
    (c ^ 2 + a * b) / (a + b) ≥ a + b + c := by
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + a := by linarith
  have h3 : 0 < a + b := by linarith
  have h5 : (a ^ 2 + b * c) / (b + c) + (b ^ 2 + c * a) / (c + a) + (c ^ 2 + a * b) / (a + b) - (a + b + c) ≥ 0 := by
    have pos1 : 0 < (b + c) * (c + a) * (a + b) := by positivity
    have h4 : ((a ^ 2 + b * c) / (b + c) + (b ^ 2 + c * a) / (c + a) + (c ^ 2 + a * b) / (a + b) - (a + b + c)) =
      ((a ^ 2 + b * c) * (c + a) * (a + b) + (b ^ 2 + c * a) * (b + c) * (a + b) + (c ^ 2 + a * b) * (b + c) * (c + a) - (a + b + c) * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) := by
      field_simp [show b + c ≠ 0 by linarith, show c + a ≠ 0 by linarith, show a + b ≠ 0 by linarith]
      ring
    rw [h4]
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
    positivity
  linarith [h5]