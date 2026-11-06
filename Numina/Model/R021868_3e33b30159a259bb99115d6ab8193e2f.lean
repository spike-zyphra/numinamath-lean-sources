import Mathlib

theorem inequalities_185 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / a + (c + a) / b + (a + b) / c ≥ a / (b + c) + b / (a + c) + c / (a + b) + 9 / 2 := by
  have h4 : (b + c) / a + (c + a) / b + (a + b) / c - (a / (b + c) + b / (a + c) + c / (a + b) + 9 / 2) ≥ 0 := by
    have pos1 : 0 < a := ha
    have pos2 : 0 < b := hb
    have pos3 : 0 < c := hc
    have pos4 : 0 < b + c := by linarith
    have pos5 : 0 < a + c := by linarith
    have pos6 : 0 < a + b := by linarith 
    have pos7 : 0 < a * b * c * (b + c) * (a + c) * (a + b) := by positivity
    have h5 : (b + c) / a + (c + a) / b + (a + b) / c - (a / (b + c) + b / (a + c) + c / (a + b) + 9 / 2) =
        ((b + c) * (b * c * (b + c) * (a + c) * (a + b)) + (c + a) * (a * c * (b + c) * (a + c) * (a + b)) + (a + b) * (a * b * (b + c) * (a + c) * (a + b)) - a * (a * b * c * (a + c) * (a + b)) - b * (a * b * c * (b + c) * (a + b)) - c * (a * b * c * (b + c) * (a + c)) - (9 / 2) * (a * b * c * (b + c) * (a + c) * (a + b)) ) / (a * b * c * (b + c) * (a + c) * (a + b)) := by
      field_simp
      ring 
    rw [h5] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (show 0 < b + c by linarith) (show 0 < a + c by linarith), 
      mul_pos (show 0 < a + c by linarith) (show 0 < a + b by linarith), 
      mul_pos (show 0 < a + b by linarith) (show 0 < b + c by linarith)
    ]
    positivity
  linarith