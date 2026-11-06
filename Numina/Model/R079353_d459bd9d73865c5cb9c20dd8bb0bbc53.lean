import Mathlib

theorem inequalities_320262 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) ≥ 2 - 4 * (a / (b + c) * b / (c + a) * c / (a + b)) := by
  have hb' : 0 < b := hb
  have hc' : 0 < c := hc
  have ha' : 0 < a := ha
  have pos1 : b + c > 0 := by positivity
  have pos2 : c + a > 0 := by positivity
  have pos3 : a + b > 0 := by positivity
  have h1 : a / (b + c) + b / (c + a) + c / (a + b) - (2 - 4 * (a / (b + c) * b / (c + a) * c / (a + b))) ≥ 0 := by
    have eq : a / (b + c) + b / (c + a) + c / (a + b) - (2 - 4 * (a / (b + c) * b / (c + a) * c / (a + b))) =
          (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 
           (2 * (b + c) * (c + a) * (a + b) - 4 * (a * b * c))) / ((b + c) * (c + a) * (a + b)) := by 
      field_simp [pos1, pos2, pos3]
      ring
    rw [eq]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
         ]
    positivity
  linarith