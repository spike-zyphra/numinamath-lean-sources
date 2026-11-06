import Mathlib

theorem inequalities_602183 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / a / (1 + b) + 1 / b / (1 + c) + 1 / c / (1 + a) ≥ 1 / (1 + a * b * c) := by
  have ha' : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc

  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < b * c := mul_pos hb hc
  have h3 : 0 < a * c := mul_pos ha hc

  have h4 : 0 < 1 + a := by nlinarith
  have h5 : 0 < 1 + b := by nlinarith
  have h6 : 0 < 1 + c := by nlinarith
  have h7 : 0 < 1 + a * b * c := by nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h8 : a * (1 + b) > 0 := by positivity
  have h9 : b * (1 + c) > 0 := by positivity
  have h10 : c * (1 + a) > 0 := by positivity
  have h11 : 1 + a * b * c > 0 := by positivity
  
  suffices 1 / a / (1 + b) + 1 / b / (1 + c) + 1 / c / (1 + a) - 1 / (1 + a * b * c) ≥ 0 by linarith
  
  have h13 : 1 / a / (1 + b) + 1 / b / (1 + c) + 1 / c / (1 + a) - 1 / (1 + a * b * c) =
      (b * c * (1 + a) * (1 + c) * (1 + a * b * c) + a * c * (1 + a) * (1 + b) * (1 + a * b * c) + a * b * (1 + b) * (1 + c) * (1 + a * b * c) - a * b * c * (1 + a) * (1 + b) * (1 + c)) 
      / (a * b * c * (1 + a) * (1 + b) * (1 + c) * (1 + a * b * c)) := by 
    field_simp [h8, h9, h10, h11]
    ring
  
  rw [h13]
  apply div_nonneg
  
  nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (b - c)), sq_nonneg (b * (a - c)), sq_nonneg (c * (a - b)), 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith),
          mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith),
          mul_pos (show 0 < c * a by nlinarith) (show 0 < a * b by nlinarith)
          ]
  
  positivity