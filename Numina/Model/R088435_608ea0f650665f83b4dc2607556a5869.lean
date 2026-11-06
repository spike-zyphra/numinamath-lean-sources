import Mathlib

theorem inequalities_598606 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    6 ≤ (1 + c) / (a + b) + (1 + a) / (b + c) + (1 + b) / (c + a) := by 
  have hb1 : 0 < b + c := by nlinarith
  have ha1 : 0 < a + c := by nlinarith
  have hc1 : 0 < a + b := by nlinarith
  have h1 : (1 + c) / (a + b) + (1 + a) / (b + c) + (1 + b) / (c + a) - 6 ≥ 0 := by
    have h3 : (a + b) * (b + c) * (c + a) > 0 := by positivity
    have eq1 : (1 + c) / (a + b) + (1 + a) / (b + c) + (1 + b) / (c + a) - 6 
        = ((1 + c) * (b + c) * (c + a) + (1 + a) * (a + b) * (c + a) + (1 + b) * (a + b) * (b + c) - 6 * ((a + b) * (b + c) * (c + a)) ) / ((a + b) * (b + c) * (c + a)) := by
      field_simp [(show 0 < a + b from by linarith), (show 0 < b + c from by linarith), (show 0 < c + a from by linarith)]
      ring
    rw [eq1]
    apply div_nonneg 
    nlinarith [sq_nonneg (a + b - b - c), sq_nonneg (b + c - c - a), sq_nonneg (c + a - a - b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    positivity 
  linarith 
  all_goals linarith