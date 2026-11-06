import Mathlib

theorem inequalities_598128
    (a b c d : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d) :
    2 ≤ a / (b + c) + b / (c + d) + c / (d + a) + d / (a + b) := by
  have pos1 : 0 < b + c := by linarith
  have pos2 : 0 < c + d := by linarith
  have pos3 : 0 < d + a := by linarith
  have pos4 : 0 < a + b := by linarith
  have h : a / (b + c) + b / (c + d) + c / (d + a) + d / (a + b) - 2 ≥ 0 := by
    have pos1 : 0 < b + c := by linarith
    have pos2 : 0 < c + d := by linarith
    have pos3 : 0 < d + a := by linarith
    have pos4 : 0 < a + b := by linarith
    have h' : a / (b + c) + b / (c + d) + c / (d + a) + d / (a + b) - 2 = (a * (c + d) * (d + a) * (a + b) + b * (b + c) * (d + a) * (a + b) + c * (b + c) * (c + d) * (a + b) + d * (b + c) * (c + d) * (d + a) - 2 * (b + c) * (c + d) * (d + a) * (a + b)) / ((b + c) * (c + d) * (d + a) * (a + b)) := by 
      field_simp 
      ring
    rw [h']
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
            sq_nonneg (a + b - c - d), sq_nonneg (a + c - b - d), sq_nonneg (a + d - b - c), 
            mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
            mul_pos hb hc, mul_pos hb hd, 
            mul_pos hc hd]
    all_goals positivity
  linarith