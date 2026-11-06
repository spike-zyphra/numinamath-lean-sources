import Mathlib

theorem inequalities_607712 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 + (a + b + c)^2 ≤ 4) :
    3 ≤ (a * b + 1) / (a + b)^2 + (b * c + 1) / (b + c)^2 + (c * a + 1) / (c + a)^2 := by 
  have h1 : 0 < a + b := by linarith
  have h2 : 0 < b + c := by linarith
  have h3 : 0 < c + a := by linarith
  have h4 : a^2 + b^2 + c^2 + a * b + b * c + c * a ≤ 2 := by 
    nlinarith
  have h5 : (a * b + 1) / (a + b)^2 + (b * c + 1) / (b + c)^2 + (c * a + 1) / (c + a)^2 - 3 ≥ 0 := by
    have h_pos1 : 0 < (a + b)^2 := by positivity
    have h_pos2 : 0 < (b + c)^2 := by positivity
    have h_pos3 : 0 < (c + a)^2 := by positivity
    have eq6 : (a * b + 1) / (a + b)^2 + (b * c + 1) / (b + c)^2 + (c * a + 1) / (c + a)^2 - 3 =
        ((a * b + 1) * (b + c)^2 * (c + a)^2 + (b * c + 1) * (a + b)^2 * (c + a)^2 + (c * a + 1) * (a + b)^2 * (b + c)^2 - 3 * (a + b)^2 * (b + c)^2 * (c + a)^2) / ((a + b)^2 * (b + c)^2 * (c + a)^2) := by 
      field_simp
      ring
    rw [eq6] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
               sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
               mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
               mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
               mul_pos (show 0 < a * b by nlinarith) (show 0 < c * a by nlinarith), 
               mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith)]
    all_goals positivity
  linarith