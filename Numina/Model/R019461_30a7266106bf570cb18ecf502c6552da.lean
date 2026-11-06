import Mathlib

theorem inequalities_599339 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + a := by linarith
  have h3 : 0 < a + b := by linarith

  have h4 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have pos1 : 0 < (b + c) * (c + a) * (a + b) := by positivity
    have h5 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
        ( (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - (3 / 2) * (b + c) * (c + a) * (a + b) ) / ( (b + c) * (c + a) * (a + b) ) ) := by 
      field_simp 
      ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [ mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c), mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith), mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith) ]
    positivity 
  linarith