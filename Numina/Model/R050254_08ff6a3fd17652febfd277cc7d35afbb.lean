import Mathlib

theorem inequalities_161473 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
  have hab1 : 0 < b + c := by linarith
  have hab2 : 0 < c + a := by linarith
  have hab3 : 0 < a + b := by linarith
  have h1 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h2 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
        (2*a*(c + a)*(a + b) + 2*b*(b + c)*(a + b) + 2*c*(b + c)*(c + a) - 3*(b + c)*(c + a)*(a + b)) / (2*(b + c)*(c + a)*(a + b)) := by
        field_simp [show 0 < b + c by positivity, show 0 < c + a by positivity, show 0 < a + b by positivity]
        ring
    rw [h2]
    apply div_nonneg
    -- Show the numerator is non-negative
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
      sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    positivity
  linarith