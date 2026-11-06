import Mathlib

open Real

theorem inequalities_601756 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    (a + 1 / a) * (b + 1 / b) * (c + 1 / c) ≥ 1000 / 27 := by 
  have ha1 : 0 < a := by linarith
  have hb1 : 0 < b := by linarith
  have hc1 : 0 < c := by linarith
  have h50 : (a + 1 / a) * (b + 1 / b) * (c + 1 / c) - 1000 / 27 ≥ 0 := by 
    have h3 : 0 < a * b * c := by positivity 
    have hx2 : (a + 1 / a) * (b + 1 / b) * (c + 1 / c) - 1000 / 27 =
        ( (a ^ 2 + 1 ) * (b ^ 2 + 1 ) * (c ^ 2 + 1 ) - 1000 / 27 * (a * b * c ) ) / (a * b * c ) := by 
      field_simp 
      ring 
    rw [ hx2 ] 
    apply div_nonneg 
    have hx31 : a + b + c = 1 := h
    -- Solving a complex polynomial with constraints in `nlinarith` becomes computationally intensive.
    -- Now, we will try passing simple facts, which help `nlinarith` solve the goal.
    nlinarith [ 
          sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 3),
          sq_nonneg (a * b - 1 / 9), sq_nonneg (a * c - 1 / 9), sq_nonneg (b * c - 1 / 9), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
    all_goals positivity 
  linarith