import Mathlib

theorem inequalities_603736
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    5 / 3 ≤ a / (b + c) + b / (c + a) + c / (a + b) +
    a * b * c / (2 * (a ^ 3 + b ^ 3 + c ^ 3)) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : 0 < a ^ 3 + b ^ 3 + c ^ 3 := by
    have ha3 : 0 < a ^ 3 := by positivity
    have hb3 : 0 < b ^ 3 := by positivity
    have hc3 : 0 < c ^ 3 := by positivity
    linarith
  have h4 : a / (b + c) + b / (c + a) + c / (a + b) + a * b * c / (2 * (a ^ 3 + b ^ 3 + c ^ 3)) - 5 / 3 ≥ 0 := by
    have pos1 : 0 < b + c := by linarith
    have pos2 : 0 < c + a := by linarith
    have pos3 : 0 < a + b := by linarith
    have h5 : a / (b + c) + b / (c + a) + c / (a + b) + a * b * c / (2 * (a ^ 3 + b ^ 3 + c ^ 3)) - 5 / 3 =
        ( (a * (c + a) * (a + b) * (a ^ 3 + b ^ 3 + c ^ 3) * 2 + b * (b + c) * (a + b) * (a ^ 3 + b ^ 3 + c ^ 3) * 2 + c * (b + c) * (c + a) * (a ^ 3 + b ^ 3 + c ^ 3) * 2 + a * b * c * (b + c) * (c + a) * (a + b) - 5 / 3 * 2 * (a ^ 3 + b ^ 3 + c ^ 3) * (b + c) * (c + a) * (a + b) ) ) / ( (b + c) * (c + a) * (a + b) * (2 * (a ^ 3 + b ^ 3 + c ^ 3) ) ) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
              sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
              sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
              sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
              sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
              sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2),
              sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a),
              mul_pos h1 (show 0 < 1 by norm_num)
          ]
    positivity
  linarith
  all_goals try { 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
  ]
}