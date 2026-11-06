import Mathlib

theorem inequalities_320278 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 2 / (c * (b + c)) + b ^ 2 / (a * (c + a)) + c ^ 2 / (b * (a + b)) ≥ 3 / 2 := by
  have h1 : 0 < c * (b + c) := by
    positivity
  have h2 : 0 < a * (c + a) := by
    positivity
  have h3 : 0 < b * (a + b) := by
    positivity
  have h4 : a ^ 2 / (c * (b + c)) + b ^ 2 / (a * (c + a)) + c ^ 2 / (b * (a + b)) - 3 / 2 ≥ 0 := by
    have h4' : a ^ 2 / (c * (b + c)) + b ^ 2 / (a * (c + a)) + c ^ 2 / (b * (a + b)) - 3 / 2 = ( 
        a ^ 2 * a * (c + a) * b * (a + b) + b ^ 2 * c * (b + c) * b * (a + b) + c ^ 2 * c * (b + c) * a * (c + a) - 3 / 2 * c * (b + c) * a * (c + a) * b * (a + b)
     ) / ( c * (b + c) * a * (c + a) * b * (a + b) ) := by
      field_simp
      ring
    rw [h4']
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (a * b - c * a), sq_nonneg (b * c - c * a), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
    all_goals positivity
  linarith