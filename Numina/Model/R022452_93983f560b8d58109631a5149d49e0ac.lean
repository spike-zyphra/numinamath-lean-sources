import Mathlib

theorem inequalities_129349 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (b + c) / a + (c + a) / b + (a + b) / c ≥
    ((a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a)) / (a * b * c * (a + b + c)) + 3 := by
  have h1 : 0 < a * b * c * (a + b + c) := by
    positivity
  have h2 : (b + c) / a + (c + a) / b + (a + b) / c - ((a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a)) / (a * b * c * (a + b + c)) - 3 ≥ 0 := by
    have h3 : 0 < a * b * c * (a + b + c) := h1
    have h4 : ((b + c) / a + (c + a) / b + (a + b) / c - ((a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a)) / (a * b * c * (a + b + c)) - 3) = 
      ((b + c) * b * c * (a + b + c) + (c + a) * a * c * (a + b + c) + (a + b) * a * b * (a + b + c) - ((a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a)) - 3 * (a * b * c * (a + b + c))) / (a * b * c * (a + b + c)) := by 
        field_simp
        ring
    rw [h4]
    have h5 : ((b + c) * b * c * (a + b + c) + (c + a) * a * c * (a + b + c) + (a + b) * a * b * (a + b + c) - ((a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a)) - 3 * (a * b * c * (a + b + c))) ≥ 0 := by 
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc 
        ]
    apply div_nonneg 
    linarith 
    all_goals 
      linarith 
  linarith