import Mathlib

theorem inequalities_598824 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) +
    1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ 1 / (a * b * c) := by

  have h1 : 0 < a * b * c := by
    positivity
  have h6 : 1 / (a ^ 3 + b ^ 3 + a * b * c) ≤ c / (a * b * c * (a + b + c)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2)
        ]
  have h7 : 1 / (b ^ 3 + c ^ 3 + a * b * c) ≤ a / (a * b * c * (a + b + c)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (b - c), sq_nonneg (b - a), sq_nonneg (c - a), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a * b - b * c), 
          sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (a ^ 2 - b ^ 2)
        ]
  have h8 : 1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ b / (a * b * c * (a + b + c)) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (c - a), sq_nonneg (c - b), sq_nonneg (a - b), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (c * a - a * b), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), 
          sq_nonneg (c ^ 2 - a ^ 2), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2)
        ]
  have h9 : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) +
      1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ (c + a + b) / (a * b * c * (a + b + c)) := by
    have h14 : 1 / (a ^ 3 + b ^ 3 + a * b * c) + 1 / (b ^ 3 + c ^ 3 + a * b * c) +
        1 / (c ^ 3 + a ^ 3 + a * b * c) ≤ c / (a * b * c * (a + b + c)) + 
        a / (a * b * c * (a + b + c)) + b / (a * b * c * (a + b + c)) := by 
      apply add_le_add
      apply add_le_add
      all_goals
        try exact h6
        try exact h7
        try exact h8
    have h15 : c / (a * b * c * (a + b + c)) + a / (a * b * c * (a + b + c)) + b / (a * b * c * (a + b + c)) = (c + a + b) / (a * b * c * (a + b + c)) := by
      field_simp
      <;> ring
    linarith [h14, h15]
  have h10 : (c + a + b) / (a * b * c * (a + b + c)) ≤ 1 / (a * b * c) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  linarith [h9, h10]