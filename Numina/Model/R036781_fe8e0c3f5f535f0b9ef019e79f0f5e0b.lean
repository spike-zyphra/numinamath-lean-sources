import Mathlib

theorem algebra_2027 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 4 + b ^ 4 + c ^ 4 + 16 = 8 * a * b * c) : a * b * c = 8 := by 
  have h5 : (a - 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * b - 4), sq_nonneg (a * c - 4), sq_nonneg (b * c - 4),
      sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  have h6 : a - 2 = 0 := by
    apply pow_eq_zero 
    exact h5 
  have ha2 : a = 2 := by linarith 
  -- Now the same for b and c 
  have h7 : (b - 2) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * b - 4), sq_nonneg (a * c - 4), sq_nonneg (b * c - 4),
      sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  have h8 : b - 2 = 0 := by 
    apply pow_eq_zero 
    exact h7 
  have hb2 : b = 2 := by linarith 
  -- And c
  have h9 : (c - 2) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * b - 4), sq_nonneg (a * c - 4), sq_nonneg (b * c - 4),
      sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]
  have h10 : c - 2 = 0 := by 
    apply pow_eq_zero 
    exact h9 
  have hc2 : c = 2 := by linarith 
  -- Now we can prove a* b* c=8
  rw [ha2, hb2, hc2] 
  norm_num