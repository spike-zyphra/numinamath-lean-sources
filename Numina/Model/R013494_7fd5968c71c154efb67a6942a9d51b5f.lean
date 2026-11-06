import Mathlib

theorem inequalities_8983
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    (1 + a ^ 3 + b ^ 3 + c ^ 3) * (1 + a + b + c) ≥
    2 * (a + b) * (b + c) * (c + a) := by 
  have h11 : (1 + a ^ 3 + b ^ 3 + c ^ 3) * (1 + a + b + c) - 2 * (a + b) * (b + c) * (c + a) ≥ 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2),
      sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < c * a by nlinarith), 
      mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith)
    ]
  linarith