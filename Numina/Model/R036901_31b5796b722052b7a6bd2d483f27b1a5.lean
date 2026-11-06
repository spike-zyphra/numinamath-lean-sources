import Mathlib

open Real

theorem inequalities_596932 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 1) :
    4 * sqrt 3 ≤ a + b + c + 1 / (a * b * c) := by 
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h3 : sqrt 3 > 0 := by
    positivity
  have h4 : a + b + c + 1 / (a * b * c) - 4 * sqrt 3 ≥ 0 := by
    have h5 : sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by linarith)
    have h6 : sqrt 3 ^ 4 = 9 := by
      calc
        sqrt 3 ^ 4 = (sqrt 3 ^ 2) ^ 2 := by ring
        _ = 3 ^ 2 := by rw [h5]
        _ = 9 := by norm_num
    have h8 : a + b + c + 1 / (a * b * c) - 4 * sqrt 3 =
        ((a + b + c) * (a * b * c) + 1 - 4 * sqrt 3 * (a * b * c)) / (a * b * c) := by
      field_simp
      <;> nlinarith
    rw [h8]
    have h9 : ((a + b + c) * (a * b * c) + 1 - 4 * sqrt 3 * (a * b * c)) ≥ 0 := by
      nlinarith [sq_nonneg (a + b + c - sqrt 3), sq_nonneg (a * b * c - (1 / sqrt 3) ^ 3), 
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg ( (a * b + b * c + c * a) - (1 / 3) ), 
          h, 
          Real.sqrt_pos.2 (show (3 : ℝ) > 0 by norm_num), 
          sq_nonneg ( (a * b * c) - 1 / (3 ^ (3 / 2 : ℝ) ) ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by nlinarith), 
          sq_nonneg (a^2 + b^2 + c^2 -1), 
          h5, h6
        ]
    have h10 : (a * b * c) > 0 := h1
    apply div_nonneg
    linarith
    all_goals linarith
  linarith