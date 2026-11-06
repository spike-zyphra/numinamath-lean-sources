import Mathlib

theorem inequalities_143592
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c < a + b ∧ b < a + c ∧ a < b + c) (hsum : a + b + c = 1) :
    5 * (a ^ 2 + b ^ 2 + c ^ 2) + 18 * a * b * c ≥ 7 / 3 := by 
  have h1 : c = 1 - a - b := by 
    linarith
  rw [h1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          mul_pos ha hb, mul_pos ha (show (0 : ℝ) < 1 - a - b by 
              nlinarith [h.1, h.2.1, h.2.2, hsum]
          ), 
          mul_pos hb (show (0 : ℝ) < 1 - a - b by 
              nlinarith [h.1, h.2.1, h.2.2, hsum]
          ), 
          h.1, h.2.1, h.2.2, 
          sq_nonneg (a + b - (1 - a - b)), 
          sq_nonneg (a - 1/3), sq_nonneg (b - 1/3), sq_nonneg ((1 - a - b) - 1/3)]