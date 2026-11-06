import Mathlib

theorem algebra_309290 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a^2 - b^2 = b * c) (h2 : b^2 - c^2 = c * a) :
    a^2 - c^2 = a * b := by 
  nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]