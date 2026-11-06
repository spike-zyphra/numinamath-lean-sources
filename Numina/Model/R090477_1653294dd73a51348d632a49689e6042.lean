import Mathlib

theorem algebra_141401
    (a b : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (h1 : a^3 = a + 1)
    (h2 : b^6 = b + 3 * a) :
    a > b := by
  nlinarith [sq_nonneg (a ^ 2 - 1), sq_nonneg (b ^ 3 - (a + 1)), 
          sq_nonneg (b ^ 3 + (a + 1) - 1), 
          sq_nonneg (b - a), sq_nonneg (b ^ 3 - a), 
          mul_pos ha hb, 
          h1, h2, 
          sq_nonneg (b ^ 3 - b - 1), 
          sq_nonneg (a - 1), 
          sq_nonneg (a ^ 2 - 1)]