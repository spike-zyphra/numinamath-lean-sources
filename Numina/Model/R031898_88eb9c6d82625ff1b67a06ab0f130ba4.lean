import Mathlib

theorem inequalities_232596 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h1 : a < 1) (h2 : b < 1) :
    1 + a^2 + b^2 > 3 * a * b := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), 
          mul_pos ha hb, mul_pos ha (show 0 < 1 - a by linarith), 
          mul_pos hb (show 0 < 1 - b by linarith)]