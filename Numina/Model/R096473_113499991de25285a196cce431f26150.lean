import Mathlib

theorem inequalities_132530 (a b : ℝ) (h₀ : a > b) : a^3 > b^3 := by 
  have h1 : a - b > 0 := sub_pos.mpr h₀
  have h2 : a^2 + a*b + b^2 > 0 := by 
    nlinarith [sq_pos_of_pos (show 0 < a - b by linarith), sq_nonneg (a + b), sq_nonneg (a - b)]
  have h3 : a^3 - b^3 > 0 := by 
    nlinarith [h1, h2, sq_nonneg (a - b), sq_nonneg (a + b)]
  linarith