import Mathlib

theorem inequalities_111908 (a b : ℝ) (h₀ : a + b > 2) : a ^ 4 + b ^ 4 > 2 := by
  nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), 
          sq_nonneg (a - b), sq_nonneg (a + b - 2),
          h₀, mul_pos (sub_pos.mpr h₀) (sub_pos.mpr h₀), 
          mul_self_nonneg (a^2 - b^2), 
          mul_self_nonneg (a - b), 
          sq_nonneg (a^2 + b^2 - 2), sq_nonneg (a * b - 1)]