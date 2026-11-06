import Mathlib

theorem inequalities_202989 (a b c d : ℝ) (h₀ : a + b + c + d = 0) :
    5 * (a * b + b * c + c * d) + 8 * (a * c + a * d + b * d) ≤ 0
  := by
  have h1 : d = -a - b - c := by
    linarith 
  rw [h1] 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - (-b - c)), 
          sq_nonneg (b - c), sq_nonneg (b - (-a - c)), sq_nonneg (c - (-a - b)), 
          sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (a + b + c), 
          sq_nonneg (a + b - (-c)), sq_nonneg (a - b + c), sq_nonneg (a + b - c)
          ]