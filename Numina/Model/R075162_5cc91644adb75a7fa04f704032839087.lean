import Mathlib

theorem inequalities_267209 (a b c d : ℝ) (h₀ : a + d = b + c) :
    (a - b) * (c - d) + (a - c) * (b - d) + (d - a) * (b - c) ≥ 0 := by 
  have h1 : d = b + c - a := by linarith
  rw [h1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - (b + c - a)), sq_nonneg (c - a)]