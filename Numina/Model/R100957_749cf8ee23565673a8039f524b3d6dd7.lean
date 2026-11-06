import Mathlib

theorem inequalities_305072 (x y z k : ℝ) (h : x + y + z = k) :
    x ^ 2 + y ^ 2 + z ^ 2 ≥ k ^ 2 / 3 := by
  have h1 : k = x + y + z := by linarith
  rw [h1]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]