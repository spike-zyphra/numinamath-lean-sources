import Mathlib

theorem algebra_316803 (x y : ℝ) (h : 5 * x ^ 2 - 6 * x * y + 2 * y ^ 2 - 4 * x + 2 * y + 1 = 0) :
    x = 1 ∧ y = 1 := by
  have h1 : (y - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (5 * x - 3 * y - 2), sq_nonneg (y - 1)]
  have hy : y = 1 := by 
    nlinarith
  have hx : x = 1 := by
    rw [show y = 1 by linarith [hy]] at h
    nlinarith
  exact ⟨hx, hy⟩