import Mathlib

theorem algebra_172756 (x y z : ℝ) (h₀ : x - y = 2) (h₁ : x * y + z ^ 2 + 1 = 0) :
    z = 0 := by
  have hx : x = y + 2 := by linarith
  rw [hx] at h₁
  have h2 : (y + 1) ^ 2 + z ^ 2 = 0 := by
    nlinarith
  have hz : z ^ 2 = 0 := by
    nlinarith [sq_nonneg (y + 1), sq_nonneg z]
  have h5 : z = 0 := by
    nlinarith [sq_nonneg z]
  exact h5