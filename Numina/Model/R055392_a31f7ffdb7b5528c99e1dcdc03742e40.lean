import Mathlib

theorem algebra_124683 {a b x y : ℝ} (h₀ : a + b = 2) (h₁ : x + y = 2)
    (h₂ : a * x + b * y = 5) :
    (a ^ 2 + b ^ 2) * x * y + a * b * (x ^ 2 + y ^ 2) = -5 := by
  have hb : b = 2 - a := by linarith
  have hy : y = 2 - x := by linarith
  rw [hb, hy] at h₂
  rw [hb, hy]
  nlinarith [sq_nonneg (a - x), sq_nonneg (a - (2 - x)), sq_nonneg (x - a), sq_nonneg (x - (2 - x)), sq_nonneg (a -1), sq_nonneg (x -1)]