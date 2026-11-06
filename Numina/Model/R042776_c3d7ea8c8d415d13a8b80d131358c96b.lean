import Mathlib

  theorem algebra_302945 {x y z : ℝ} (h₁ : x = 6 - y) (h₂ : z^2 = x * y - 9) : x = y := by
  rw [show x = 6 - y by linarith [h₁]] at h₂
  have h3 : (y - 3) ^ 2 + z ^ 2 = 0 := by
    nlinarith
  have hy : (y - 3) ^ 2 = 0 := by
    linarith [sq_nonneg (y - 3), sq_nonneg z]
  have hz : z ^ 2 = 0 := by
    linarith [sq_nonneg (y - 3), sq_nonneg z]
  have hy2 : y = 3 := by
    nlinarith
  have hx : x = 3 := by
    rw [show y = 3 by linarith [hy2] ] at h₁
    linarith
  linarith [hx, hy2]