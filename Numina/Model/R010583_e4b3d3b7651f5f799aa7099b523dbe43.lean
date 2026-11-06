import Mathlib

theorem algebra_21206 {x y : ℝ} (h₀ : x + y = 3) (h₁ : x - y = 4) :
    2 * x ^ 2 + 2 * y ^ 2 = 25 := by
  have h2 : 2 * x = 7 := by
    linarith
  have hx : x = 7 / 2 := by
    linarith
  have hy : y = -1 / 2 := by
    linarith [h₀, hx]
  rw [hx, hy]
  norm_num