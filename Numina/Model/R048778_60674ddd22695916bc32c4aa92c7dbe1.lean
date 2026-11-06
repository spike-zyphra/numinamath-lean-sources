import Mathlib

theorem algebra_14467 {x y : ℤ} (h₀ : x + y = 19) (h₁ : x - y = 5) : x * y = 84 := by
  have h2 : 2 * x = 24 := by
    linarith
  have hx : x = 12 := by
    linarith
  have hy : y = 7 := by
    linarith [h₀, hx]
  rw [hx, hy]
  norm_num