import Mathlib

theorem algebra_11490 {x y : ℝ} (h₀ : x + y = 50) (h₁ : x - y = 6) : x * y = 616 := by
  have hx : x = 28 := by
    linarith [h₀, h₁]
  have hy : y = 22 := by
    rw [hx] at h₀
    linarith
  rw [hx, hy]
  norm_num