import Mathlib

theorem algebra_21481 {x y : ℝ} (h₀ : x + y = 25) (h₁ : x - y = 11) :
    max x y = 18 := by
  have hx : x = 18 := by
    linarith
  have hy : y = 7 := by
    rw [hx] at h₀
    linarith
  rw [hx, hy]
  norm_num