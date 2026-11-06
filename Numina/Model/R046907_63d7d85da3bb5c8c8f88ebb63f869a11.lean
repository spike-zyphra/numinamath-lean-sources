import Mathlib

theorem algebra_228274 (d : ℝ) (h₀ : d > 0) (h₁ : 6 * 42 + 6 * (42 / (1 - 1 / 7)) = 3 * d / 5) :
    d = 910 := by
  have eq1 : (6 * 42 + 6 * (42 / (1 - 1 / 7 : ℝ))) = 546 := by
    norm_num
  rw [eq1] at h₁
  linarith