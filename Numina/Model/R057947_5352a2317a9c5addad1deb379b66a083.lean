import Mathlib

theorem algebra_137025 (a d : ℝ) (h₀ : a = 1 / 3) (h₁ : a + 2 * d = 1 / 5) :
    a + d = 4 / 15 := by
  rw [h₀] at h₁
  have h2 : d = -1 / 15 := by
    linarith
  rw [h₀, h2]
  norm_num