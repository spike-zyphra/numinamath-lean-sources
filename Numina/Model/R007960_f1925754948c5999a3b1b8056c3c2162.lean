import Mathlib

theorem algebra_21566 (a d : ℚ) (h₀ : a = 2 / 3)
    (h₂ : a + 8 * d = 4 / 5) : a + 4 * d = 11 / 15 := by
  rw [h₀] at h₂
  have hd : d = 1 / 60 := by
    linarith
  rw [h₀, hd]
  norm_num