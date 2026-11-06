import Mathlib

theorem algebra_193663 (a d : ℝ) (h₀ : a > 0) (h₁ : d > 0)
    (h₂ : a + (a + d) + (a + 2 * d) + (a + 3 * d) = 84)
    (h₃ : a + 2 * d = 2.5 * (a + d)) :
    a + d = 12 := by
  norm_num at h₃
  linarith