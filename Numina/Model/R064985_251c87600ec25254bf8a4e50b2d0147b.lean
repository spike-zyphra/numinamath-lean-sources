import Mathlib

theorem algebra_188501 (d h : ℝ) (h₀ : d > 0) (h₁ : h > 0)
    (h₂ : d - h = 150) (h₃ : d / 17 = h / 14 + 520 / 17) :
    False := by 
  have eq1 : d = h + 150 := by linarith
  rw [eq1] at h₃
  linarith