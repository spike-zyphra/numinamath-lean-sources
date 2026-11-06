import Mathlib

theorem algebra_175239 (d a b : ℝ) (h₀ : d > 0) (h₁ : a > 0) (h₂ : b > 0)
    (h₃ : a = 3 * b) (h₄ : a * 150 = b * (d - 150)) (h₅ : a * (d - 150) = b * (d / 2)) :
    d = 1550 := by
  rw [h₃] at h₄ h₅
  nlinarith