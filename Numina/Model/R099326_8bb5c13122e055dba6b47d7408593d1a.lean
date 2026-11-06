import Mathlib

theorem algebra_194046 (s : ℝ) (h₀ : s ≠ 0) (h₁ : (7 / s) = (-2) * (s / 2)) :
    s = -2 := by
  field_simp [h₀] at h₁
  nlinarith [sq_nonneg s]