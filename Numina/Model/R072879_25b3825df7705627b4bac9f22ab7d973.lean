import Mathlib

theorem algebra_169708 (d : ℝ) (h₀ : d > 0) (h₁ : (d / 4) / (d - (d / 4)) = 5 / 6) (h₂ : (d / 4) / (d + (d / 4)) = 1 / 6) :
    d = 12 := by
  have eq1 : d - (d / 4) ≠ 0 := by
    by_contra h
    have : d - (d / 4) = 0 := by linarith
    have : d = 0 := by
      nlinarith
    linarith
  have eq2 : d + (d / 4) ≠ 0 := by
    by_contra h
    have : d + (d / 4) = 0 := by linarith
    have : d = 0 := by
      nlinarith
    linarith
  field_simp [eq1] at h₁
  field_simp [eq2] at h₂
  nlinarith