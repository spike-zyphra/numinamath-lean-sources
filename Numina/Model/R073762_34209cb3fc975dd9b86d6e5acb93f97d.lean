import Mathlib

theorem algebra_147092 (x y : ℝ) (h₁ : Real.sin x = (3 / 2) * Real.sin y - (2 / 3) * Real.cos y)
    (h₂ : Real.cos x = (3 / 2) * Real.cos y - (2 / 3) * Real.sin y) :
    Real.sin (2 * y) = 61 / 72 := by 
  have h3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by 
    exact Real.sin_sq_add_cos_sq x
  rw [h₁, h₂] at h3
  have h4 : Real.sin (2 * y) = 2 * Real.sin y * Real.cos y := by
    rw [Real.sin_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq y, h4]