import Mathlib

theorem calculus_14664 (x y z : ℝ) (h₀ : Real.cos x + Real.cos y + Real.cos z = 0)
    (h₁ : Real.sin x + Real.sin y + Real.sin z = 0) :
    Real.cos (2 * x) + Real.cos (2 * y) + Real.cos (2 * z) = 0 := by
  have h2 : Real.cos z = - (Real.cos x + Real.cos y) := by
    linarith
  have h3 : Real.sin z = - (Real.sin x + Real.sin y) := by
    linarith
  have h4 : Real.cos z ^ 2 + Real.sin z ^ 2 = 1 := Real.cos_sq_add_sin_sq z
  rw [h2, h3] at h4

  have h5 : Real.cos (2 * x) = 2 * (Real.cos x) ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  have h6 : Real.cos (2 * y) = 2 * (Real.cos y) ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  have h7 : Real.cos (2 * z) = 2 * (Real.cos z) ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  rw [h5, h6, h7, h2]
  nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq z, sq_nonneg (Real.sin x + Real.sin y), sq_nonneg (Real.cos x + Real.cos y), sq_nonneg (Real.sin x - Real.sin y), sq_nonneg (Real.cos x - Real.cos y)]