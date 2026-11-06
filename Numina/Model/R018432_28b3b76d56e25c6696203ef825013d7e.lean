import Mathlib

theorem algebra_146787 (x y : ℝ) (h₁ : Real.sin x = 2 * Real.cos y - (5 / 2) * Real.sin y)
    (h₂ : Real.cos x = 2 * Real.sin y - (5 / 2) * Real.cos y) :
    Real.sin (2 * y) = (37 / 40) := by
  have h3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  rw [h₁, h₂] at h3
  have h4 : Real.sin (2 * y) = 2 * Real.sin y * Real.cos y := by
    rw [Real.sin_two_mul]
    all_goals ring_nf <;> tauto
  have h5 : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
  have h6 : Real.sin y * Real.cos y = (37 / 80) := by
    nlinarith [sq_nonneg (Real.sin y - Real.cos y), sq_nonneg (Real.sin y + Real.cos y), Real.sin_sq_add_cos_sq y]
  rw [h4]
  nlinarith [h6, Real.sin_sq_add_cos_sq y]