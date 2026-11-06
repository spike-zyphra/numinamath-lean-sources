import Mathlib

theorem algebra_284964 (A B : ℝ) (h₁ : Real.sin A + Real.sin B = 1) (h₂ : Real.cos A + Real.cos B = 0) :
    12 * Real.cos (2 * A) + 4 * Real.cos (2 * B) = 8 := by

  have h3 : Real.sin A ^ 2 + Real.cos A ^ 2 = 1 := Real.sin_sq_add_cos_sq A
  have h4 : Real.sin B ^ 2 + Real.cos B ^ 2 = 1 := Real.sin_sq_add_cos_sq B
  have h5 : Real.cos (2 * A) = 2 * Real.cos A ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  have h6 : Real.cos (2 * B) = 2 * Real.cos B ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  rw [h5, h6]
  have h7 : Real.cos B = -Real.cos A := by
    linarith
  have h8 : Real.cos B ^ 2 = Real.cos A ^ 2 := by
    rw [h7]
    ring
  have h9 : Real.sin B = 1 - Real.sin A := by
    linarith
  have h10 : Real.sin B ^ 2 + Real.cos A ^ 2 = 1 := by
    have h11 : Real.sin B ^ 2 + Real.cos B ^ 2 = 1 := Real.sin_sq_add_cos_sq B
    rw [h7] at h11
    linarith
  have h12 : Real.sin A = 1 / 2 := by
    rw [h9] at h10 -- Replace Real.sin B = 1 - Real.sin A
    have h13 : Real.sin A ^ 2 + Real.cos A ^ 2 = 1 := Real.sin_sq_add_cos_sq A
    nlinarith
  have h13 : Real.cos A ^ 2 = 3 / 4 := by
    have h14 : Real.sin A ^ 2 + Real.cos A ^ 2 = 1 := Real.sin_sq_add_cos_sq A
    rw [h12] at h14
    nlinarith
  have h14 : Real.cos B ^ 2 = 3 / 4 := by
    rw [h7]
    nlinarith
  nlinarith [h13, h14]