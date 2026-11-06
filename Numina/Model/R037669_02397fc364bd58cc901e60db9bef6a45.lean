import Mathlib

theorem algebra_597216 (A B C : ℝ) (h₁ : Real.cos A + Real.cos B + Real.cos C = 0) (h₂ : Real.sin A + Real.sin B + Real.sin C = 0) :
    Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2 = 3 / 2 := by
  have h3 : Real.cos C = - (Real.cos A + Real.cos B) := by linarith 
  have h4 : Real.sin C = - (Real.sin A + Real.sin B) := by linarith 
  have h5 : (Real.cos A + Real.cos B) ^ 2 + (Real.sin A + Real.sin B) ^ 2 = 1 := by 
    have h5 : Real.cos C ^ 2 + Real.sin C ^ 2 = 1 := Real.cos_sq_add_sin_sq C 
    rw [h3, h4] at h5 
    linarith 
  rw [h3]
  nlinarith [Real.cos_sq_add_sin_sq A, Real.cos_sq_add_sin_sq B, h5, mul_self_nonneg (Real.sin A - Real.sin B), mul_self_nonneg (Real.cos A - Real.cos B)]