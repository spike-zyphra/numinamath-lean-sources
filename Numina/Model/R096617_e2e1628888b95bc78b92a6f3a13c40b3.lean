import Mathlib

theorem algebra_256503 {A B C : ℝ} (h₀ : Real.sin A + Real.sin B + Real.sin C = 0) (h₁ : Real.cos A + Real.cos B + Real.cos C = 0) :
    Real.cos (A - B) + Real.cos (B - C) + Real.cos (C - A) = -3 / 2 := by

  have h2 : Real.cos (A - B) = Real.cos A * Real.cos B + Real.sin A * Real.sin B := by
    rw [Real.cos_sub]
  have h3 : Real.cos (B - C) = Real.cos B * Real.cos C + Real.sin B * Real.sin C := by
    rw [Real.cos_sub]
  have h4 : Real.cos (C - A) = Real.cos C * Real.cos A + Real.sin C * Real.sin A := by
    rw [Real.cos_sub]

  have h5 : Real.cos (A - B) + Real.cos (B - C) + Real.cos (C - A) =
      (Real.cos A * Real.cos B + Real.sin A * Real.sin B) +
      (Real.cos B * Real.cos C + Real.sin B * Real.sin C) +
      (Real.cos C * Real.cos A + Real.sin C * Real.sin A) := by 
    rw [h2, h3, h4]
    <;> ring

  have h6 : (Real.sin A + Real.sin B + Real.sin C) ^ 2 + (Real.cos A + Real.cos B + Real.cos C) ^ 2 = 0 := by
    rw [h₀, h₁]
    norm_num

  have h7 : (Real.sin A + Real.sin B + Real.sin C) ^ 2 + (Real.cos A + Real.cos B + Real.cos C) ^ 2 =
      (Real.sin A ^ 2 + Real.sin B ^ 2 + Real.sin C ^ 2 + 2 * (Real.sin A * Real.sin B + Real.sin A * Real.sin C + Real.sin B * Real.sin C)) +
      (Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2 + 2 * (Real.cos A * Real.cos B + Real.cos A * Real.cos C + Real.cos B * Real.cos C)) := by
    ring

  have h8 : (Real.sin A ^ 2 + Real.cos A ^ 2) = 1 := Real.sin_sq_add_cos_sq A
  have h9 : (Real.sin B ^ 2 + Real.cos B ^ 2) = 1 := Real.sin_sq_add_cos_sq B
  have h10 : (Real.sin C ^ 2 + Real.cos C ^ 2) = 1 := Real.sin_sq_add_cos_sq C
  
  have h11 : Real.sin A ^ 2 + Real.sin B ^ 2 + Real.sin C ^ 2 + Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2 + 2 * (Real.sin A * Real.sin B + Real.sin A * Real.sin C + Real.sin B * Real.sin C + Real.cos A * Real.cos B + Real.cos A * Real.cos C + Real.cos B * Real.cos C) = 0 := by
    nlinarith [h7, h8, h9, h10, h6, Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq C]

  rw [h5]
  nlinarith [h11, Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq C]