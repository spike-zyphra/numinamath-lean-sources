import Mathlib

theorem algebra_176987 (A B C : ℝ) (h₀ : Real.cos A + Real.cos B + Real.cos C = 0) (h₁ : Real.sin A + Real.sin B + Real.sin C = 0) :
    Real.cos A ^ 4 + Real.cos B ^ 4 + Real.cos C ^ 4 = 9 / 8 := by

  have h2 : Real.cos C = - (Real.cos A + Real.cos B) := by linarith [h₀]
  have h3 : Real.sin C = - (Real.sin A + Real.sin B) := by linarith [h₁]

  have h4 : Real.cos C ^ 2 + Real.sin C ^ 2 = 1 := Real.cos_sq_add_sin_sq C
  rw [h2, h3] at h4
  have h5 : (Real.cos A + Real.cos B) ^ 2 + (Real.sin A + Real.sin B) ^ 2 = 1 := by linarith [h4]

  have h6 : Real.cos A ^ 2 + Real.sin A ^ 2 = 1 := Real.cos_sq_add_sin_sq A
  have h7 : Real.cos B ^ 2 + Real.sin B ^ 2 = 1 := Real.cos_sq_add_sin_sq B

  have h8 : Real.cos A * Real.cos B + Real.sin A * Real.sin B = -1 / 2 := by
    nlinarith [h5, h6, h7]

  have eq1 : Real.cos C ^ 4 = (Real.cos A + Real.cos B) ^ 4 := by
    rw [h2]
    all_goals ring

  have eq2 : Real.cos A ^ 4 + Real.cos B ^ 4 + Real.cos C ^ 4 =
      Real.cos A ^ 4 + Real.cos B ^ 4 + (Real.cos A + Real.cos B) ^ 4 := by
    rw [eq1]

  rw [eq2]

  have eq3 : Real.cos A ^ 4 + Real.cos B ^ 4 + (Real.cos A + Real.cos B) ^ 4 =
      2 * (Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos A * Real.cos B) ^ 2 := by
    ring_nf

  rw [eq3]

  have eq4 : Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos A * Real.cos B = 3 / 4 := by
    nlinarith [sq_nonneg (Real.cos A - Real.cos B), sq_nonneg (Real.sin A - Real.sin B), sq_nonneg (Real.cos A + Real.cos B), sq_nonneg (Real.sin A + Real.sin B), Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, h8]

  rw [eq4]
  norm_num