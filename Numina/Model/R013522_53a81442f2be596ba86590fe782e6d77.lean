import Mathlib

open Real Set
open scoped Real

theorem algebra_196575 (A B C : Real) (hA : A ∈ Ioo 0 π)
  (hB : B ∈ Ioo 0 π) (hC : C ∈ Ioo 0 π) (hABC : A + B + C = π) :
  sin A ^ 2 + sin B ^ 2 + sin C ^ 2 - 2 * cos A * cos B * cos C = 2 := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  have hC_eq : C = π - (A + B) := by linarith [hABC]
  have h1 : sin C = sin (A + B) := by
    rw [hC_eq]
    rw [sin_pi_sub]
  have h2 : cos C = -cos (A + B) := by 
    rw [hC_eq]
    rw [cos_pi_sub]
    <;> ring
  have h3 : sin (A + B) = sin A * cos B + cos A * sin B := by 
    rw [sin_add]
  have h4 : cos (A + B) = cos A * cos B - sin A * sin B := by
    rw [cos_add]
  rw [h1, h3, h2, h4]
  have h5 : sin A ^ 2 + cos A ^ 2 = 1 := Real.sin_sq_add_cos_sq A
  have h6 : sin B ^ 2 + cos B ^ 2 = 1 := Real.sin_sq_add_cos_sq B
  nlinarith [sq_nonneg (sin A - sin B), sq_nonneg (cos A - cos B), 
            sq_nonneg (sin A - cos A), sq_nonneg (sin B - cos B), 
            sq_nonneg (sin A * sin B), sq_nonneg (cos A * cos B), 
            Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, 
            sq_nonneg (sin A * cos B - cos A * sin B), 
            sq_nonneg (cos A * cos B - sin A * sin B), 
            mul_pos (show 0 < sin A by apply sin_pos_of_pos_of_lt_pi hA1 (by linarith)) 
                        (show 0 < sin B by apply sin_pos_of_pos_of_lt_pi hB1 (by linarith)), 
            h5, h6]