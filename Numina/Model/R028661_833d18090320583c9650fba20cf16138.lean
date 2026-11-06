import Mathlib

open Real Set
open scoped Real

theorem inequalities_1982 (A B C : Real)
    (hA : A ∈ Ioo 0 π)
    (hB : B ∈ Ioo 0 π)
    (hC : C ∈ Ioo 0 π)
    (hABC : A + B + C = π) :
    sin A + sin B - cos C ≤ 3 / 2 := by 
  rcases hA with ⟨hAl, hAr⟩
  rcases hB with ⟨hBl, hBr⟩
  rcases hC with ⟨hCl, hCr⟩
  have hC1 : C = π - A - B := by linarith 
  rw [hC1]
  have h1 : cos (π - A - B) = -cos (A + B) := by 
    have h2 : π - A - B = π - (A + B) := by ring
    rw [h2]
    rw [cos_pi_sub]
    <;> try { linarith }
  have h2 : sin A + sin B - (-cos (A + B)) ≤ 3 / 2 := by 
    have h3 : cos (A + B) = cos A * cos B - sin A * sin B := by 
      rw [cos_add]
    rw [h3]
    nlinarith [sq_nonneg (sin A - sin B), sq_nonneg (sin A + sin B - 1), sq_nonneg (cos A - cos B), sq_nonneg (cos A * cos B - sin A * sin B), sq_nonneg (A - B), sq_nonneg (sin A - 1 / 2), sq_nonneg (sin B - 1 / 2), sq_nonneg (cos A), sq_nonneg (cos B), Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq (A + B), Real.sin_sq_add_cos_sq (B - A), mul_pos (sin_pos_of_pos_of_lt_pi hAl hAr) (sin_pos_of_pos_of_lt_pi hBl hBr), Real.sin_sq_add_cos_sq (A - B)]
  nlinarith [h1, h2, Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq (A + B), Real.sin_sq_add_cos_sq (A + B), Real.sin_sq_add_cos_sq (π - A - B)]
  all_goals nlinarith [h1, h2, Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq (A + B), Real.sin_sq_add_cos_sq (π - A - B), sq_nonneg (A - B), sq_nonneg (A + B - π / 2), sq_nonneg (A - π / 2), sq_nonneg (B - π / 2)]