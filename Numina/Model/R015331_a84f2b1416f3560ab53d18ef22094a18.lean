import Mathlib

open Real Set
open scoped Real

theorem inequalities_314424 (A B C : Real) (hA : A ∈ Ioo 0 (π / 2)) (hB : B ∈ Ioo 0 (π / 2))
    (hC : C ∈ Ioo 0 (π / 2)) (hABC : A + B + C = π) :
    cos A + cos B + cos C ≥ 2 * (cos A * cos B + cos B * cos C + cos A * cos C) := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with  ⟨hB1, hB2⟩
  rcases hC with  ⟨hC1, hC2⟩
  have h1 : cos A > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [hA1, hA2, Real.pi_pos]
  have h2 : cos B > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [hB1, hB2, Real.pi_pos]
  have h3 : cos C > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [hC1, hC2, Real.pi_pos]
  have h4 : sin A > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [hA1, hA2, Real.pi_pos]
  have h5 : sin B > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [hB1, hB2, Real.pi_pos]
  have h6 : sin C > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    all_goals linarith [hC1, hC2, Real.pi_pos]
  have h7 : C = π - (A + B) := by linarith
  have h8 : cos C = -cos (A + B) := by
    rw [h7]
    have h9 : cos (π - (A + B)) = -cos (A + B) := by
      rw [cos_pi_sub]
    linarith
  have h12 : cos (A + B) = cos A * cos B - sin A * sin B := by
    rw [cos_add]
  rw [h8, h12]
  nlinarith [sq_nonneg (cos A - cos B), sq_nonneg (cos A + cos B - 1), sq_nonneg (sin A - sin B), sq_nonneg (sin A ^ 2 - sin B ^ 2), 
    Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq (A + B), 
    mul_pos h1 h2, mul_pos h1 (show 0 < sin A by nlinarith), mul_pos h2 (show 0 < sin B by nlinarith), 
    mul_pos h4 h5, sq_nonneg (A + B - π / 2)]