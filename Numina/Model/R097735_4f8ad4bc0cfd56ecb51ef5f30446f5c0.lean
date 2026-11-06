import Mathlib

open Real Set
open scoped Real

theorem inequalities_45020 (A : Real) (hA : A ∈ Ioo 0 (π / 2)) :
    (1 + 1 / sin A) * (1 + 1 / cos A) > 5 := by
  rcases hA with ⟨h1, h2⟩
  have h3 : sin A > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [h1, h2, Real.pi_pos]
    linarith [h1, h2, Real.pi_pos]
  have h4 : cos A > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [h1, h2, Real.pi_pos]
    · linarith [h1, h2, Real.pi_pos]
  have h5 : sin A * cos A > 0 := mul_pos h3 h4
  have h6 : (1 + 1 / sin A) * (1 + 1 / cos A) - 5 > 0 := by
    have h7 : (1 + 1 / sin A) * (1 + 1 / cos A) - 5 = ((sin A + 1) * (cos A + 1) - 5 * (sin A * cos A)) / (sin A * cos A) := by
      field_simp
      <;> ring
    rw [h7]
    have h10 : (sin A + 1) * (cos A + 1) - 5 * (sin A * cos A) > 0 := by
      nlinarith [sq_nonneg (sin A - cos A), sq_nonneg (sin A - 1), sq_nonneg (cos A - 1),
                Real.sin_sq_add_cos_sq A, mul_pos h3 h4]
    have h8 : sin A * cos A > 0 := h5
    apply div_pos
    · linarith [h10]
    · positivity
  linarith